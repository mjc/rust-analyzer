//! Parser recognizes special macro syntax, `$var` and `$(repeat)*`, in token
//! trees.

use std::sync::Arc;

use arrayvec::ArrayVec;
use intern::{Symbol, sym};
use span::{Edition, Span, SyntaxContext};
use tt::{
    MAX_GLUED_PUNCT_LEN,
    iter::{TtElement, TtIter},
};

use crate::{MacroCallStyle, ParseError};

pub(crate) fn parse_rule_style(src: &mut TtIter<'_>) -> Result<MacroCallStyle, ParseError> {
    // Skip an optional `unsafe`. This is only actually allowed for `attr`
    // rules, but we'll let rustc worry about that.
    if let Some(TtElement::Leaf(tt::Leaf::Ident(ident))) = src.peek()
        && ident.sym == sym::unsafe_
    {
        src.next().expect("already peeked");
    }

    let kind = match src.peek() {
        Some(TtElement::Leaf(tt::Leaf::Ident(ident))) if ident.sym == sym::attr => {
            src.next().expect("already peeked");
            // FIXME: Add support for `attr(..)` rules with attribute arguments,
            // which would be inside these parens.
            src.expect_subtree().map_err(|_| ParseError::expected("expected `()`"))?;
            MacroCallStyle::Attr
        }
        Some(TtElement::Leaf(tt::Leaf::Ident(ident))) if ident.sym == sym::derive => {
            src.next().expect("already peeked");
            src.expect_subtree().map_err(|_| ParseError::expected("expected `()`"))?;
            MacroCallStyle::Derive
        }
        _ => MacroCallStyle::FnLike,
    };
    Ok(kind)
}

/// Consider
///
/// ```
/// macro_rules! a_macro {
///     ($x:expr, $y:expr) => ($y * $x)
/// }
/// ```
///
/// Stuff to the left of `=>` is a [`MetaTemplate`] pattern (which is matched
/// with input).
///
/// Stuff to the right is a [`MetaTemplate`] template which is used to produce
/// output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MetaTemplate(pub(crate) Box<[Op]>);

impl MetaTemplate {
    pub(crate) fn parse_pattern(
        edition: impl Copy + Fn(SyntaxContext) -> Edition,
        pattern: TtIter<'_>,
    ) -> Result<Self, ParseError> {
        MetaTemplate::parse(edition, pattern, Mode::Pattern)
    }

    pub(crate) fn parse_template(
        edition: impl Copy + Fn(SyntaxContext) -> Edition,
        template: TtIter<'_>,
    ) -> Result<Self, ParseError> {
        MetaTemplate::parse(edition, template, Mode::Template)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &Op> {
        self.0.iter()
    }

    fn parse(
        edition: impl Copy + Fn(SyntaxContext) -> Edition,
        mut src: TtIter<'_>,
        mode: Mode,
    ) -> Result<Self, ParseError> {
        let mut res = Vec::new();
        while let Some(first) = src.peek() {
            let op = next_op(edition, first, &mut src, mode)?;
            res.push(op);
        }

        Ok(MetaTemplate(res.into_boxed_slice()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Var { name: Symbol, kind: Option<MetaVarKind>, id: Span },
    Ignore { name: Symbol, id: Span },
    Index { depth: usize },
    Len { depth: usize },
    Count { name: Symbol, depth: usize },
    Concat { payload: Box<ConcatOp> },
    Repeat { tokens: MetaTemplate, kind: RepeatKind, separator: Option<Arc<Separator>> },
    Subtree { tokens: MetaTemplate, delimiter: Box<tt::Delimiter> },
    Literal { text_and_suffix: Symbol, span: Span, kind: tt::LitKind, suffix_len: u8 },
    PunctInline { span: Span, encoded: u32 },
    PunctBoxed(Box<[tt::Punct]>),
    Ident { sym: Symbol, span: Span, is_raw: tt::IdentIsRaw },
}

impl Op {
    pub(crate) fn from_puncts(puncts: &[tt::Punct]) -> Self {
        assert!(!puncts.is_empty() && puncts.len() <= MAX_GLUED_PUNCT_LEN);
        let first = puncts[0];
        let can_inline = puncts.len() == 1
            || puncts.iter().enumerate().all(|(index, punct)| {
                punct.char.is_ascii()
                    && punct.span.anchor == first.span.anchor
                    && punct.span.ctx == first.span.ctx
                    && punct.span.range
                        == tt::TextRange::at(
                            first.span.range.start() + tt::TextSize::new(index as u32),
                            tt::TextSize::new(1),
                        )
            });
        if !can_inline {
            return Self::PunctBoxed(puncts.into());
        }

        // Bits 0..=1 store len - 1, bits 2..=7 store the three spacing values, and the
        // remaining bits store either one Unicode scalar or up to three ASCII characters.
        let mut encoded = (puncts.len() - 1) as u32;
        for (index, punct) in puncts.iter().enumerate() {
            let spacing = match punct.spacing {
                tt::Spacing::Alone => 0,
                tt::Spacing::Joint => 1,
                tt::Spacing::JointHidden => 2,
            };
            encoded |= spacing << (2 + index * 2);
            if puncts.len() == 1 {
                encoded |= (punct.char as u32) << 8;
            } else {
                encoded |= (punct.char as u32) << (8 + index * 8);
            }
        }
        Self::PunctInline { span: first.span, encoded }
    }

    pub(crate) fn puncts(&self) -> Puncts<'_> {
        match self {
            Self::PunctInline { span, encoded } => {
                Puncts::Inline { span: *span, encoded: *encoded, index: 0 }
            }
            Self::PunctBoxed(puncts) => Puncts::Boxed(puncts.iter()),
            _ => unreachable!("puncts called on a non-punctuation operation"),
        }
    }

    fn from_literal(literal: tt::Literal) -> Self {
        let tt::Literal { text_and_suffix, span, kind, suffix_len } = literal;
        Self::Literal { text_and_suffix, span, kind, suffix_len }
    }

    fn from_ident(ident: tt::Ident) -> Self {
        let tt::Ident { sym, span, is_raw } = ident;
        Self::Ident { sym, span, is_raw }
    }
}

#[derive(Clone)]
pub(crate) enum Puncts<'a> {
    Inline { span: Span, encoded: u32, index: u8 },
    Boxed(std::slice::Iter<'a, tt::Punct>),
}

impl Iterator for Puncts<'_> {
    type Item = tt::Punct;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inline { span, encoded, index } => {
                let len = (*encoded & 0b11) as u8 + 1;
                if *index == len {
                    return None;
                }

                let char = if len == 1 {
                    char::from_u32(*encoded >> 8)
                } else {
                    char::from_u32((*encoded >> (8 + u32::from(*index) * 8)) & 0xff)
                }
                .expect("packed punctuation contains a valid character");
                let spacing = match (*encoded >> (2 + u32::from(*index) * 2)) & 0b11 {
                    0 => tt::Spacing::Alone,
                    1 => tt::Spacing::Joint,
                    2 => tt::Spacing::JointHidden,
                    _ => unreachable!("packed punctuation contains a valid spacing"),
                };
                let mut punct_span = *span;
                if *index != 0 {
                    punct_span.range = tt::TextRange::at(
                        span.range.start() + tt::TextSize::new(u32::from(*index)),
                        tt::TextSize::new(1),
                    );
                }
                *index += 1;
                Some(tt::Punct { char, spacing, span: punct_span })
            }
            Self::Boxed(puncts) => puncts.next().copied(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = match self {
            Self::Inline { encoded, index, .. } => {
                ((*encoded & 0b11) as usize + 1).saturating_sub(usize::from(*index))
            }
            Self::Boxed(puncts) => puncts.len(),
        };
        (len, Some(len))
    }
}

impl ExactSizeIterator for Puncts<'_> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ConcatOp {
    pub(crate) elements: Box<[ConcatMetaVarExprElem]>,
    pub(crate) span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ConcatMetaVarExprElem {
    /// There is NO preceding dollar sign, which means that this identifier should be interpreted
    /// as a literal.
    Ident(tt::Ident),
    /// There is a preceding dollar sign, which means that this identifier should be expanded
    /// and interpreted as a variable.
    Var(tt::Ident),
    /// For example, a number or a string.
    Literal(tt::Literal),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum RepeatKind {
    ZeroOrMore,
    OneOrMore,
    ZeroOrOne,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExprKind {
    // Matches expressions using the post-edition 2024. Was written using
    // `expr` in edition 2024 or later.
    Expr,
    // Matches expressions using the pre-edition 2024 rules.
    // Either written using `expr` in edition 2021 or earlier or.was written using `expr_2021`.
    Expr2021,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum MetaVarKind {
    Path,
    Ty,
    Pat,
    PatParam,
    Stmt,
    Block,
    Meta,
    Item,
    Vis,
    Expr(ExprKind),
    Ident,
    Tt,
    Lifetime,
    Literal,
}

#[derive(Clone, Debug, Eq)]
pub(crate) enum Separator {
    Literal(tt::Literal),
    Ident(tt::Ident),
    Puncts(ArrayVec<tt::Punct, MAX_GLUED_PUNCT_LEN>),
    Lifetime(tt::Punct, tt::Ident),
}

// Note that when we compare a Separator, we just care about its textual value.
impl PartialEq for Separator {
    fn eq(&self, other: &Separator) -> bool {
        use Separator::*;

        match (self, other) {
            (Ident(a), Ident(b)) => a.sym == b.sym,
            (Literal(a), Literal(b)) => a.text_and_suffix == b.text_and_suffix,
            (Puncts(a), Puncts(b)) if a.len() == b.len() => {
                let a_iter = a.iter().map(|a| a.char);
                let b_iter = b.iter().map(|b| b.char);
                a_iter.eq(b_iter)
            }
            (Lifetime(_, a), Lifetime(_, b)) => a.sym == b.sym,
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
enum Mode {
    Pattern,
    Template,
}

fn next_op(
    edition: impl Copy + Fn(SyntaxContext) -> Edition,
    first_peeked: TtElement<'_>,
    src: &mut TtIter<'_>,
    mode: Mode,
) -> Result<Op, ParseError> {
    let res = match first_peeked {
        TtElement::Leaf(tt::Leaf::Punct(p @ tt::Punct { char: '$', .. })) => {
            src.next().expect("first token already peeked");
            // Note that the '$' itself is a valid token inside macro_rules.
            let second = match src.next() {
                None => {
                    return Ok(Op::from_puncts(&[p]));
                }
                Some(it) => it,
            };
            match second {
                TtElement::Subtree(subtree, mut subtree_iter) => match subtree.delimiter.kind {
                    tt::DelimiterKind::Parenthesis => {
                        let (separator, kind) = parse_repeat(src)?;
                        let tokens = MetaTemplate::parse(edition, subtree_iter, mode)?;
                        Op::Repeat { tokens, separator: separator.map(Arc::new), kind }
                    }
                    tt::DelimiterKind::Brace => match mode {
                        Mode::Template => parse_metavar_expr(&mut subtree_iter).map_err(|()| {
                            ParseError::unexpected("invalid metavariable expression")
                        })?,
                        Mode::Pattern => {
                            return Err(ParseError::unexpected(
                                "`${}` metavariable expressions are not allowed in matchers",
                            ));
                        }
                    },
                    _ => {
                        return Err(ParseError::expected(
                            "expected `$()` repetition or `${}` expression",
                        ));
                    }
                },
                TtElement::Leaf(leaf) => match leaf {
                    tt::Leaf::Ident(ident) if ident.sym == sym::crate_ => {
                        // We simply produce identifier `$crate` here. And it will be resolved when lowering ast to Path.
                        Op::Ident {
                            sym: sym::dollar_crate,
                            span: ident.span,
                            is_raw: tt::IdentIsRaw::No,
                        }
                    }
                    tt::Leaf::Ident(ident) => {
                        let kind = eat_fragment_kind(edition, src, mode)?;
                        let name = ident.sym.clone();
                        let id = ident.span;
                        Op::Var { name, kind, id }
                    }
                    tt::Leaf::Literal(lit) if is_boolean_literal(&lit) => {
                        let kind = eat_fragment_kind(edition, src, mode)?;
                        let name = lit.text_and_suffix.clone();
                        let id = lit.span;
                        Op::Var { name, kind, id }
                    }
                    tt::Leaf::Punct(punct @ tt::Punct { char: '$', .. }) => match mode {
                        Mode::Pattern => {
                            return Err(ParseError::unexpected(
                                "`$$` is not allowed on the pattern side",
                            ));
                        }
                        Mode::Template => Op::from_puncts(&[punct]),
                    },
                    tt::Leaf::Punct(_) | tt::Leaf::Literal(_) => {
                        return Err(ParseError::expected("expected ident"));
                    }
                },
            }
        }

        TtElement::Leaf(tt::Leaf::Literal(it)) => {
            src.next().expect("first token already peeked");
            Op::from_literal(it.clone())
        }

        TtElement::Leaf(tt::Leaf::Ident(it)) => {
            src.next().expect("first token already peeked");
            Op::from_ident(it.clone())
        }

        TtElement::Leaf(tt::Leaf::Punct(_)) => {
            // There's at least one punct so this shouldn't fail.
            let puncts = src.expect_glued_punct().unwrap();
            Op::from_puncts(&puncts)
        }

        TtElement::Subtree(subtree, subtree_iter) => {
            src.next().expect("first token already peeked");
            let tokens = MetaTemplate::parse(edition, subtree_iter, mode)?;
            Op::Subtree { tokens, delimiter: Box::new(subtree.delimiter) }
        }
    };
    Ok(res)
}

fn eat_fragment_kind(
    edition: impl Copy + Fn(SyntaxContext) -> Edition,
    src: &mut TtIter<'_>,
    mode: Mode,
) -> Result<Option<MetaVarKind>, ParseError> {
    if let Mode::Pattern = mode {
        src.expect_char(':').map_err(|()| ParseError::unexpected("missing fragment specifier"))?;
        let ident = src
            .expect_ident()
            .map_err(|()| ParseError::unexpected("missing fragment specifier"))?;
        let kind = match ident.sym.as_str() {
            "path" => MetaVarKind::Path,
            "ty" => MetaVarKind::Ty,
            "pat" => {
                if edition(ident.span.ctx).at_least_2021() {
                    MetaVarKind::Pat
                } else {
                    MetaVarKind::PatParam
                }
            }
            "pat_param" => MetaVarKind::PatParam,
            "stmt" => MetaVarKind::Stmt,
            "block" => MetaVarKind::Block,
            "meta" => MetaVarKind::Meta,
            "item" => MetaVarKind::Item,
            "vis" => MetaVarKind::Vis,
            "expr" => {
                if edition(ident.span.ctx).at_least_2024() {
                    MetaVarKind::Expr(ExprKind::Expr)
                } else {
                    MetaVarKind::Expr(ExprKind::Expr2021)
                }
            }
            "expr_2021" => MetaVarKind::Expr(ExprKind::Expr2021),
            "ident" => MetaVarKind::Ident,
            "tt" => MetaVarKind::Tt,
            "lifetime" => MetaVarKind::Lifetime,
            "literal" => MetaVarKind::Literal,
            _ => return Ok(None),
        };
        return Ok(Some(kind));
    };
    Ok(None)
}

fn is_boolean_literal(lit: &tt::Literal) -> bool {
    lit.text_and_suffix == sym::true_ || lit.text_and_suffix == sym::false_
}

fn parse_repeat(src: &mut TtIter<'_>) -> Result<(Option<Separator>, RepeatKind), ParseError> {
    let mut separator = Separator::Puncts(ArrayVec::new());
    for tt in src {
        let tt = match tt {
            TtElement::Leaf(leaf) => leaf,
            TtElement::Subtree(..) => return Err(ParseError::InvalidRepeat),
        };
        let has_sep = match &separator {
            Separator::Puncts(puncts) => !puncts.is_empty(),
            _ => true,
        };
        match tt {
            tt::Leaf::Ident(ident) => match separator {
                Separator::Puncts(puncts) if puncts.is_empty() => {
                    separator = Separator::Ident(ident.clone());
                }
                Separator::Puncts(puncts) => match puncts.as_slice() {
                    [tt::Punct { char: '\'', .. }] => {
                        separator = Separator::Lifetime(puncts[0], ident.clone());
                    }
                    _ => return Err(ParseError::InvalidRepeat),
                },
                _ => return Err(ParseError::InvalidRepeat),
            },
            tt::Leaf::Literal(_) if has_sep => return Err(ParseError::InvalidRepeat),
            tt::Leaf::Literal(lit) => separator = Separator::Literal(lit.clone()),
            tt::Leaf::Punct(punct) => {
                let repeat_kind = match punct.char {
                    '*' => RepeatKind::ZeroOrMore,
                    '+' => RepeatKind::OneOrMore,
                    '?' => RepeatKind::ZeroOrOne,
                    _ => match &mut separator {
                        Separator::Puncts(puncts) if puncts.len() < 3 => {
                            puncts.push(punct);
                            continue;
                        }
                        _ => return Err(ParseError::InvalidRepeat),
                    },
                };
                return Ok((has_sep.then_some(separator), repeat_kind));
            }
        }
    }
    Err(ParseError::InvalidRepeat)
}

fn parse_metavar_expr(src: &mut TtIter<'_>) -> Result<Op, ()> {
    let func = src.expect_ident()?;
    let (args, mut args_iter) = src.expect_subtree()?;

    if args.delimiter.kind != tt::DelimiterKind::Parenthesis {
        return Err(());
    }

    let op = match &func.sym {
        s if sym::ignore == *s => {
            args_iter.expect_dollar()?;
            let ident = args_iter.expect_ident()?;
            Op::Ignore { name: ident.sym.clone(), id: ident.span }
        }
        s if sym::index == *s => Op::Index { depth: parse_depth(&mut args_iter)? },
        s if sym::len == *s => Op::Len { depth: parse_depth(&mut args_iter)? },
        s if sym::count == *s => {
            args_iter.expect_dollar()?;
            let ident = args_iter.expect_ident()?;
            let depth =
                if try_eat_comma(&mut args_iter) { parse_depth(&mut args_iter)? } else { 0 };
            Op::Count { name: ident.sym.clone(), depth }
        }
        s if sym::concat == *s => {
            let mut elements = Vec::new();
            while let Some(next) = args_iter.peek() {
                let element = if let TtElement::Leaf(tt::Leaf::Literal(lit)) = next {
                    args_iter.next().expect("already peeked");
                    ConcatMetaVarExprElem::Literal(lit.clone())
                } else {
                    let is_var = try_eat_dollar(&mut args_iter);
                    let ident = args_iter.expect_ident_or_underscore()?.clone();

                    if is_var {
                        ConcatMetaVarExprElem::Var(ident)
                    } else {
                        ConcatMetaVarExprElem::Ident(ident)
                    }
                };
                elements.push(element);
                if !args_iter.is_empty() {
                    args_iter.expect_comma()?;
                }
            }
            if elements.len() < 2 {
                return Err(());
            }
            Op::Concat {
                payload: Box::new(ConcatOp {
                    elements: elements.into_boxed_slice(),
                    span: func.span,
                }),
            }
        }
        _ => return Err(()),
    };

    if args_iter.next().is_some() {
        return Err(());
    }

    Ok(op)
}

fn parse_depth(src: &mut TtIter<'_>) -> Result<usize, ()> {
    if src.is_empty() {
        Ok(0)
    } else if let tt::Leaf::Literal(lit) = src.expect_literal()?
        && let (text, suffix) = lit.text_and_suffix()
        && suffix.is_empty()
    {
        // Suffixes are not allowed.
        text.parse().map_err(|_| ())
    } else {
        Err(())
    }
}

fn try_eat_comma(src: &mut TtIter<'_>) -> bool {
    if let Some(TtElement::Leaf(tt::Leaf::Punct(tt::Punct { char: ',', .. }))) = src.peek() {
        let _ = src.next();
        return true;
    }
    false
}

fn try_eat_dollar(src: &mut TtIter<'_>) -> bool {
    if let Some(TtElement::Leaf(tt::Leaf::Punct(tt::Punct { char: '$', .. }))) = src.peek() {
        let _ = src.next();
        return true;
    }
    false
}
