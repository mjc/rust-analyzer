//! This module defines Concrete Syntax Tree (CST), used by rust-analyzer.
//!
//! The CST includes comments and whitespace, provides a single node type,
//! `SyntaxNode`, and a basic traversal API (parent, children, siblings).
//!
//! The *real* implementation is in the (language-agnostic) `rowan` crate, this
//! module just wraps its API.

use std::sync::OnceLock;

use rowan::{GreenNodeBuilder, Language, SharedNodeCache};
use smallvec::SmallVec;

use crate::{Edition, Parse, SyntaxError, SyntaxKind, TextRange, TextSize};

pub(crate) use rowan::{GreenNode, GreenToken, NodeOrToken};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RustLanguage {}
impl Language for RustLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        SyntaxKind::from(raw.0)
    }

    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.into())
    }
}

pub type SyntaxNode = rowan::SyntaxNode<RustLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<RustLanguage>;
pub type SyntaxElement = rowan::SyntaxElement<RustLanguage>;
pub type SyntaxNodeChildren = rowan::SyntaxNodeChildren<RustLanguage>;
pub(crate) type SyntaxNodeChildrenByKind = rowan::SyntaxNodeChildrenByKind<RustLanguage>;
pub type SyntaxElementChildren = rowan::SyntaxElementChildren<RustLanguage>;
pub type PreorderWithTokens = rowan::api::PreorderWithTokens<RustLanguage>;

#[derive(Clone, Debug)]
pub struct SyntaxGreenToken {
    green: GreenToken,
    range: TextRange,
}

impl SyntaxGreenToken {
    pub fn kind(&self) -> SyntaxKind {
        SyntaxKind::from(self.green.kind().0)
    }

    pub fn text(&self) -> &str {
        self.green.text()
    }

    pub fn text_range(&self) -> TextRange {
        self.range
    }
}

#[derive(Debug)]
pub struct SyntaxGreenTokens {
    stack: SmallVec<[(NodeOrToken<GreenNode, GreenToken>, TextSize); 16]>,
}

impl SyntaxGreenTokens {
    fn new(node: &SyntaxNode) -> Self {
        let green = GreenNode::from(node.green());
        let mut stack = SmallVec::new();
        stack.push((NodeOrToken::Node(green), node.text_range().start()));
        Self { stack }
    }
}

impl Iterator for SyntaxGreenTokens {
    type Item = SyntaxGreenToken;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (element, offset) = self.stack.pop()?;
            match element {
                NodeOrToken::Node(node) => {
                    let mut child_offset = offset + node.text_len();
                    for child in node.children().rev() {
                        child_offset -= child.text_len();
                        let child = match child {
                            NodeOrToken::Node(node) => NodeOrToken::Node(node.to_owned()),
                            NodeOrToken::Token(token) => NodeOrToken::Token(token.to_owned()),
                        };
                        self.stack.push((child, child_offset));
                    }
                }
                NodeOrToken::Token(green) => {
                    return Some(SyntaxGreenToken {
                        range: TextRange::at(offset, green.text_len()),
                        green,
                    });
                }
            }
        }
    }
}

pub fn green_tokens(node: &SyntaxNode) -> SyntaxGreenTokens {
    SyntaxGreenTokens::new(node)
}

static STATIC_TOKENS: [OnceLock<GreenToken>; SyntaxKind::__LAST as usize] =
    [const { OnceLock::new() }; SyntaxKind::__LAST as usize];
static SHARED_NODE_CACHE: OnceLock<SharedNodeCache> = OnceLock::new();
const MAX_SHARED_NEWLINES: usize = 2;
const MAX_SHARED_SPACES: usize = 32;
static WHITESPACE_TOKENS: [[OnceLock<GreenToken>; MAX_SHARED_SPACES + 1]; MAX_SHARED_NEWLINES + 1] =
    [const { [const { OnceLock::new() }; MAX_SHARED_SPACES + 1] }; MAX_SHARED_NEWLINES + 1];

#[doc(hidden)]
pub fn clear_shared_parse_cache() {
    if let Some(cache) = SHARED_NODE_CACHE.get() {
        cache.clear();
    }
}

fn shared_whitespace(text: &str) -> Option<&'static OnceLock<GreenToken>> {
    let bytes = text.as_bytes();
    let newlines = bytes.iter().take_while(|&&byte| byte == b'\n').count();
    let spaces = bytes.len() - newlines;
    if newlines > MAX_SHARED_NEWLINES
        || spaces > MAX_SHARED_SPACES
        || bytes[newlines..].iter().any(|&byte| byte != b' ')
        || bytes.is_empty()
    {
        return None;
    }
    Some(&WHITESPACE_TOKENS[newlines][spaces])
}

pub struct SyntaxTreeBuilder {
    errors: Vec<SyntaxError>,
    inner: GreenNodeBuilder<'static>,
}

impl Default for SyntaxTreeBuilder {
    fn default() -> Self {
        Self { errors: Vec::new(), inner: GreenNodeBuilder::new() }
    }
}

impl SyntaxTreeBuilder {
    #[doc(hidden)]
    pub fn with_shared_cache() -> Self {
        let cache = SHARED_NODE_CACHE.get_or_init(SharedNodeCache::default);
        Self { errors: Vec::new(), inner: GreenNodeBuilder::with_shared_cache(cache) }
    }

    pub(crate) fn finish_raw(self) -> (GreenNode, Vec<SyntaxError>) {
        let green = self.inner.finish();
        (green, self.errors)
    }

    pub fn finish(self) -> Parse<SyntaxNode> {
        let (green, errors) = self.finish_raw();
        // Disable block validation, see https://github.com/rust-lang/rust-analyzer/pull/10357
        #[allow(clippy::overly_complex_bool_expr)]
        if cfg!(debug_assertions) && false {
            let node = SyntaxNode::new_root(green.clone());
            crate::validation::validate_block_structure(&node);
        }
        Parse::new(green, errors)
    }

    pub fn token(&mut self, kind: SyntaxKind, text: &str) {
        let rowan_kind = RustLanguage::kind_to_raw(kind);
        let shared = if (kind.is_punct() || kind.is_keyword(Edition::LATEST)) && kind.text() == text
        {
            Some(&STATIC_TOKENS[kind as usize])
        } else if kind == SyntaxKind::WHITESPACE {
            shared_whitespace(text)
        } else {
            None
        };
        if let Some(shared) = shared {
            let token = shared.get_or_init(|| GreenToken::new(rowan_kind, text));
            self.inner.token_from_green(token.clone());
        } else {
            self.inner.token(rowan_kind, text);
        }
    }

    pub fn start_node(&mut self, kind: SyntaxKind) {
        let kind = RustLanguage::kind_to_raw(kind);
        self.inner.start_node(kind);
    }

    pub fn finish_node(&mut self) {
        self.inner.finish_node();
    }

    pub fn error(&mut self, error: String, text_pos: TextSize) {
        self.errors.push(SyntaxError::new_at_offset(error, text_pos));
    }
}
