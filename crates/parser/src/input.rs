//! See [`Input`].

use edition::Edition;

use crate::SyntaxKind;

/// Input for the parser -- a sequence of tokens.
///
/// As of now, parser doesn't have access to the *text* of the tokens, and makes
/// decisions based solely on their classification. Unlike `LexerToken`, the
/// `Tokens` doesn't include whitespace and comments. Main input to the parser.
///
pub struct Input {
    token: Vec<InputToken>,
}

struct InputToken {
    kind: SyntaxKind,
    contextual_kind: SyntaxKind,
    edition: Edition,
    joint: bool,
}

/// `pub` impl used by callers to create `Tokens`.
impl Input {
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self { token: Vec::with_capacity(capacity) }
    }
    #[inline]
    pub fn push(&mut self, kind: SyntaxKind, edition: Edition) {
        self.push_impl(kind, SyntaxKind::EOF, edition)
    }
    #[inline]
    pub fn push_ident(&mut self, contextual_kind: SyntaxKind, edition: Edition) {
        self.push_impl(SyntaxKind::IDENT, contextual_kind, edition)
    }
    /// Sets jointness for the last token we've pushed.
    ///
    /// This is a separate API rather than an argument to the `push` to make it
    /// convenient both for textual and mbe tokens. With text, you know whether
    /// the *previous* token was joint, with mbe, you know whether the *current*
    /// one is joint. This API allows for styles of usage:
    ///
    /// ```ignore
    /// // In text:
    /// tokens.was_joint(prev_joint);
    /// tokens.push(curr);
    ///
    /// // In MBE:
    /// token.push(curr);
    /// tokens.push(curr_joint)
    /// ```
    #[inline]
    pub fn was_joint(&mut self) {
        self.token.last_mut().unwrap().joint = true;
    }
    #[inline]
    fn push_impl(&mut self, kind: SyntaxKind, contextual_kind: SyntaxKind, edition: Edition) {
        self.token.push(InputToken { kind, contextual_kind, edition, joint: false });
    }
}

/// pub(crate) impl used by the parser to consume `Tokens`.
impl Input {
    pub(crate) fn kind(&self, idx: usize) -> SyntaxKind {
        self.token.get(idx).map_or(SyntaxKind::EOF, |token| token.kind)
    }
    pub(crate) fn contextual_kind(&self, idx: usize) -> SyntaxKind {
        self.token.get(idx).map_or(SyntaxKind::EOF, |token| token.contextual_kind)
    }
    pub(crate) fn edition(&self, idx: usize) -> Edition {
        self.token[idx].edition
    }
    pub(crate) fn is_joint(&self, n: usize) -> bool {
        self.token[n].joint
    }
}

impl Input {
    pub fn len(&self) -> usize {
        self.token.len()
    }
}
