//! This module defines Concrete Syntax Tree (CST), used by rust-analyzer.
//!
//! The CST includes comments and whitespace, provides a single node type,
//! `SyntaxNode`, and a basic traversal API (parent, children, siblings).
//!
//! The *real* implementation is in the (language-agnostic) `rowan` crate, this
//! module just wraps its API.

use std::sync::OnceLock;

use rowan::{GreenNodeBuilder, Language};

use crate::{Edition, Parse, SyntaxError, SyntaxKind, TextSize};

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
pub type SyntaxElementChildren = rowan::SyntaxElementChildren<RustLanguage>;
pub type PreorderWithTokens = rowan::api::PreorderWithTokens<RustLanguage>;

static FIXED_TOKENS: [OnceLock<GreenToken>; SyntaxKind::__LAST as usize] =
    [const { OnceLock::new() }; SyntaxKind::__LAST as usize];
static FIXED_TOKEN_LEAF_NODES: [OnceLock<GreenNode>; SyntaxKind::__LAST as usize] =
    [const { OnceLock::new() }; SyntaxKind::__LAST as usize];
const MAX_SHARED_NEWLINES: usize = 2;
const MAX_SHARED_SPACES: usize = 32;
static WHITESPACE_TOKENS: [[OnceLock<GreenToken>; MAX_SHARED_SPACES + 1]; MAX_SHARED_NEWLINES + 1] =
    [const { [const { OnceLock::new() }; MAX_SHARED_SPACES + 1] }; MAX_SHARED_NEWLINES + 1];

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
        Self {
            errors: Vec::new(),
            inner: GreenNodeBuilder::with_static_leaf_nodes(&FIXED_TOKEN_LEAF_NODES),
        }
    }
}

impl SyntaxTreeBuilder {
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
            Some(&FIXED_TOKENS[kind as usize])
        } else if kind == SyntaxKind::WHITESPACE {
            shared_whitespace(text)
        } else {
            None
        };
        if let Some(shared) = shared {
            let token = shared.get_or_init(|| GreenToken::new(rowan_kind, text));
            self.inner.token_from_static_green(token.clone());
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
