//! Span maps for real files and macro expansions.

use base_db::SourceDatabase;
use span::Span;
use syntax::{AstNode, SyntaxKind, SyntaxNodePtr, TextRange, TextSize, ast};

pub use span::RealSpanMap;

use crate::{HirFileId, MacroCallId};

pub type ExpansionSpanMap = span::SpanMap;

/// Spanmap for a macro file or a real file
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpanMap<'db> {
    /// Spanmap for a macro file
    ExpansionSpanMap(&'db ExpansionSpanMap),
    /// Spanmap for a real file
    RealSpanMap(&'db RealSpanMap),
}

impl syntax_bridge::SpanMapper for SpanMap<'_> {
    fn span_for(&self, range: TextRange) -> Span {
        self.span_for_range(range)
    }
}

impl<'db> SpanMap<'db> {
    pub fn span_for_range(&self, range: TextRange) -> Span {
        match self {
            // FIXME: Is it correct for us to only take the span at the start? This feels somewhat
            // wrong. The context will be right, but the range could be considered wrong. See
            // https://github.com/rust-lang/rust/issues/23480, we probably want to fetch the span at
            // the start and end, then merge them like rustc does in `Span::to`
            Self::ExpansionSpanMap(span_map) => span_map.span_at(range.start()),
            Self::RealSpanMap(span_map) => span_map.span_for_range(range),
        }
    }
}

impl HirFileId {
    #[inline]
    pub fn span_map<'db>(self, db: &'db dyn SourceDatabase) -> SpanMap<'db> {
        match self {
            HirFileId::FileId(file_id) => SpanMap::RealSpanMap(real_span_map(db, file_id)),
            HirFileId::MacroFile(m) => SpanMap::ExpansionSpanMap(m.expansion_span_map(db)),
        }
    }
}

/// This is an implementation detail of [`HirFileId::span_map`]. Outside this crate, use
/// `HirFileId::from(file_id).span_map(db)` instead of `real_span_map(db, file_id)`.
#[salsa::tracked(returns(ref))]
pub(crate) fn real_span_map(
    db: &dyn SourceDatabase,
    editioned_file_id: base_db::EditionedFileId,
) -> RealSpanMap {
    use syntax::ast::HasModuleItem;
    let mut pairs = vec![(syntax::TextSize::new(0), span::ROOT_ERASED_FILE_AST_ID)];
    let ast_id_map = HirFileId::from(editioned_file_id).ast_id_map(db);

    let tree = editioned_file_id.parse(db).tree();
    // This is an incrementality layer. Basically we can't use absolute ranges for our spans as that
    // would mean we'd invalidate everything whenever we type. So instead we make the text ranges
    // relative to some AstIds reducing the risk of invalidation as typing somewhere no longer
    // affects all following spans in the file.
    // There is some stuff to bear in mind here though, for one, the more "anchors" we create, the
    // easier it gets to invalidate things again as spans are as stable as their anchor's ID.
    // The other problem is proc-macros. Proc-macros have a `Span::join` api that allows them
    // to join two spans that come from the same file. rust-analyzer's proc-macro server
    // can only join two spans if they belong to the same anchor though, as the spans are relative
    // to that anchor. To do cross anchor joining we'd need to access to the ast id map to resolve
    // them again, something we might get access to in the future. But even then, proc-macros doing
    // this kind of joining makes them as stable as the AstIdMap (which is basically changing on
    // every input of the file)…

    let ptr_to_entry =
        |ptr: SyntaxNodePtr| (ptr.text_range().start(), ast_id_map.erased_ast_id_for_ptr(ptr));
    let item_to_entry = |item: ast::Item| ptr_to_entry(SyntaxNodePtr::new(item.syntax()));
    let mut nested_pairs = Vec::new();
    // Unfortunately, assoc items are very common in Rust, so descend into those as well and make
    // them anchors too, but only if they have no attributes attached, as those might be proc-macros
    // and using different anchors inside of them will prevent spans from being joinable.
    for ptr in top_level_item_ptrs(&tree) {
        // Top level items make for great anchors as they are the most stable and a decent boundary.
        pairs.push(ptr_to_entry(ptr));
        if !matches!(
            ptr.kind(),
            SyntaxKind::EXTERN_BLOCK | SyntaxKind::IMPL | SyntaxKind::MODULE | SyntaxKind::TRAIT
        ) {
            continue;
        }
        let Some(item) = ptr.try_to_node(tree.syntax()).and_then(ast::Item::cast) else {
            stdx::never!("top-level item pointer did not resolve");
            continue;
        };
        match &item {
            ast::Item::ExternBlock(it) if ast::attrs_including_inner(it).next().is_none() => {
                if let Some(extern_item_list) = it.extern_item_list() {
                    nested_pairs.extend(
                        extern_item_list.extern_items().map(ast::Item::from).map(item_to_entry),
                    );
                }
            }
            ast::Item::Impl(it) if ast::attrs_including_inner(it).next().is_none() => {
                if let Some(assoc_item_list) = it.assoc_item_list() {
                    nested_pairs.extend(
                        assoc_item_list.assoc_items().map(ast::Item::from).map(item_to_entry),
                    );
                }
            }
            ast::Item::Module(it) if ast::attrs_including_inner(it).next().is_none() => {
                if let Some(item_list) = it.item_list() {
                    nested_pairs.extend(item_list.items().map(item_to_entry));
                }
            }
            ast::Item::Trait(it) if ast::attrs_including_inner(it).next().is_none() => {
                if let Some(assoc_item_list) = it.assoc_item_list() {
                    nested_pairs.extend(
                        assoc_item_list.assoc_items().map(ast::Item::from).map(item_to_entry),
                    );
                }
            }
            _ => (),
        }
    }
    // Keep the existing top-level-then-nested anchor order without traversing top-level items twice.
    pairs.extend(nested_pairs);

    RealSpanMap::from_file(
        editioned_file_id.span_file_id(db),
        pairs.into_boxed_slice(),
        tree.syntax().text_range().end(),
    )
}

fn top_level_item_ptrs(tree: &ast::SourceFile) -> impl Iterator<Item = SyntaxNodePtr> + '_ {
    let mut offset = TextSize::new(0);
    tree.syntax().green().children().filter_map(move |child| {
        let range = TextRange::at(offset, child.text_len());
        offset += child.text_len();
        let child = child.as_node()?;
        let kind = SyntaxKind::from(child.kind().0);
        ast::Item::can_cast(kind).then(|| SyntaxNodePtr::from_kind_and_range(kind, range))
    })
}

impl MacroCallId {
    pub fn expansion_span_map(self, db: &dyn SourceDatabase) -> &ExpansionSpanMap {
        &self.parse_macro_expansion(db).value.1
    }
}

#[cfg(test)]
mod tests {
    use syntax::{AstNode, Edition, SourceFile, ast::HasModuleItem};

    use super::top_level_item_ptrs;

    #[test]
    fn green_item_pointers_resolve_like_red_items() {
        let tree =
            SourceFile::parse("fn first() {}\n\n#[cfg(test)]\nstruct Second;\n", Edition::CURRENT)
                .tree();
        let expected = tree.items().map(|item| item.syntax().text_range()).collect::<Vec<_>>();
        let actual = top_level_item_ptrs(&tree)
            .map(|ptr| ptr.try_to_node(tree.syntax()).unwrap().text_range())
            .collect::<Vec<_>>();

        assert_eq!(actual, expected);
    }
}
