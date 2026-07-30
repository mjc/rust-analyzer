//! `AstIdMap` allows to create stable IDs for "large" syntax nodes like items
//! and macro calls.
//!
//! Specifically, it enumerates all items in a file and uses the position of an
//! item as an ID. That way, IDs don't change unless the set of items itself
//! changes.
//!
//! These IDs are tricky. If one of them invalidates, its interned ID invalidates,
//! and this can cause *a lot* to be recomputed. For example, if you invalidate the ID
//! of a struct, and that struct has an impl (any impl!) this will cause the `Self`
//! type of the impl to invalidate, which will cause the all impls queries to be
//! invalidated, which will cause every trait solve query in this crate *and* all
//! transitive reverse dependencies to be invalidated, which is pretty much the worst
//! thing that can happen incrementality wise.
//!
//! So we want these IDs to stay as stable as possible. For top-level items, we store
//! their kind and name, which should be unique, but since they can still not be, we
//! also store an index disambiguator. For nested items, we also store the ID of their
//! parent. For macro calls, we store the macro name and an index. There aren't usually
//! a lot of macro calls in item position, and invalidation in bodies is not much of
//! a problem, so this should be enough.

use std::{
    any::type_name,
    fmt,
    hash::{BuildHasher, Hash, Hasher},
    marker::PhantomData,
};

use la_arena::{Arena, Idx, RawIdx};
use rustc_hash::{FxBuildHasher, FxHashMap};
use smallvec::SmallVec;
use syntax::{
    AstNode, AstPtr, GreenNode, NodeOrToken, SyntaxKind, SyntaxNode, SyntaxNodePtr, TextRange, ast,
};

// The first index is always the root node's AstId
/// The root ast id always points to the encompassing file, using this in spans is discouraged as
/// any range relative to it will be effectively absolute, ruining the entire point of anchored
/// relative text ranges.
pub const ROOT_ERASED_FILE_AST_ID: ErasedFileAstId =
    ErasedFileAstId(pack_hash_index_and_kind(0, 0, ErasedFileAstIdKind::Root as u32));

/// ErasedFileAstId used as the span for syntax node fixups. Any Span containing this file id is to be
/// considered fake.
/// Do not modify this, it is used by the proc-macro server.
pub const FIXUP_ERASED_FILE_AST_ID_MARKER: ErasedFileAstId =
    ErasedFileAstId(pack_hash_index_and_kind(0, 0, ErasedFileAstIdKind::Fixup as u32));

/// [`ErasedFileAstId`] used as the span for syntax nodes that should not be mapped down to
/// macro expansion. Any `Span` containing this file id is to be considered fake.
pub const NO_DOWNMAP_ERASED_FILE_AST_ID_MARKER: ErasedFileAstId =
    ErasedFileAstId(pack_hash_index_and_kind(0, 0, ErasedFileAstIdKind::NoDownmap as u32));

/// This is a type erased FileAstId.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ErasedFileAstId(u32);

impl fmt::Debug for ErasedFileAstId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = self.kind();
        macro_rules! kind {
            ($($kind:ident),* $(,)?) => {
                if false {
                    // Ensure we covered all variants.
                    match ErasedFileAstIdKind::Root {
                        $( ErasedFileAstIdKind::$kind => {} )*
                    }
                    unreachable!()
                }
                $( else if kind == ErasedFileAstIdKind::$kind as u32 {
                    stringify!($kind)
                } )*
                else {
                    "Unknown"
                }
            };
        }
        let kind = kind!(
            Root,
            Enum,
            Struct,
            Union,
            ExternCrate,
            MacroDef,
            MacroRules,
            Module,
            Static,
            Trait,
            Variant,
            Const,
            Fn,
            MacroCall,
            TypeAlias,
            ExternBlock,
            Use,
            Impl,
            BlockExpr,
            AsmExpr,
            Fixup,
            NoDownmap,
        );
        if f.alternate() {
            write!(f, "{kind}[{:04X}, {}]", self.hash_value(), self.index())
        } else {
            f.debug_struct("ErasedFileAstId")
                .field("kind", &format_args!("{kind}"))
                .field("index", &self.index())
                .field("hash", &format_args!("{:04X}", self.hash_value()))
                .finish()
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[repr(u8)]
enum ErasedFileAstIdKind {
    /// This needs to not change because it's depended upon by the proc macro server.
    Fixup = 0,
    // The following are associated with `ErasedHasNameFileAstId`.
    Enum,
    Struct,
    Union,
    ExternCrate,
    MacroDef,
    MacroRules,
    Module,
    Static,
    Trait,
    // Until here associated with `ErasedHasNameFileAstId`.
    // The following are associated with `ErasedAssocItemFileAstId`.
    Variant,
    Const,
    Fn,
    MacroCall,
    TypeAlias,
    // Until here associated with `ErasedAssocItemFileAstId`.
    // Extern blocks don't really have any identifying property unfortunately.
    ExternBlock,
    // FIXME: If we store the final `UseTree` instead of the top-level `Use`, we can store its name,
    // and be way more granular for incrementality, at the expense of increased memory usage.
    // Use IDs aren't used a lot. The main thing that stores them is the def map. So everything that
    // uses the def map will be invalidated. That includes infers, and so is pretty bad, but our
    // def map incrementality story is pretty bad anyway and needs to be improved (see
    // https://rust-lang.zulipchat.com/#narrow/channel/185405-t-compiler.2Frust-analyzer/topic/.60infer.60.20queries.20and.20splitting.20.60DefMap.60).
    // So I left this as-is for now, as the def map improvement should also mitigate this.
    Use,
    /// Associated with [`ImplFileAstId`].
    Impl,
    /// Associated with [`BlockExprFileAstId`].
    BlockExpr,
    // `global_asm!()` is an item, so we need to give it an `AstId`. So we give to all inline asm
    // because incrementality is not a problem, they will always be the only item in the macro file,
    // and memory usage also not because they're rare.
    AsmExpr,
    /// Represents a fake [`ErasedFileAstId`] that should not be mapped down to macro expansion
    /// result.
    NoDownmap,
    /// Keep this last.
    Root,
}

// First hash, then index, then kind.
const HASH_BITS: u32 = 16;
const INDEX_BITS: u32 = 11;
const KIND_BITS: u32 = 5;
const _: () = assert!(ErasedFileAstIdKind::Root as u32 <= ((1 << KIND_BITS) - 1));
const _: () = assert!(HASH_BITS + INDEX_BITS + KIND_BITS == u32::BITS);

#[inline]
const fn u16_hash(hash: u64) -> u16 {
    // We do basically the same as `FxHasher`. We don't use rustc-hash and truncate because the
    // higher bits have more entropy, but unlike rustc-hash we don't rotate because it rotates
    // for hashmaps that just use the low bits, but we compare all bits.
    const K: u16 = 0xecc5;
    let (part1, part2, part3, part4) =
        (hash as u16, (hash >> 16) as u16, (hash >> 32) as u16, (hash >> 48) as u16);
    part1
        .wrapping_add(part2)
        .wrapping_mul(K)
        .wrapping_add(part3)
        .wrapping_mul(K)
        .wrapping_add(part4)
        .wrapping_mul(K)
}

#[inline]
const fn pack_hash_index_and_kind(hash: u16, index: u32, kind: u32) -> u32 {
    (hash as u32) | (index << HASH_BITS) | (kind << (HASH_BITS + INDEX_BITS))
}

impl ErasedFileAstId {
    #[inline]
    fn hash_value(self) -> u16 {
        self.0 as u16
    }

    #[inline]
    fn index(self) -> u32 {
        (self.0 << KIND_BITS) >> (HASH_BITS + KIND_BITS)
    }

    #[inline]
    fn kind(self) -> u32 {
        self.0 >> (HASH_BITS + INDEX_BITS)
    }

    #[inline]
    pub fn is_root(self) -> bool {
        self.kind() == ErasedFileAstIdKind::Root as u32
    }

    fn ast_id_for_green(
        node: &GreenNode,
        index_map: &mut ErasedAstIdNextIndexMap,
        parent: Option<&ErasedFileAstId>,
    ) -> Option<ErasedFileAstId> {
        let syntax_kind = SyntaxKind::from(node.kind().0);
        if let Some((kind, name_kind)) = has_name_kind(syntax_kind) {
            let data = ErasedHasNameFileAstId { name: direct_child_text(node, name_kind) };
            return Some(index_map.new_id(kind, data));
        }
        if let Some(kind) = assoc_item_kind(syntax_kind) {
            let name = if kind == ErasedFileAstIdKind::MacroCall {
                macro_call_name(node)
            } else {
                direct_child_text(node, SyntaxKind::NAME)
            };
            let data = ErasedAssocItemFileAstId {
                parent: parent.copied(),
                properties: ErasedHasNameFileAstId { name },
            };
            return Some(index_map.new_id(kind, data));
        }
        if ast::ExternBlock::can_cast(syntax_kind) {
            return Some(index_map.new_id(ErasedFileAstIdKind::ExternBlock, ()));
        }
        if ast::Use::can_cast(syntax_kind) {
            return Some(index_map.new_id(ErasedFileAstIdKind::Use, ()));
        }
        if ast::Impl::can_cast(syntax_kind) {
            return Some(impl_ast_id(node, index_map));
        }
        if ast::AsmExpr::can_cast(syntax_kind) {
            return Some(index_map.new_id(ErasedFileAstIdKind::AsmExpr, ()));
        }
        None
    }

    fn should_alloc(kind: SyntaxKind) -> Option<ErasedFileAstIdKind> {
        should_alloc_has_name(kind)
            .or_else(|| should_alloc_assoc_item(kind))
            .or_else(|| {
                ast::ExternBlock::can_cast(kind).then_some(ErasedFileAstIdKind::ExternBlock)
            })
            .or_else(|| ast::Use::can_cast(kind).then_some(ErasedFileAstIdKind::Use))
            .or_else(|| ast::Impl::can_cast(kind).then_some(ErasedFileAstIdKind::Impl))
            .or_else(|| ast::AsmExpr::can_cast(kind).then_some(ErasedFileAstIdKind::AsmExpr))
    }

    #[inline]
    pub fn into_raw(self) -> u32 {
        self.0
    }

    #[inline]
    pub const fn from_raw(v: u32) -> Self {
        Self(v)
    }
}

pub trait AstIdNode: AstNode {}

/// `AstId` points to an AST node in a specific file.
pub struct FileAstId<N> {
    raw: ErasedFileAstId,
    _marker: PhantomData<fn() -> N>,
}

/// Traits are manually implemented because `derive` adds redundant bounds.
impl<N> Clone for FileAstId<N> {
    #[inline]
    fn clone(&self) -> FileAstId<N> {
        *self
    }
}
impl<N> Copy for FileAstId<N> {}

impl<N> PartialEq for FileAstId<N> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}
impl<N> Eq for FileAstId<N> {}
impl<N> Hash for FileAstId<N> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.raw.hash(hasher);
    }
}

impl<N> fmt::Debug for FileAstId<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileAstId::<{}>({:?})", type_name::<N>(), self.raw)
    }
}

impl<N> FileAstId<N> {
    // Can't make this a From implementation because of coherence
    #[inline]
    pub fn upcast<M: AstIdNode>(self) -> FileAstId<M>
    where
        N: Into<M>,
    {
        FileAstId { raw: self.raw, _marker: PhantomData }
    }

    #[inline]
    pub fn erase(self) -> ErasedFileAstId {
        self.raw
    }
}

#[derive(Hash)]
struct ErasedHasNameFileAstId<'a> {
    name: &'a str,
}

/// This holds the ast ID for variants too (they're a kind of assoc item).
#[derive(Hash)]
struct ErasedAssocItemFileAstId<'a> {
    /// Subtle: items in `extern` blocks **do not** store the ID of the extern block here.
    /// Instead this is left empty. The reason is that `ExternBlockFileAstId` is pretty unstable
    /// (it contains only an index), and extern blocks don't introduce a new scope, so storing
    /// the extern block ID will do more harm to incrementality than help.
    parent: Option<ErasedFileAstId>,
    properties: ErasedHasNameFileAstId<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ImplFileAstId<'a> {
    /// This can be `None` if the `Self` type is not a named type, or if it is inside a macro call.
    self_ty_name: Option<&'a str>,
    /// This can be `None` if this is an inherent impl, or if the trait name is inside a macro call.
    trait_name: Option<&'a str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BlockExprFileAstId {
    parent: Option<ErasedFileAstId>,
}

impl AstIdNode for ast::ExternBlock {}
impl AstIdNode for ast::Use {}
impl AstIdNode for ast::AsmExpr {}

impl AstIdNode for ast::Impl {}

fn impl_ast_id(node: &GreenNode, index_map: &mut ErasedAstIdNextIndexMap) -> ErasedFileAstId {
    let mut types = node.children().filter_map(|child| {
        let child = child.into_node()?;
        ast::Type::can_cast(SyntaxKind::from(child.kind().0)).then(|| (*child).to_owned())
    });
    let first = types.next();
    let second = types.next();
    let has_for = node.children().any(|child| {
        child.as_token().is_some_and(|token| SyntaxKind::from(token.kind().0) == SyntaxKind::FOR_KW)
    });
    let (trait_ty, self_ty) =
        if has_for { (first.as_ref(), second.as_ref()) } else { (None, first.as_ref()) };
    let data = ImplFileAstId {
        self_ty_name: self_ty.and_then(path_type_name),
        trait_name: trait_ty.and_then(path_type_name),
    };
    index_map.new_id(ErasedFileAstIdKind::Impl, data)
}

fn path_type_name(node: &GreenNode) -> Option<&str> {
    if SyntaxKind::from(node.kind().0) != SyntaxKind::PATH_TYPE {
        return None;
    }
    node.children()
        .find_map(|child| {
            let path = child.into_node()?;
            (SyntaxKind::from(path.kind().0) == SyntaxKind::PATH).then_some(path)
        })?
        .children()
        .find_map(|child| {
            let segment = child.into_node()?;
            (SyntaxKind::from(segment.kind().0) == SyntaxKind::PATH_SEGMENT).then_some(segment)
        })?
        .children()
        .find_map(|child| {
            let name_ref = child.into_node()?;
            (SyntaxKind::from(name_ref.kind().0) == SyntaxKind::NAME_REF)
                .then(|| name_ref.children().next().and_then(NodeOrToken::into_token))
                .flatten()
                .map(|token| token.text())
        })
}

fn macro_call_name(node: &GreenNode) -> &str {
    node.children()
        .find_map(|child| {
            let path = child.into_node()?;
            (SyntaxKind::from(path.kind().0) == SyntaxKind::PATH).then_some(path)
        })
        .and_then(|path| {
            path.children().find_map(|child| {
                let segment = child.into_node()?;
                (SyntaxKind::from(segment.kind().0) == SyntaxKind::PATH_SEGMENT).then_some(segment)
            })
        })
        .and_then(|segment| {
            segment.children().find_map(|child| {
                let name_ref = child.into_node()?;
                (SyntaxKind::from(name_ref.kind().0) == SyntaxKind::NAME_REF).then_some(name_ref)
            })
        })
        .and_then(|name_ref| name_ref.children().next().and_then(NodeOrToken::into_token))
        .map_or("", |token| token.text())
}

fn block_expr_ast_id(
    index_map: &mut ErasedAstIdNextIndexMap,
    parent: Option<&ErasedFileAstId>,
) -> ErasedFileAstId {
    index_map.new_id(ErasedFileAstIdKind::BlockExpr, BlockExprFileAstId { parent: parent.copied() })
}

// Blocks aren't `AstIdNode`s deliberately, because unlike other nodes, not all blocks get their own
// ast id, only if they have items. To account for that we have a different, fallible, API for blocks.
// impl !AstIdNode for ast::BlockExpr {}

#[derive(Default)]
struct ErasedAstIdNextIndexMap(FxHashMap<(ErasedFileAstIdKind, u16), u32>);

impl ErasedAstIdNextIndexMap {
    #[inline]
    fn new_id(&mut self, kind: ErasedFileAstIdKind, data: impl Hash) -> ErasedFileAstId {
        let hash = FxBuildHasher.hash_one(&data);
        let initial_hash = u16_hash(hash);
        // Even though 2^INDEX_BITS=2048 items with the same hash seems like a lot,
        // it could happen with macro calls or `use`s in macro-generated files. So we want
        // to handle it gracefully. We just increment the hash.
        let mut hash = initial_hash;
        let index = loop {
            match self.0.entry((kind, hash)) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let i = entry.get_mut();
                    if *i < ((1 << INDEX_BITS) - 1) {
                        *i += 1;
                        break *i;
                    }
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(0);
                    break 0;
                }
            }
            hash = hash.wrapping_add(1);
            if hash == initial_hash {
                // That's 2^27=134,217,728 items!
                panic!("you have way too many items in the same file!");
            }
        };
        let kind = kind as u32;
        ErasedFileAstId(pack_hash_index_and_kind(hash, index, kind))
    }
}

macro_rules! register_enum_ast_id {
    (impl $AstIdNode:ident for $($ident:ident),+ ) => {
        $(
            impl $AstIdNode for ast::$ident {}
        )+
    };
}
register_enum_ast_id! {
    impl AstIdNode for
    Item, AnyHasGenericParams, Adt, Macro,
    AssocItem
}

fn direct_child_text(node: &GreenNode, kind: SyntaxKind) -> &str {
    node.children()
        .find_map(|child| {
            let child = child.as_node()?;
            (SyntaxKind::from(child.kind().0) == kind)
                .then(|| child.children().next().and_then(NodeOrToken::into_token))
                .flatten()
                .map(|token| token.text())
        })
        .unwrap_or("")
}

macro_rules! register_has_name_ast_id {
    (impl $AstIdNode:ident for $($ident:ident = $name_kind:ident),+ ) => {
        $(
            impl $AstIdNode for ast::$ident {}
        )+

        fn has_name_kind(kind: SyntaxKind) -> Option<(ErasedFileAstIdKind, SyntaxKind)> {
            $( if ast::$ident::can_cast(kind) {
                Some((ErasedFileAstIdKind::$ident, SyntaxKind::$name_kind))
            } else )* { None }
        }

        fn should_alloc_has_name(kind: SyntaxKind) -> Option<ErasedFileAstIdKind> {
            has_name_kind(kind).map(|(kind, _)| kind)
        }
    };
}
register_has_name_ast_id! {
    impl AstIdNode for
        Enum = NAME,
        Struct = NAME,
        Union = NAME,
        ExternCrate = NAME_REF,
        MacroDef = NAME,
        MacroRules = NAME,
        Module = NAME,
        Static = NAME,
        Trait = NAME
}

macro_rules! register_assoc_item_ast_id {
    (impl $AstIdNode:ident for $($ident:ident),+ ) => {
        $(
            impl $AstIdNode for ast::$ident {}
        )+

        fn assoc_item_kind(kind: SyntaxKind) -> Option<ErasedFileAstIdKind> {
            $( if ast::$ident::can_cast(kind) { Some(ErasedFileAstIdKind::$ident) } else )*
            if ast::MacroCall::can_cast(kind) { Some(ErasedFileAstIdKind::MacroCall) } else { None }
        }

        fn should_alloc_assoc_item(kind: SyntaxKind) -> Option<ErasedFileAstIdKind> {
            assoc_item_kind(kind)
        }
    };
}
register_assoc_item_ast_id! {
    impl AstIdNode for
    Variant,
    Const,
    Fn,
    TypeAlias
}
impl AstIdNode for ast::MacroCall {}

/// Maps items' `SyntaxNode`s to `ErasedFileAstId`s and back.
#[derive(Default)]
pub struct AstIdMap {
    /// An arena of the ptrs and their associated ID.
    arena: Arena<(SyntaxNodePtr, ErasedFileAstId)>,
    /// Map ptr to id.
    ptr_map: hashbrown::HashTable<ArenaId>,
    /// Map id to ptr.
    id_map: hashbrown::HashTable<ArenaId>,
}

type ArenaId = Idx<(SyntaxNodePtr, ErasedFileAstId)>;

impl fmt::Debug for AstIdMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AstIdMap").field("arena", &self.arena).finish()
    }
}

impl PartialEq for AstIdMap {
    fn eq(&self, other: &Self) -> bool {
        self.arena == other.arena
    }
}
impl Eq for AstIdMap {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ContainsItems {
    Yes,
    No,
}

enum GreenWalkEvent {
    Enter {
        green: GreenNode,
        range: TextRange,
        parent_kind: SyntaxKind,
        grandparent_kind: Option<SyntaxKind>,
    },
    LeaveBlock,
}

impl AstIdMap {
    pub fn len(&self) -> usize {
        self.arena.len()
    }

    pub fn from_source(node: &SyntaxNode) -> AstIdMap {
        assert!(node.parent().is_none());
        let mut res = AstIdMap::default();
        let mut index_map = ErasedAstIdNextIndexMap::default();

        // Ensure we allocate the root.
        res.arena.alloc((SyntaxNodePtr::new(node), ROOT_ERASED_FILE_AST_ID));

        // By walking the tree in breadth-first order we make sure that parents
        // get lower ids then children. That is, adding a new child does not
        // change parent's id. This means that, say, adding a new function to a
        // trait does not change ids of top-level items, which helps caching.

        // This contains the stack of the `BlockExpr`s we are under. We do this
        // so we only allocate `BlockExpr`s if they contain items.
        // The general idea is: when we enter a block we push `(block, false)` here.
        // Items inside the block are attributed to the block's container, not the block.
        // For the first item we find inside a block, we make this `(block, true)`
        // and create an ast id for the block. When exiting the block we pop it,
        // whether or not we created an ast id for it.
        // It may seem that with this setup we will generate an ID for blocks that
        // have no items directly but have items inside other items inside them.
        // This is true, but it doesn't matter, because such blocks can't exist.
        // After all, the block will then contain the *outer* item, so we allocate
        // an ID for it anyway.
        let mut blocks: SmallVec<[(TextRange, ContainsItems); 4]> = SmallVec::new();
        let mut curr_layer: SmallVec<[(GreenNode, TextRange, Option<ArenaId>); 32]> =
            SmallVec::new();
        curr_layer.push((GreenNode::from(node.green()), node.text_range(), None));
        let mut next_layer: SmallVec<[(GreenNode, TextRange, Option<ArenaId>); 32]> =
            SmallVec::new();
        while !curr_layer.is_empty() {
            for (layer_root, layer_range, parent_idx) in curr_layer.drain(..) {
                let mut walk_stack: SmallVec<[GreenWalkEvent; 64]> = SmallVec::new();
                let layer_kind = SyntaxKind::from(layer_root.kind().0);
                let mut offset = layer_range.end();
                for child in layer_root.children().rev() {
                    let len = child.text_len();
                    offset -= len;
                    if let Some(child) = child.as_node() {
                        walk_stack.push(GreenWalkEvent::Enter {
                            green: (*child).to_owned(),
                            range: TextRange::at(offset, len),
                            parent_kind: layer_kind,
                            grandparent_kind: None,
                        });
                    }
                }
                while let Some(event) = walk_stack.pop() {
                    let GreenWalkEvent::Enter { green, range, parent_kind, grandparent_kind } =
                        event
                    else {
                        blocks.pop();
                        continue;
                    };
                    let syntax_kind = SyntaxKind::from(green.kind().0);
                    let is_block = ast::BlockExpr::can_cast(syntax_kind);
                    if is_block {
                        blocks.push((range, ContainsItems::No));
                        walk_stack.push(GreenWalkEvent::LeaveBlock);
                    } else if let Some(kind) = ErasedFileAstId::should_alloc(syntax_kind) {
                        // Allocate blocks on-demand, only if they have items.
                        // We don't associate items with blocks, only with items, since block IDs can be quite unstable.
                        // FIXME: Is this the correct thing to do? Macro calls might actually be more incremental if
                        // associated with blocks (not sure). Either way it's not a big deal.
                        let is_item = matches!(
                            kind,
                            ErasedFileAstIdKind::Enum
                                | ErasedFileAstIdKind::Struct
                                | ErasedFileAstIdKind::Union
                                | ErasedFileAstIdKind::ExternCrate
                                | ErasedFileAstIdKind::MacroDef
                                | ErasedFileAstIdKind::MacroRules
                                | ErasedFileAstIdKind::Module
                                | ErasedFileAstIdKind::Static
                                | ErasedFileAstIdKind::Trait
                                | ErasedFileAstIdKind::Const
                                | ErasedFileAstIdKind::Fn
                                | ErasedFileAstIdKind::TypeAlias
                                | ErasedFileAstIdKind::ExternBlock
                                | ErasedFileAstIdKind::Use
                                | ErasedFileAstIdKind::Impl
                        );
                        if let Some((last_block_range, already_allocated @ ContainsItems::No)) =
                            blocks.last_mut()
                            && (is_item
                                || (kind == ErasedFileAstIdKind::MacroCall
                                    && parent_kind == SyntaxKind::MACRO_EXPR
                                    && grandparent_kind.is_some_and(|kind| {
                                        kind == SyntaxKind::EXPR_STMT
                                            || kind == SyntaxKind::STMT_LIST
                                    })))
                        {
                            let parent = parent_of(parent_idx, &res);
                            let block_ast_id = block_expr_ast_id(&mut index_map, parent);
                            let block_ptr = SyntaxNodePtr::from_kind_and_range(
                                SyntaxKind::BLOCK_EXPR,
                                *last_block_range,
                            );
                            res.arena.alloc((block_ptr, block_ast_id));
                            *already_allocated = ContainsItems::Yes;
                        }

                        let parent = parent_of(parent_idx, &res);
                        let Some(ast_id) =
                            ErasedFileAstId::ast_id_for_green(&green, &mut index_map, parent)
                        else {
                            stdx::never!("AST-ID candidate had no identity data");
                            continue;
                        };
                        let ptr = SyntaxNodePtr::from_kind_and_range(syntax_kind, range);
                        let idx = res.arena.alloc((ptr, ast_id));

                        next_layer.push((green, range, Some(idx)));
                        continue;
                    }

                    let mut offset = range.end();
                    for child in green.children().rev() {
                        let len = child.text_len();
                        offset -= len;
                        if let Some(child) = child.as_node() {
                            walk_stack.push(GreenWalkEvent::Enter {
                                green: (*child).to_owned(),
                                range: TextRange::at(offset, len),
                                parent_kind: syntax_kind,
                                grandparent_kind: Some(parent_kind),
                            });
                        }
                    }
                }
            }
            std::mem::swap(&mut curr_layer, &mut next_layer);
            assert!(blocks.is_empty(), "didn't leave all BlockExprs");
        }

        res.ptr_map = hashbrown::HashTable::with_capacity(res.arena.len());
        res.id_map = hashbrown::HashTable::with_capacity(res.arena.len());
        for (idx, (ptr, ast_id)) in res.arena.iter() {
            let ptr_hash = hash_ptr(ptr);
            let ast_id_hash = hash_ast_id(ast_id);
            match res.ptr_map.entry(
                ptr_hash,
                |idx2| *idx2 == idx,
                |&idx| hash_ptr(&res.arena[idx].0),
            ) {
                hashbrown::hash_table::Entry::Occupied(_) => unreachable!(),
                hashbrown::hash_table::Entry::Vacant(entry) => {
                    entry.insert(idx);
                }
            }
            match res.id_map.entry(
                ast_id_hash,
                |idx2| *idx2 == idx,
                |&idx| hash_ast_id(&res.arena[idx].1),
            ) {
                hashbrown::hash_table::Entry::Occupied(_) => unreachable!(),
                hashbrown::hash_table::Entry::Vacant(entry) => {
                    entry.insert(idx);
                }
            }
        }
        res.arena.shrink_to_fit();
        return res;

        fn parent_of(parent_idx: Option<ArenaId>, res: &AstIdMap) -> Option<&ErasedFileAstId> {
            let mut parent = parent_idx.map(|parent_idx| &res.arena[parent_idx].1);
            if parent.is_some_and(|parent| parent.kind() == ErasedFileAstIdKind::ExternBlock as u32)
            {
                // See the comment on `ErasedAssocItemFileAstId` for why is this.
                // FIXME: Technically there could be an extern block inside another item, e.g.:
                // ```
                // fn foo() {
                //     extern "C" {
                //         fn bar();
                //     }
                // }
                // ```
                // Here we want to make `foo()` the parent of `bar()`, but we make it `None`.
                // Shouldn't be a big deal though.
                parent = None;
            }
            parent
        }
    }

    /// The root node.
    pub fn root(&self) -> SyntaxNodePtr {
        self.arena[Idx::from_raw(RawIdx::from_u32(0))].0
    }

    pub fn ast_id<N: AstIdNode>(&self, item: &N) -> FileAstId<N> {
        self.ast_id_for_ptr(AstPtr::new(item))
    }

    /// Blocks may not be allocated (if they have no items), so they have a different API.
    pub fn ast_id_for_block(&self, block: &ast::BlockExpr) -> Option<FileAstId<ast::BlockExpr>> {
        self.ast_id_for_ptr_for_block(AstPtr::new(block))
    }

    pub fn ast_id_for_ptr<N: AstIdNode>(&self, ptr: AstPtr<N>) -> FileAstId<N> {
        let ptr = ptr.syntax_node_ptr();
        FileAstId { raw: self.erased_ast_id(ptr), _marker: PhantomData }
    }

    pub fn erased_ast_id_for_ptr(&self, ptr: SyntaxNodePtr) -> ErasedFileAstId {
        self.erased_ast_id(ptr)
    }

    /// Blocks may not be allocated (if they have no items), so they have a different API.
    pub fn ast_id_for_ptr_for_block(
        &self,
        ptr: AstPtr<ast::BlockExpr>,
    ) -> Option<FileAstId<ast::BlockExpr>> {
        let ptr = ptr.syntax_node_ptr();
        self.try_erased_ast_id(ptr).map(|raw| FileAstId { raw, _marker: PhantomData })
    }

    fn erased_ast_id(&self, ptr: SyntaxNodePtr) -> ErasedFileAstId {
        self.try_erased_ast_id(ptr).unwrap_or_else(|| {
            panic!(
                "Can't find SyntaxNodePtr {:?} in AstIdMap:\n{:?}",
                ptr,
                self.arena.iter().map(|(_id, i)| i).collect::<Vec<_>>(),
            )
        })
    }

    fn try_erased_ast_id(&self, ptr: SyntaxNodePtr) -> Option<ErasedFileAstId> {
        let hash = hash_ptr(&ptr);
        let idx = *self.ptr_map.find(hash, |&idx| self.arena[idx].0 == ptr)?;
        Some(self.arena[idx].1)
    }

    // Don't bound on `AstIdNode` here, because `BlockExpr`s are also valid here (`ast::BlockExpr`
    // doesn't always have a matching `FileAstId`, but a `FileAstId<ast::BlockExpr>` always has
    // a matching node).
    pub fn get<N: AstNode>(&self, id: FileAstId<N>) -> AstPtr<N> {
        let ptr = self.get_erased(id.raw);
        AstPtr::try_from_raw(ptr)
            .unwrap_or_else(|| panic!("AstIdMap node mismatch with node `{ptr:?}`"))
    }

    pub fn get_erased(&self, id: ErasedFileAstId) -> SyntaxNodePtr {
        let hash = hash_ast_id(&id);
        match self.id_map.find(hash, |&idx| self.arena[idx].1 == id) {
            Some(&idx) => self.arena[idx].0,
            None => panic!(
                "Can't find ast id {:?} in AstIdMap:\n{:?}",
                id,
                self.arena.iter().map(|(_id, i)| i).collect::<Vec<_>>(),
            ),
        }
    }
}

#[cfg(not(no_salsa_async_drops))]
impl Drop for AstIdMap {
    fn drop(&mut self) {
        let arena = std::mem::take(&mut self.arena);
        let ptr_map = std::mem::take(&mut self.ptr_map);
        let id_map = std::mem::take(&mut self.id_map);
        static AST_ID_MAP_DROP_THREAD: std::sync::OnceLock<
            std::sync::mpsc::Sender<(
                Arena<(SyntaxNodePtr, ErasedFileAstId)>,
                hashbrown::HashTable<ArenaId>,
                hashbrown::HashTable<ArenaId>,
            )>,
        > = std::sync::OnceLock::new();
        AST_ID_MAP_DROP_THREAD
            .get_or_init(|| {
                let (sender, receiver) = std::sync::mpsc::channel::<(
                    Arena<(SyntaxNodePtr, ErasedFileAstId)>,
                    hashbrown::HashTable<ArenaId>,
                    hashbrown::HashTable<ArenaId>,
                )>();
                std::thread::Builder::new()
                    .name("AstIdMapDropper".to_owned())
                    .spawn(move || {
                        loop {
                            // block on a receive
                            _ = receiver.recv();
                            // then drain the entire channel
                            while receiver.try_recv().is_ok() {}
                            // and sleep for a bit
                            std::thread::sleep(std::time::Duration::from_millis(100));
                        }
                        // why do this over just a `receiver.iter().for_each(drop)`? To reduce contention on the channel lock.
                        // otherwise this thread will constantly wake up and sleep again.
                    })
                    .unwrap();
                sender
            })
            .send((arena, ptr_map, id_map))
            .unwrap();
    }
}

#[inline]
fn hash_ptr(ptr: &SyntaxNodePtr) -> u64 {
    FxBuildHasher.hash_one(ptr)
}

#[inline]
fn hash_ast_id(ptr: &ErasedFileAstId) -> u64 {
    FxBuildHasher.hash_one(ptr)
}

#[cfg(test)]
mod tests {
    use syntax::{
        AstNode, Edition, GreenNode, SourceFile, SyntaxKind, SyntaxNodePtr, WalkEvent, ast,
    };

    use super::{
        AstIdMap, ErasedAstIdNextIndexMap, ErasedFileAstIdKind, ImplFileAstId, impl_ast_id,
        macro_call_name,
    };

    #[test]
    fn check_all_nodes() {
        let syntax = SourceFile::parse(
            r#"
extern crate foo;
fn foo() {
    union U {}
}
struct S;
macro_rules! m {}
macro m2() {}
trait Trait {}
impl Trait for S {}
impl S {}
impl m!() {}
impl m2!() for m!() {}
type T = i32;
enum E {
    V1(),
    V2 {},
    V3,
}
struct S; // duplicate
extern "C" {
    static S: i32;
}
static mut S: i32 = 0;
const FOO: i32 = 0;
        "#,
            Edition::CURRENT,
        )
        .syntax_node();
        let ast_id_map = AstIdMap::from_source(&syntax);
        for node in syntax.preorder() {
            let WalkEvent::Enter(node) = node else { continue };
            if !matches!(
                node.kind(),
                SyntaxKind::EXTERN_CRATE
                    | SyntaxKind::FN
                    | SyntaxKind::UNION
                    | SyntaxKind::STRUCT
                    | SyntaxKind::MACRO_RULES
                    | SyntaxKind::MACRO_DEF
                    | SyntaxKind::MACRO_CALL
                    | SyntaxKind::TRAIT
                    | SyntaxKind::IMPL
                    | SyntaxKind::TYPE_ALIAS
                    | SyntaxKind::ENUM
                    | SyntaxKind::VARIANT
                    | SyntaxKind::EXTERN_BLOCK
                    | SyntaxKind::STATIC
                    | SyntaxKind::CONST
            ) {
                continue;
            }
            let ptr = SyntaxNodePtr::new(&node);
            let ast_id = ast_id_map.erased_ast_id(ptr);
            let turn_back = ast_id_map.get_erased(ast_id);
            assert_eq!(ptr, turn_back);
        }
    }

    #[test]
    fn different_names_get_different_hashes() {
        let syntax = SourceFile::parse(
            r#"
fn foo() {}
fn bar() {}
        "#,
            Edition::CURRENT,
        )
        .syntax_node();
        let ast_id_map = AstIdMap::from_source(&syntax);
        let fns = syntax.descendants().filter_map(ast::Fn::cast).collect::<Vec<_>>();
        let [foo_fn, bar_fn] = fns.as_slice() else {
            panic!("not exactly 2 functions");
        };
        let foo_fn_id = ast_id_map.ast_id(foo_fn);
        let bar_fn_id = ast_id_map.ast_id(bar_fn);
        assert_ne!(foo_fn_id.raw.hash_value(), bar_fn_id.raw.hash_value(), "hashes are equal");
    }

    #[test]
    fn different_parents_get_different_hashes() {
        let syntax = SourceFile::parse(
            r#"
fn foo() {
    m!();
}
fn bar() {
    m!();
}
        "#,
            Edition::CURRENT,
        )
        .syntax_node();
        let ast_id_map = AstIdMap::from_source(&syntax);
        let macro_calls = syntax.descendants().filter_map(ast::MacroCall::cast).collect::<Vec<_>>();
        let [macro_call_foo, macro_call_bar] = macro_calls.as_slice() else {
            panic!("not exactly 2 macro calls");
        };
        let macro_call_foo_id = ast_id_map.ast_id(macro_call_foo);
        let macro_call_bar_id = ast_id_map.ast_id(macro_call_bar);
        assert_ne!(
            macro_call_foo_id.raw.hash_value(),
            macro_call_bar_id.raw.hash_value(),
            "hashes are equal"
        );
    }

    #[test]
    fn green_identity_data_matches_typed_ast() {
        let syntax = SourceFile::parse(
            r#"
impl Trait for Type {}
impl qualified::Trait for qualified::Type {}
impl (Type,) {}
plain!();
qualified::nested!();
        "#,
            Edition::CURRENT,
        )
        .syntax_node();

        for impl_ in syntax.descendants().filter_map(ast::Impl::cast) {
            let green = GreenNode::from(impl_.syntax().green());
            let actual = impl_ast_id(&green, &mut ErasedAstIdNextIndexMap::default());
            let type_as_name = |ty: Option<ast::Type>| match ty? {
                ast::Type::PathType(path_ty) => {
                    Some(path_ty.path()?.segment()?.name_ref()?.text_non_mutable().to_owned())
                }
                _ => None,
            };
            let expected_self_ty = type_as_name(impl_.self_ty());
            let expected_trait = type_as_name(impl_.trait_());
            let expected = ErasedAstIdNextIndexMap::default().new_id(
                ErasedFileAstIdKind::Impl,
                ImplFileAstId {
                    self_ty_name: expected_self_ty.as_deref(),
                    trait_name: expected_trait.as_deref(),
                },
            );

            assert_eq!(actual, expected);
        }

        for call in syntax.descendants().filter_map(ast::MacroCall::cast) {
            let green = GreenNode::from(call.syntax().green());
            let expected = call
                .path()
                .and_then(|path| path.segment()?.name_ref())
                .map(|name| name.text_non_mutable().to_owned())
                .unwrap_or_default();

            assert_eq!(macro_call_name(&green), expected);
        }
    }

    #[test]
    fn blocks_with_no_items_have_no_id() {
        let syntax = SourceFile::parse(
            r#"
fn foo() {
    let foo = 1;
    bar(foo);
}
        "#,
            Edition::CURRENT,
        )
        .syntax_node();
        let ast_id_map = AstIdMap::from_source(&syntax);
        let block = syntax.descendants().find_map(ast::BlockExpr::cast).expect("no block");
        assert!(ast_id_map.ast_id_for_block(&block).is_none());
    }
}
