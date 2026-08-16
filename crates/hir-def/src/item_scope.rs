//! Describes items defined or visible (ie, imported) in a certain scope.
//! This is shared between modules and blocks.

use std::{fmt, num::NonZeroU32, sync::LazyLock};

use base_db::{Crate, SourceDatabase};
use either::Either;
use hir_expand::{AstId, MacroCallId, attrs::AttrId, name::Name};
use indexmap::map::Entry;
use itertools::Itertools;
use la_arena::Idx;
use rustc_hash::{FxHashMap, FxHashSet};
use salsa::plumbing::{AsId, FromId};
use smallvec::SmallVec;
use span::Edition;
use stdx::{format_to, impl_from};
use syntax::ast;
use thin_vec::ThinVec;

use crate::{
    AdtId, BuiltinDeriveImplId, BuiltinType, ConstId, ExternBlockId, ExternCrateId, FxIndexMap,
    HasModule, ImplId, Lookup, MacroCallStyles, MacroId, ModuleDefId, ModuleId, TraitId, UseId,
    per_ns::{Item, MacrosItem, PerNs, TypesItem, ValuesItem},
    visibility::Visibility,
};

#[derive(Debug, Default)]
pub struct PerNsGlobImports {
    types: FxHashSet<(ModuleId, Name)>,
    values: FxHashSet<(ModuleId, Name)>,
    macros: FxHashSet<(ModuleId, Name)>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ImportOrExternCrate {
    Glob(GlobId),
    Import(ImportId),
    ExternCrate(ExternCrateId),
}

impl_from!(ImportOrGlob { Glob, Import } for ImportOrExternCrate);

impl ImportOrExternCrate {
    pub fn import_or_glob(self) -> Option<ImportOrGlob> {
        match self {
            ImportOrExternCrate::Import(it) => Some(ImportOrGlob::Import(it)),
            ImportOrExternCrate::Glob(it) => Some(ImportOrGlob::Glob(it)),
            _ => None,
        }
    }

    pub fn import(self) -> Option<ImportId> {
        match self {
            ImportOrExternCrate::Import(it) => Some(it),
            _ => None,
        }
    }

    pub fn glob(self) -> Option<GlobId> {
        match self {
            ImportOrExternCrate::Glob(id) => Some(id),
            _ => None,
        }
    }

    pub fn use_(self) -> Option<UseId> {
        match self {
            ImportOrExternCrate::Glob(id) => Some(id.use_),
            ImportOrExternCrate::Import(id) => Some(id.use_),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ImportOrGlob {
    Glob(GlobId),
    Import(ImportId),
}

impl ImportOrGlob {
    pub fn into_import(self) -> Option<ImportId> {
        match self {
            ImportOrGlob::Import(it) => Some(it),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ImportOrDef {
    Import(ImportId),
    Glob(GlobId),
    ExternCrate(ExternCrateId),
    Def(ModuleDefId),
}

impl_from!(ImportOrExternCrate { Import, Glob, ExternCrate } for ImportOrDef);
impl_from!(ImportOrGlob { Import, Glob } for ImportOrDef);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ImportId {
    pub use_: UseId,
    pub idx: Idx<ast::UseTree>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct GlobId {
    pub use_: UseId,
    pub idx: Idx<ast::UseTree>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeValuesItem {
    def: ModuleDefId,
    vis: ScopeVisibility,
    import: ScopeImportId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeVisibility(u32);

impl ScopeVisibility {
    const PUBLIC: Self = Self(u32::MAX);

    fn new(visibility: Visibility, visibilities: &mut ThinVec<Visibility>) -> Self {
        if visibility == Visibility::Public {
            return Self::PUBLIC;
        }
        let index =
            visibilities.iter().position(|&stored| stored == visibility).unwrap_or_else(|| {
                visibilities.push(visibility);
                visibilities.len() - 1
            });
        Self(u32::try_from(index).expect("ItemScope has more than u32::MAX visibilities"))
    }

    fn get(self, visibilities: &[Visibility]) -> Visibility {
        if self == Self::PUBLIC { Visibility::Public } else { visibilities[self.0 as usize] }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeImportOrExternCrateKind {
    Import,
    Glob,
    ExternCrate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeImportOrExternCrate {
    id: NonZeroU32,
    use_tree: u32,
    kind: ScopeImportOrExternCrateKind,
}

impl From<ImportOrExternCrate> for ScopeImportOrExternCrate {
    fn from(import: ImportOrExternCrate) -> Self {
        let (id, use_tree, kind) = match import {
            ImportOrExternCrate::Import(import) => (
                import.use_.as_id(),
                u32::from(import.idx.into_raw()),
                ScopeImportOrExternCrateKind::Import,
            ),
            ImportOrExternCrate::Glob(glob) => (
                glob.use_.as_id(),
                u32::from(glob.idx.into_raw()),
                ScopeImportOrExternCrateKind::Glob,
            ),
            ImportOrExternCrate::ExternCrate(extern_crate) => {
                (extern_crate.as_id(), 0, ScopeImportOrExternCrateKind::ExternCrate)
            }
        };
        assert_eq!(id.generation(), 0, "interned provenance ID unexpectedly has a generation");
        let id = NonZeroU32::new(id.index() + 1).unwrap();
        Self { id, use_tree, kind }
    }
}

impl From<ScopeImportOrExternCrate> for ImportOrExternCrate {
    fn from(import: ScopeImportOrExternCrate) -> Self {
        let id = salsa::Id::from_bits(u64::from(import.id.get()));
        match import.kind {
            ScopeImportOrExternCrateKind::Import => ImportOrExternCrate::Import(ImportId {
                use_: UseId::from_id(id),
                idx: Idx::from_raw(import.use_tree.into()),
            }),
            ScopeImportOrExternCrateKind::Glob => ImportOrExternCrate::Glob(GlobId {
                use_: UseId::from_id(id),
                idx: Idx::from_raw(import.use_tree.into()),
            }),
            ScopeImportOrExternCrateKind::ExternCrate => {
                ImportOrExternCrate::ExternCrate(ExternCrateId::from_id(id))
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeImportId(Option<NonZeroU32>);

impl ScopeImportId {
    const NONE: Self = Self(None);

    fn new(
        import: Option<ImportOrExternCrate>,
        imports: &mut ThinVec<ScopeImportOrExternCrate>,
    ) -> Self {
        let Some(import) = import.map(ScopeImportOrExternCrate::from) else {
            return Self::NONE;
        };
        let index = imports.iter().position(|&stored| stored == import).unwrap_or_else(|| {
            imports.push(import);
            imports.len() - 1
        });
        let index = u32::try_from(index + 1).expect("ItemScope has more than u32::MAX imports");
        Self(NonZeroU32::new(index))
    }

    fn get(self, imports: &[ScopeImportOrExternCrate]) -> Option<ImportOrExternCrate> {
        let index = self.0?.get() - 1;
        Some(imports[index as usize].into())
    }

    fn is_none(self) -> bool {
        self == Self::NONE
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeTypesItem {
    def: ModuleDefId,
    vis: ScopeVisibility,
    import: ScopeImportId,
}

impl ScopeValuesItem {
    fn new(
        item: ValuesItem,
        vis: ScopeVisibility,
        imports: &mut ThinVec<ScopeImportOrExternCrate>,
    ) -> Self {
        let import = ScopeImportId::new(item.import.map(Into::into), imports);
        Self { def: item.def, vis, import }
    }

    fn get(self, visibilities: &[Visibility], imports: &[ScopeImportOrExternCrate]) -> ValuesItem {
        ValuesItem {
            def: self.def,
            vis: self.vis.get(visibilities),
            import: self.import.get(imports).map(|import| {
                import.import_or_glob().expect("value namespace contains an extern-crate import")
            }),
        }
    }
}

impl ScopeTypesItem {
    fn new(
        item: TypesItem,
        vis: ScopeVisibility,
        imports: &mut ThinVec<ScopeImportOrExternCrate>,
    ) -> Self {
        let import = ScopeImportId::new(item.import, imports);
        Self { def: item.def, vis, import }
    }

    fn get(self, visibilities: &[Visibility], imports: &[ScopeImportOrExternCrate]) -> TypesItem {
        TypesItem {
            def: self.def,
            vis: self.vis.get(visibilities),
            import: self.import.get(imports),
        }
    }
}

const _: () = assert!(std::mem::size_of::<ScopeVisibility>() == 4);
const _: () = assert!(std::mem::size_of::<ScopeImportId>() == 4);
const _: () = assert!(std::mem::size_of::<ScopeValuesItem>() == 24);
const _: () = assert!(std::mem::size_of::<ScopeImportOrExternCrate>() == 12);
const _: () = assert!(std::mem::size_of::<ScopeTypesItem>() == 24);

impl PerNsGlobImports {
    pub(crate) fn contains_type(&self, module_id: ModuleId, name: Name) -> bool {
        self.types.contains(&(module_id, name))
    }
    pub(crate) fn contains_value(&self, module_id: ModuleId, name: Name) -> bool {
        self.values.contains(&(module_id, name))
    }
    pub(crate) fn contains_macro(&self, module_id: ModuleId, name: Name) -> bool {
        self.macros.contains(&(module_id, name))
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct ItemScope {
    /// Defs visible in this scope. This includes `declarations`, but also
    /// imports. The imports belong to this module and can be resolved by using them on
    /// the `use_imports_*` fields.
    types: FxIndexMap<Name, ScopeTypesItem>,
    values: FxIndexMap<Name, ScopeValuesItem>,
    macros: FxIndexMap<Name, MacrosItem>,
    /// Deduplicated visibilities referenced by type and value entries.
    visibilities: ThinVec<Visibility>,
    /// Deduplicated import provenance referenced by type and value entries.
    imports: ThinVec<ScopeImportOrExternCrate>,
    unresolved: FxHashSet<Name>,

    /// The defs declared in this scope. Each def has a single scope where it is
    /// declared.
    declarations: ThinVec<ModuleDefId>,

    impls: ThinVec<(ImplId, /* trait impl */ bool)>,
    builtin_derive_impls: ThinVec<BuiltinDeriveImplId>,
    extern_blocks: ThinVec<ExternBlockId>,
    unnamed_consts: ThinVec<ConstId>,
    /// Traits imported via `use Trait as _;`.
    unnamed_trait_imports: ThinVec<(TraitId, Item<()>)>,

    // the resolutions of the imports of this scope
    use_imports_types: FxHashMap<ImportOrExternCrate, ImportOrDef>,
    use_imports_values: FxHashMap<ImportOrGlob, ImportOrDef>,
    use_imports_macros: FxHashMap<ImportOrExternCrate, ImportOrDef>,

    use_decls: ThinVec<UseId>,
    extern_crate_decls: ThinVec<ExternCrateId>,
    /// Macros visible in current module in legacy textual scope
    ///
    /// For macros invoked by an unqualified identifier like `bar!()`, `legacy_macros` will be searched in first.
    /// If it yields no result, then it turns to module scoped `macros`.
    /// It macros with name qualified with a path like `crate::foo::bar!()`, `legacy_macros` will be skipped,
    /// and only normal scoped `macros` will be searched in.
    ///
    /// Note that this automatically inherit macros defined textually before the definition of module itself.
    ///
    /// Module scoped macros will be inserted into `items` instead of here.
    // FIXME: Macro shadowing in one module is not properly handled. Non-item place macros will
    // be all resolved to the last one defined if shadowing happens.
    legacy_macros: FxHashMap<Name, SmallVec<[MacroId; 1]>>,
    /// The attribute macro invocations in this scope.
    attr_macros: FxHashMap<AstId<ast::Item>, MacroCallId>,
    /// The macro invocations in this scope.
    macro_invocations: FxHashMap<AstId<ast::MacroCall>, MacroCallId>,
    /// The derive macro invocations in this scope, keyed by the owner item over the actual derive attributes
    /// paired with the derive macro invocations for the specific attribute.
    derive_macros: FxHashMap<AstId<ast::Adt>, SmallVec<[DeriveMacroInvocation; 1]>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::visibility::VisibilityExplicitness;

    #[test]
    fn values_scope_entry_is_compact() {
        assert_eq!(std::mem::size_of::<ScopeValuesItem>(), 24);
    }

    #[test]
    fn type_scope_entry_is_compact() {
        assert_eq!(std::mem::size_of::<ScopeTypesItem>(), 24);
    }

    #[test]
    fn scope_visibilities_roundtrip_and_deduplicate() {
        let krate = Crate::from_id(salsa::Id::from_bits(1));
        let module = ModuleId::from_id(salsa::Id::from_bits(2));
        let visibilities = [
            Visibility::Public,
            Visibility::PubCrate(krate),
            Visibility::Module(module, VisibilityExplicitness::Implicit),
            Visibility::Module(module, VisibilityExplicitness::Explicit),
        ];
        let mut stored = ThinVec::new();

        for visibility in visibilities {
            let first = ScopeVisibility::new(visibility, &mut stored);
            let second = ScopeVisibility::new(visibility, &mut stored);
            assert_eq!(first, second);
            assert_eq!(first.get(&stored), visibility);
        }
        assert_eq!(stored.len(), 3, "public visibility should not need an arena entry");
    }

    #[test]
    fn shrinking_scope_normalizes_visibility_storage() {
        let krate = Crate::from_id(salsa::Id::from_bits(1));
        let module = ModuleId::from_id(salsa::Id::from_bits(2));
        let type_vis = Visibility::PubCrate(krate);
        let value_vis = Visibility::Module(module, VisibilityExplicitness::Explicit);
        let type_import = ImportOrExternCrate::Glob(GlobId {
            use_: UseId::from_id(salsa::Id::from_bits(3)),
            idx: Idx::from_raw(4.into()),
        });
        let value_import = ImportOrGlob::Import(ImportId {
            use_: UseId::from_id(salsa::Id::from_bits(5)),
            idx: Idx::from_raw(6.into()),
        });
        let mut first = ItemScope::default();
        let mut second = ItemScope::default();

        for (scope, reverse_intern_order) in [(&mut first, false), (&mut second, true)] {
            if reverse_intern_order {
                scope.intern_visibility(value_vis);
                ScopeImportId::new(Some(value_import.into()), &mut scope.imports);
            }
            let type_id = scope.intern_visibility(type_vis);
            let value_id = scope.intern_visibility(value_vis);
            let def = ModuleDefId::ModuleId(module);
            scope.types.insert(
                Name::missing(),
                ScopeTypesItem::new(
                    TypesItem { def, vis: type_vis, import: Some(type_import) },
                    type_id,
                    &mut scope.imports,
                ),
            );
            scope.values.insert(
                Name::missing(),
                ScopeValuesItem::new(
                    ValuesItem { def, vis: value_vis, import: Some(value_import) },
                    value_id,
                    &mut scope.imports,
                ),
            );
        }

        first.shrink_to_fit();
        second.shrink_to_fit();
        assert_eq!(first, second);
    }

    #[test]
    fn scope_imports_roundtrip_and_deduplicate() {
        let imports = [
            ImportOrExternCrate::Import(ImportId {
                use_: UseId::from_id(salsa::Id::from_bits(1)),
                idx: Idx::from_raw(2.into()),
            }),
            ImportOrExternCrate::Glob(GlobId {
                use_: UseId::from_id(salsa::Id::from_bits(3)),
                idx: Idx::from_raw(4.into()),
            }),
            ImportOrExternCrate::ExternCrate(ExternCrateId::from_id(salsa::Id::from_bits(5))),
        ];
        let mut stored = ThinVec::new();

        assert_eq!(ScopeImportId::NONE.get(&stored), None);
        for import in imports {
            let first = ScopeImportId::new(Some(import), &mut stored);
            let second = ScopeImportId::new(Some(import), &mut stored);
            assert_eq!(first, second);
            assert_eq!(first.get(&stored), Some(import));
        }
        assert_eq!(stored.len(), imports.len());

        let shared = ImportId {
            use_: UseId::from_id(salsa::Id::from_bits(7)),
            idx: Idx::from_raw(8.into()),
        };
        let def = ModuleDefId::ModuleId(ModuleId::from_id(salsa::Id::from_bits(9)));
        let type_item = TypesItem {
            def,
            vis: Visibility::Public,
            import: Some(ImportOrExternCrate::Import(shared)),
        };
        let value_item =
            ValuesItem { def, vis: Visibility::Public, import: Some(ImportOrGlob::Import(shared)) };
        let compact_type = ScopeTypesItem::new(type_item, ScopeVisibility::PUBLIC, &mut stored);
        let compact_value = ScopeValuesItem::new(value_item, ScopeVisibility::PUBLIC, &mut stored);

        assert_eq!(stored.len(), imports.len() + 1);
        assert_eq!(compact_type.get(&[], &stored), type_item);
        assert_eq!(compact_value.get(&[], &stored), value_item);
    }
}

#[derive(Debug, PartialEq, Eq)]
struct DeriveMacroInvocation {
    attr_id: AttrId,
    /// The `#[derive]` call
    attr_call_id: MacroCallId,
    derive_call_ids: SmallVec<[Option<Either<MacroCallId, BuiltinDeriveImplId>>; 4]>,
}

pub(crate) static BUILTIN_SCOPE: LazyLock<FxIndexMap<Name, PerNs>> = LazyLock::new(|| {
    BuiltinType::all_builtin_types()
        .iter()
        .map(|(name, ty)| (name.clone(), PerNs::types((*ty).into(), Visibility::Public, None)))
        .collect()
});

/// Shadow mode for builtin type which can be shadowed by module.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum BuiltinShadowMode {
    /// Prefer user-defined modules (or other types) over builtins.
    Module,
    /// Prefer builtins over user-defined modules (but not other types).
    Other,
}

/// Legacy macros can only be accessed through special methods like `get_legacy_macros`.
/// Other methods will only resolve values, types and module scoped macros only.
impl ItemScope {
    fn intern_visibility(&mut self, visibility: Visibility) -> ScopeVisibility {
        ScopeVisibility::new(visibility, &mut self.visibilities)
    }

    pub fn entries(&self) -> impl Iterator<Item = (&Name, PerNs)> + '_ {
        // FIXME: shadowing
        self.types
            .keys()
            .chain(self.values.keys())
            .chain(self.macros.keys())
            .chain(self.unresolved.iter())
            .sorted()
            .dedup()
            .map(move |name| (name, self.get(name)))
    }

    pub fn values(&self) -> impl Iterator<Item = (&Name, Item<ModuleDefId, ImportOrGlob>)> + '_ {
        self.values.iter().map(|(name, &item)| (name, item.get(&self.visibilities, &self.imports)))
    }

    pub fn types(
        &self,
    ) -> impl Iterator<Item = (&Name, Item<ModuleDefId, ImportOrExternCrate>)> + '_ {
        self.types.iter().map(|(name, &item)| (name, item.get(&self.visibilities, &self.imports)))
    }

    pub fn macros(&self) -> impl Iterator<Item = (&Name, Item<MacroId, ImportOrExternCrate>)> + '_ {
        self.macros.iter().map(|(n, &i)| (n, i))
    }

    pub fn imports(&self) -> impl Iterator<Item = ImportId> + '_ {
        self.use_imports_types
            .keys()
            .copied()
            .chain(self.use_imports_macros.keys().copied())
            .filter_map(ImportOrExternCrate::import_or_glob)
            .chain(self.use_imports_values.keys().copied())
            .filter_map(ImportOrGlob::into_import)
            .sorted()
            .dedup()
    }

    pub fn fully_resolve_import(&self, db: &dyn SourceDatabase, mut import: ImportId) -> PerNs {
        let mut res = PerNs::none();

        let mut scope = self;
        while let Some(&m) = scope.use_imports_macros.get(&ImportOrExternCrate::Import(import)) {
            match m {
                ImportOrDef::Import(i) => {
                    let module_id = i.use_.lookup(db).container;
                    scope = &module_id.def_map(db)[module_id].scope;
                    import = i;
                }
                ImportOrDef::Def(ModuleDefId::MacroId(def)) => {
                    res.macros = Some(Item { def, vis: Visibility::Public, import: None });
                    break;
                }
                _ => break,
            }
        }
        let mut scope = self;
        while let Some(&m) = scope.use_imports_types.get(&ImportOrExternCrate::Import(import)) {
            match m {
                ImportOrDef::Import(i) => {
                    let module_id = i.use_.lookup(db).container;
                    scope = &module_id.def_map(db)[module_id].scope;
                    import = i;
                }
                ImportOrDef::Def(def) => {
                    res.types = Some(Item { def, vis: Visibility::Public, import: None });
                    break;
                }
                _ => break,
            }
        }
        let mut scope = self;
        while let Some(&m) = scope.use_imports_values.get(&ImportOrGlob::Import(import)) {
            match m {
                ImportOrDef::Import(i) => {
                    let module_id = i.use_.lookup(db).container;
                    scope = &module_id.def_map(db)[module_id].scope;
                    import = i;
                }
                ImportOrDef::Def(def) => {
                    res.values = Some(Item { def, vis: Visibility::Public, import: None });
                    break;
                }
                _ => break,
            }
        }
        res
    }

    pub fn declarations(&self) -> impl Iterator<Item = ModuleDefId> + '_ {
        self.declarations.iter().copied()
    }

    pub fn extern_crate_decls(&self) -> impl ExactSizeIterator<Item = ExternCrateId> + '_ {
        self.extern_crate_decls.iter().copied()
    }

    pub fn extern_blocks(&self) -> impl Iterator<Item = ExternBlockId> + '_ {
        self.extern_blocks.iter().copied()
    }

    pub fn use_decls(&self) -> impl ExactSizeIterator<Item = UseId> + '_ {
        self.use_decls.iter().copied()
    }

    pub fn impls(&self) -> impl ExactSizeIterator<Item = ImplId> + '_ {
        self.impls.iter().map(|&(id, _)| id)
    }

    pub fn trait_impls(&self) -> impl Iterator<Item = ImplId> + '_ {
        self.impls.iter().filter(|&&(_, is_trait_impl)| is_trait_impl).map(|&(id, _)| id)
    }

    pub fn inherent_impls(&self) -> impl Iterator<Item = ImplId> + '_ {
        self.impls.iter().filter(|&&(_, is_trait_impl)| !is_trait_impl).map(|&(id, _)| id)
    }

    pub fn builtin_derive_impls(&self) -> impl ExactSizeIterator<Item = BuiltinDeriveImplId> + '_ {
        self.builtin_derive_impls.iter().copied()
    }

    pub fn all_macro_calls(&self) -> impl Iterator<Item = MacroCallId> + '_ {
        self.macro_invocations.values().copied().chain(self.attr_macros.values().copied()).chain(
            self.derive_macros.values().flat_map(|it| {
                it.iter().flat_map(|it| {
                    it.derive_call_ids.iter().copied().flatten().flat_map(|it| it.left())
                })
            }),
        )
    }

    pub(crate) fn modules_in_scope(&self) -> impl Iterator<Item = (ModuleId, Visibility)> + '_ {
        self.types.values().filter_map(|ns| match ns.def {
            ModuleDefId::ModuleId(module) => Some((module, ns.vis.get(&self.visibilities))),
            _ => None,
        })
    }

    pub fn unnamed_consts(&self) -> impl Iterator<Item = ConstId> + '_ {
        self.unnamed_consts.iter().copied()
    }

    /// Iterate over all legacy textual scoped macros visible at the end of the module
    pub fn legacy_macros(&self) -> impl Iterator<Item = (&Name, &[MacroId])> + '_ {
        self.legacy_macros.iter().map(|(name, def)| (name, &**def))
    }

    /// Get a name from current module scope, legacy macros are not included
    pub fn get(&self, name: &Name) -> PerNs {
        PerNs {
            types: self
                .types
                .get(name)
                .copied()
                .map(|item| item.get(&self.visibilities, &self.imports)),
            values: self
                .values
                .get(name)
                .copied()
                .map(|item| item.get(&self.visibilities, &self.imports)),
            macros: self.macros.get(name).copied(),
        }
    }

    pub(crate) fn type_(&self, name: &Name) -> Option<(ModuleDefId, Visibility)> {
        self.types.get(name).map(|item| (item.def, item.vis.get(&self.visibilities)))
    }

    pub(crate) fn makro(&self, name: &Name) -> Option<MacroId> {
        self.macros.get(name).map(|item| item.def)
    }

    /// XXX: this is O(N) rather than O(1), try to not introduce new usages.
    pub(crate) fn name_of(&self, item: ItemInNs) -> Option<(&Name, Visibility, /*declared*/ bool)> {
        match item {
            ItemInNs::Macros(def) => self.macros.iter().find_map(|(name, other_def)| {
                (other_def.def == def).then_some((name, other_def.vis, other_def.import.is_none()))
            }),
            ItemInNs::Types(def) => self.types.iter().find_map(|(name, other_def)| {
                (other_def.def == def).then_some((
                    name,
                    other_def.vis.get(&self.visibilities),
                    other_def.import.is_none(),
                ))
            }),
            ItemInNs::Values(def) => self.values.iter().find_map(|(name, other_def)| {
                (other_def.def == def).then_some((
                    name,
                    other_def.vis.get(&self.visibilities),
                    other_def.import.is_none(),
                ))
            }),
        }
    }

    /// XXX: this is O(N) rather than O(1), try to not introduce new usages.
    pub(crate) fn names_of<T>(
        &self,
        item: ItemInNs,
        mut cb: impl FnMut(&Name, Visibility, /*declared*/ bool) -> Option<T>,
    ) -> Option<T> {
        match item {
            ItemInNs::Macros(def) => self
                .macros
                .iter()
                .filter_map(|(name, other_def)| {
                    (other_def.def == def).then_some((
                        name,
                        other_def.vis,
                        other_def.import.is_none(),
                    ))
                })
                .find_map(|(a, b, c)| cb(a, b, c)),
            ItemInNs::Types(def) => self
                .types
                .iter()
                .filter_map(|(name, other_def)| {
                    (other_def.def == def).then_some((
                        name,
                        other_def.vis.get(&self.visibilities),
                        other_def.import.is_none(),
                    ))
                })
                .find_map(|(a, b, c)| cb(a, b, c)),
            ItemInNs::Values(def) => self
                .values
                .iter()
                .filter_map(|(name, other_def)| {
                    (other_def.def == def).then_some((
                        name,
                        other_def.vis.get(&self.visibilities),
                        other_def.import.is_none(),
                    ))
                })
                .find_map(|(a, b, c)| cb(a, b, c)),
        }
    }

    pub(crate) fn traits(&self) -> impl Iterator<Item = TraitId> + '_ {
        self.types
            .values()
            .filter_map(|def| match def.def {
                ModuleDefId::TraitId(t) => Some(t),
                _ => None,
            })
            .chain(self.unnamed_trait_imports.iter().map(|&(t, _)| t))
    }

    pub(crate) fn resolutions(&self) -> impl Iterator<Item = (Option<Name>, PerNs)> + '_ {
        self.entries().map(|(name, res)| (Some(name.clone()), res)).chain(
            self.unnamed_trait_imports.iter().map(|(tr, trait_)| {
                (
                    None,
                    PerNs::types(
                        ModuleDefId::TraitId(*tr),
                        trait_.vis,
                        trait_.import.map(ImportOrExternCrate::Import),
                    ),
                )
            }),
        )
    }

    pub fn macro_invoc(&self, call: AstId<ast::MacroCall>) -> Option<MacroCallId> {
        self.macro_invocations.get(&call).copied()
    }

    pub fn iter_macro_invoc(&self) -> impl Iterator<Item = (&AstId<ast::MacroCall>, &MacroCallId)> {
        self.macro_invocations.iter()
    }
}

impl ItemScope {
    pub(crate) fn declare(&mut self, def: ModuleDefId) {
        self.declarations.push(def)
    }

    pub(crate) fn remove_from_value_ns(&mut self, name: &Name, def: ModuleDefId) {
        // predicate needed since a different item with the same name may be registered instead,
        // leading to `shift_remove` removing the wrong item.
        if self.values.get(name).is_some_and(|entry| entry.def == def) {
            let _ = self.values.shift_remove(name);
        }
    }

    pub(crate) fn get_legacy_macro(&self, name: &Name) -> Option<&[MacroId]> {
        self.legacy_macros.get(name).map(|it| &**it)
    }

    pub(crate) fn define_impl(&mut self, imp: ImplId, is_trait_impl: bool) {
        self.impls.push((imp, is_trait_impl));
    }

    pub(crate) fn define_builtin_derive_impl(&mut self, imp: BuiltinDeriveImplId) {
        self.builtin_derive_impls.push(imp);
    }

    pub(crate) fn define_extern_block(&mut self, extern_block: ExternBlockId) {
        self.extern_blocks.push(extern_block);
    }

    pub(crate) fn define_extern_crate_decl(&mut self, extern_crate: ExternCrateId) {
        self.extern_crate_decls.push(extern_crate);
    }

    pub(crate) fn define_unnamed_const(&mut self, konst: ConstId) {
        self.unnamed_consts.push(konst);
    }

    pub(crate) fn define_legacy_macro(&mut self, name: Name, mac: MacroId) {
        self.legacy_macros.entry(name).or_default().push(mac);
    }

    pub(crate) fn add_attr_macro_invoc(&mut self, item: AstId<ast::Item>, call: MacroCallId) {
        self.attr_macros.insert(item, call);
    }

    pub(crate) fn add_macro_invoc(&mut self, call: AstId<ast::MacroCall>, call_id: MacroCallId) {
        self.macro_invocations.insert(call, call_id);
    }

    pub fn attr_macro_invocs(&self) -> impl Iterator<Item = (AstId<ast::Item>, MacroCallId)> + '_ {
        self.attr_macros.iter().map(|(k, v)| (*k, *v))
    }

    pub(crate) fn set_derive_macro_invoc(
        &mut self,
        adt: AstId<ast::Adt>,
        call: Either<MacroCallId, BuiltinDeriveImplId>,
        id: AttrId,
        idx: usize,
    ) {
        if let Some(derives) = self.derive_macros.get_mut(&adt)
            && let Some(DeriveMacroInvocation { derive_call_ids, .. }) =
                derives.iter_mut().find(|&&mut DeriveMacroInvocation { attr_id, .. }| id == attr_id)
        {
            derive_call_ids[idx] = Some(call);
        }
    }

    /// We are required to set this up front as derive invocation recording happens out of order
    /// due to the fixed pointer iteration loop being able to record some derives later than others
    /// independent of their indices.
    pub(crate) fn init_derive_attribute(
        &mut self,
        adt: AstId<ast::Adt>,
        attr_id: AttrId,
        attr_call_id: MacroCallId,
        mut derive_call_ids: SmallVec<[Option<Either<MacroCallId, BuiltinDeriveImplId>>; 4]>,
    ) {
        derive_call_ids.shrink_to_fit();
        self.derive_macros.entry(adt).or_default().push(DeriveMacroInvocation {
            attr_id,
            attr_call_id,
            derive_call_ids,
        });
    }

    pub fn derive_macro_invocs(
        &self,
    ) -> impl Iterator<
        Item = (
            AstId<ast::Adt>,
            impl Iterator<
                Item = (AttrId, MacroCallId, &[Option<Either<MacroCallId, BuiltinDeriveImplId>>]),
            >,
        ),
    > + '_ {
        self.derive_macros.iter().map(|(k, v)| {
            (
                *k,
                v.iter().map(|DeriveMacroInvocation { attr_id, attr_call_id, derive_call_ids }| {
                    (*attr_id, *attr_call_id, &**derive_call_ids)
                }),
            )
        })
    }

    pub fn derive_macro_invoc(
        &self,
        ast_id: AstId<ast::Adt>,
        attr_id: AttrId,
    ) -> Option<MacroCallId> {
        Some(self.derive_macros.get(&ast_id)?.iter().find(|it| it.attr_id == attr_id)?.attr_call_id)
    }

    // FIXME: This is only used in collection, we should move the relevant parts of it out of ItemScope
    pub(crate) fn unnamed_trait_vis(&self, tr: TraitId) -> Option<Visibility> {
        self.unnamed_trait_imports.iter().find(|&&(t, _)| t == tr).map(|(_, trait_)| trait_.vis)
    }

    pub(crate) fn push_unnamed_trait(
        &mut self,
        tr: TraitId,
        vis: Visibility,
        import: Option<ImportId>,
    ) {
        self.unnamed_trait_imports.push((tr, Item { def: (), vis, import }));
    }

    pub(crate) fn push_res_with_import(
        &mut self,
        glob_imports: &mut PerNsGlobImports,
        lookup: (ModuleId, Name),
        def: PerNs,
        import: Option<ImportOrExternCrate>,
    ) -> bool {
        let mut changed = false;

        // FIXME: Document and simplify this

        if let Some(mut fld) = def.types {
            let vis = self.intern_visibility(fld.vis);
            let visibilities = &self.visibilities;
            let imports = &mut self.imports;
            let existing = self.types.entry(lookup.1.clone());
            match existing {
                Entry::Vacant(entry) => {
                    match import {
                        Some(ImportOrExternCrate::Glob(_)) => {
                            glob_imports.types.insert(lookup.clone());
                        }
                        _ => _ = glob_imports.types.remove(&lookup),
                    }
                    let prev = std::mem::replace(&mut fld.import, import);
                    if let Some(import) = import {
                        self.use_imports_types
                            .insert(import, prev.map_or(ImportOrDef::Def(fld.def), Into::into));
                    }
                    entry.insert(ScopeTypesItem::new(fld, vis, imports));
                    changed = true;
                }
                Entry::Occupied(mut entry) => {
                    match import {
                        Some(ImportOrExternCrate::Glob(..)) => {
                            // Multiple globs may import the same item and they may
                            // override visibility from previously resolved globs. This is
                            // currently handled by `DefCollector`, because we need to
                            // compute the max visibility for items and we need `DefMap`
                            // for that.
                        }
                        _ => {
                            // A non-glob import either shadows a glob import of the same
                            // name, or re-resolves a stale binding it recorded earlier.
                            if glob_imports.types.remove(&lookup)
                                || entry
                                    .get()
                                    .get(visibilities, imports)
                                    .is_reresolved_by(&fld.def, import)
                            {
                                let prev = std::mem::replace(&mut fld.import, import);
                                if let Some(import) = import {
                                    self.use_imports_types.insert(
                                        import,
                                        prev.map_or(ImportOrDef::Def(fld.def), Into::into),
                                    );
                                }
                                cov_mark::hit!(import_shadowed);
                                entry.insert(ScopeTypesItem::new(fld, vis, imports));
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        if let Some(mut fld) = def.values {
            let vis = self.intern_visibility(fld.vis);
            let visibilities = &self.visibilities;
            let imports = &mut self.imports;
            let existing = self.values.entry(lookup.1.clone());
            match existing {
                Entry::Vacant(entry) => {
                    match import {
                        Some(ImportOrExternCrate::Glob(_)) => {
                            glob_imports.values.insert(lookup.clone());
                        }
                        _ => _ = glob_imports.values.remove(&lookup),
                    }
                    let import = import.and_then(ImportOrExternCrate::import_or_glob);
                    let prev = std::mem::replace(&mut fld.import, import);
                    if let Some(import) = import {
                        self.use_imports_values
                            .insert(import, prev.map_or(ImportOrDef::Def(fld.def), Into::into));
                    }
                    entry.insert(ScopeValuesItem::new(fld, vis, imports));
                    changed = true;
                }
                Entry::Occupied(mut entry)
                    if !matches!(import, Some(ImportOrExternCrate::Glob(..))) =>
                {
                    let import = import.and_then(ImportOrExternCrate::import_or_glob);
                    if glob_imports.values.remove(&lookup)
                        || entry.get().get(visibilities, imports).is_reresolved_by(&fld.def, import)
                    {
                        cov_mark::hit!(import_shadowed);

                        let prev = std::mem::replace(&mut fld.import, import);
                        if let Some(import) = import {
                            self.use_imports_values
                                .insert(import, prev.map_or(ImportOrDef::Def(fld.def), Into::into));
                        }
                        entry.insert(ScopeValuesItem::new(fld, vis, imports));
                        changed = true;
                    }
                }
                _ => {}
            }
        }

        if let Some(mut fld) = def.macros {
            let existing = self.macros.entry(lookup.1.clone());
            match existing {
                Entry::Vacant(entry) => {
                    match import {
                        Some(ImportOrExternCrate::Glob(_)) => {
                            glob_imports.macros.insert(lookup.clone());
                        }
                        _ => _ = glob_imports.macros.remove(&lookup),
                    }
                    let prev = std::mem::replace(&mut fld.import, import);
                    if let Some(import) = import {
                        self.use_imports_macros.insert(
                            import,
                            prev.map_or_else(|| ImportOrDef::Def(fld.def.into()), Into::into),
                        );
                    }
                    entry.insert(fld);
                    changed = true;
                }
                Entry::Occupied(mut entry)
                    if !matches!(import, Some(ImportOrExternCrate::Glob(..)))
                        && (glob_imports.macros.remove(&lookup)
                            || entry.get().is_reresolved_by(&fld.def, import)) =>
                {
                    cov_mark::hit!(import_shadowed);
                    let prev = std::mem::replace(&mut fld.import, import);
                    if let Some(import) = import {
                        self.use_imports_macros.insert(
                            import,
                            prev.map_or_else(|| ImportOrDef::Def(fld.def.into()), Into::into),
                        );
                    }
                    entry.insert(fld);
                    changed = true;
                }
                _ => {}
            }
        }

        if def.is_none() && self.unresolved.insert(lookup.1) {
            changed = true;
        }

        changed
    }

    /// Marks everything that is not a procedural macro as private to `this_module`.
    pub(crate) fn censor_non_proc_macros(&mut self, krate: Crate) {
        let visibility = Visibility::PubCrate(krate);
        let vis = self.intern_visibility(visibility);
        self.types.values_mut().for_each(|def| def.vis = vis);
        self.values.values_mut().for_each(|def| def.vis = vis);
        self.unnamed_trait_imports.iter_mut().for_each(|(_, def)| def.vis = visibility);

        for mac in self.macros.values_mut() {
            if matches!(mac.def, MacroId::ProcMacroId(_) if mac.import.is_none()) {
                continue;
            }
            mac.vis = Visibility::PubCrate(krate)
        }
    }

    pub(crate) fn dump(&self, db: &dyn SourceDatabase, buf: &mut String) {
        let mut entries: Vec<_> = self.resolutions().collect();
        entries.sort_by_key(|(name, _)| name.clone());

        let print_macro_sub_ns = |buf: &mut String, macro_id: MacroId| {
            let styles = crate::nameres::macro_styles_from_id(db, macro_id);
            if styles.contains(MacroCallStyles::FN_LIKE) {
                buf.push('!');
            }
            if styles.contains(MacroCallStyles::ATTR) || styles.contains(MacroCallStyles::DERIVE) {
                buf.push('#');
            }
        };

        for (name, def) in entries {
            let display_name: &dyn fmt::Display = match &name {
                Some(name) => &name.display(db, Edition::LATEST),
                None => &"_",
            };
            format_to!(buf, "- {display_name} :");

            if let Some(Item { import, .. }) = def.types {
                buf.push_str(" type");
                match import {
                    Some(ImportOrExternCrate::Import(_)) => buf.push_str(" (import)"),
                    Some(ImportOrExternCrate::Glob(_)) => buf.push_str(" (glob)"),
                    Some(ImportOrExternCrate::ExternCrate(_)) => buf.push_str(" (extern)"),
                    None => (),
                }
            }
            if let Some(Item { import, .. }) = def.values {
                buf.push_str(" value");
                match import {
                    Some(ImportOrGlob::Import(_)) => buf.push_str(" (import)"),
                    Some(ImportOrGlob::Glob(_)) => buf.push_str(" (glob)"),
                    None => (),
                }
            }
            if let Some(Item { def: macro_id, import, .. }) = def.macros {
                buf.push_str(" macro");
                print_macro_sub_ns(buf, macro_id);
                match import {
                    Some(ImportOrExternCrate::Import(_)) => buf.push_str(" (import)"),
                    Some(ImportOrExternCrate::Glob(_)) => buf.push_str(" (glob)"),
                    Some(ImportOrExternCrate::ExternCrate(_)) => buf.push_str(" (extern)"),
                    None => (),
                }
            }
            if def.is_none() {
                buf.push_str(" _");
            }

            buf.push('\n');
        }

        // Also dump legacy-textual-scope macros visible at the _end_ of the scope.
        //
        // For tests involving a cursor position, this might include macros that
        // are _not_ visible at the cursor position.
        let mut legacy_macros = self.legacy_macros().collect::<Vec<_>>();
        legacy_macros.sort_by(|(a, _), (b, _)| Ord::cmp(a, b));
        for (name, macros) in legacy_macros {
            format_to!(buf, "- (legacy) {} :", name.display(db, Edition::LATEST));
            for &macro_id in macros {
                buf.push_str(" macro");
                print_macro_sub_ns(buf, macro_id);
            }
            buf.push('\n');
        }
    }

    pub(crate) fn shrink_to_fit(&mut self) {
        let old_visibilities = std::mem::take(&mut self.visibilities);
        for item in self.types.values_mut() {
            item.vis =
                ScopeVisibility::new(item.vis.get(&old_visibilities), &mut self.visibilities);
        }
        for item in self.values.values_mut() {
            item.vis =
                ScopeVisibility::new(item.vis.get(&old_visibilities), &mut self.visibilities);
        }

        let old_imports = std::mem::take(&mut self.imports);
        for item in self.types.values_mut() {
            item.import = ScopeImportId::new(item.import.get(&old_imports), &mut self.imports);
        }
        for item in self.values.values_mut() {
            item.import = ScopeImportId::new(item.import.get(&old_imports), &mut self.imports);
        }

        // Exhaustive match to require handling new fields.
        let Self {
            types,
            values,
            macros,
            visibilities,
            imports,
            unresolved,
            declarations,
            impls,
            builtin_derive_impls,
            unnamed_consts,
            unnamed_trait_imports,
            legacy_macros,
            attr_macros,
            derive_macros,
            extern_crate_decls,
            use_decls,
            use_imports_values,
            use_imports_types,
            use_imports_macros,
            macro_invocations,
            extern_blocks,
        } = self;
        extern_blocks.shrink_to_fit();
        types.shrink_to_fit();
        values.shrink_to_fit();
        macros.shrink_to_fit();
        visibilities.shrink_to_fit();
        imports.shrink_to_fit();
        use_imports_types.shrink_to_fit();
        use_imports_values.shrink_to_fit();
        use_imports_macros.shrink_to_fit();
        unresolved.shrink_to_fit();
        declarations.shrink_to_fit();
        impls.shrink_to_fit();
        builtin_derive_impls.shrink_to_fit();
        unnamed_consts.shrink_to_fit();
        unnamed_trait_imports.shrink_to_fit();
        legacy_macros.shrink_to_fit();
        attr_macros.shrink_to_fit();
        derive_macros.shrink_to_fit();
        extern_crate_decls.shrink_to_fit();
        use_decls.shrink_to_fit();
        macro_invocations.shrink_to_fit();
    }
}

// These methods are a temporary measure only meant to be used by `DefCollector::push_res_and_update_glob_vis()`.
impl ItemScope {
    pub(crate) fn update_visibility_types(&mut self, name: &Name, vis: Visibility) {
        let vis = self.intern_visibility(vis);
        let res =
            self.types.get_mut(name).expect("tried to update visibility of non-existent type");
        res.vis = vis;
    }

    pub(crate) fn update_visibility_values(&mut self, name: &Name, vis: Visibility) {
        let vis = self.intern_visibility(vis);
        let res =
            self.values.get_mut(name).expect("tried to update visibility of non-existent value");
        res.vis = vis;
    }

    pub(crate) fn update_visibility_macros(&mut self, name: &Name, vis: Visibility) {
        let res =
            self.macros.get_mut(name).expect("tried to update visibility of non-existent macro");
        res.vis = vis;
    }

    pub(crate) fn update_def_types(&mut self, name: &Name, def: ModuleDefId, vis: Visibility) {
        let vis = self.intern_visibility(vis);
        let res = self.types.get_mut(name).expect("tried to update def of non-existent type");
        res.def = def;
        res.vis = vis;
    }

    pub(crate) fn update_def_values(&mut self, name: &Name, def: ModuleDefId, vis: Visibility) {
        let vis = self.intern_visibility(vis);
        let res = self.values.get_mut(name).expect("tried to update def of non-existent value");
        res.def = def;
        res.vis = vis;
    }

    pub(crate) fn update_def_macros(&mut self, name: &Name, def: MacroId, vis: Visibility) {
        let res = self.macros.get_mut(name).expect("tried to update def of non-existent macro");
        res.def = def;
        res.vis = vis;
    }
}

impl PerNs {
    pub(crate) fn from_def(
        def: ModuleDefId,
        vis: Visibility,
        value_ns_ctor_vis: Option<Visibility>,
        import: Option<ImportOrExternCrate>,
    ) -> PerNs {
        match def {
            ModuleDefId::ModuleId(_) => PerNs::types(def, vis, import),
            ModuleDefId::FunctionId(_) => {
                PerNs::values(def, vis, import.and_then(ImportOrExternCrate::import_or_glob))
            }
            ModuleDefId::AdtId(adt) => match adt {
                AdtId::UnionId(_) => PerNs::types(def, vis, import),
                AdtId::EnumId(_) => PerNs::types(def, vis, import),
                AdtId::StructId(_) => match value_ns_ctor_vis {
                    Some(value_ns_ctor_vis) => PerNs {
                        types: Some(Item { def, vis, import }),
                        values: Some(Item {
                            def,
                            vis: value_ns_ctor_vis,
                            import: import.and_then(ImportOrExternCrate::import_or_glob),
                        }),
                        macros: None,
                    },
                    None => PerNs::types(def, vis, import),
                },
            },
            ModuleDefId::EnumVariantId(_) => match value_ns_ctor_vis {
                Some(value_ns_ctor_vis) => PerNs {
                    types: Some(Item { def, vis, import }),
                    values: Some(Item {
                        def,
                        vis: value_ns_ctor_vis,
                        import: import.and_then(ImportOrExternCrate::import_or_glob),
                    }),
                    macros: None,
                },
                None => PerNs::types(def, vis, import),
            },
            ModuleDefId::ConstId(_) | ModuleDefId::StaticId(_) => {
                PerNs::values(def, vis, import.and_then(ImportOrExternCrate::import_or_glob))
            }
            ModuleDefId::TraitId(_) => PerNs::types(def, vis, import),
            ModuleDefId::TypeAliasId(_) => PerNs::types(def, vis, import),
            ModuleDefId::BuiltinType(_) => PerNs::types(def, vis, import),
            ModuleDefId::MacroId(mac) => PerNs::macros(mac, vis, import),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ItemInNs {
    Types(ModuleDefId),
    Values(ModuleDefId),
    Macros(MacroId),
}

impl ItemInNs {
    pub fn as_module_def_id(self) -> Option<ModuleDefId> {
        match self {
            ItemInNs::Types(id) | ItemInNs::Values(id) => Some(id),
            ItemInNs::Macros(_) => None,
        }
    }

    /// Returns the crate defining this item (or `None` if `self` is built-in).
    pub fn krate(&self, db: &dyn SourceDatabase) -> Option<Crate> {
        self.module(db).map(|module_id| module_id.krate(db))
    }

    pub fn module(&self, db: &dyn SourceDatabase) -> Option<ModuleId> {
        match self {
            ItemInNs::Types(id) | ItemInNs::Values(id) => id.module(db),
            ItemInNs::Macros(id) => Some(id.module(db)),
        }
    }
}
