//! Describes items defined or visible (ie, imported) in a certain scope.
//! This is shared between modules and blocks.

use std::{fmt, hash::Hash, num::NonZeroU32, sync::LazyLock};

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
    builtin_type::{BuiltinFloat, BuiltinInt, BuiltinUint},
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

#[derive(Clone, Copy, PartialEq, Eq)]
struct ScopeDefId(u64);

impl ScopeDefId {
    // Modules are tracked and can have nonzero generations, so preserve their full Salsa ID.
    // The other definitions are permanent interned IDs; tag their index with Salsa's invalid-index
    // niche, which keeps the two representations disjoint without losing any ID bits.
    const COMPACT_START: u32 = salsa::Id::MAX_U32 + 1;
    const FUNCTION: u32 = 0;
    const STRUCT: u32 = 1;
    const UNION: u32 = 2;
    const ENUM: u32 = 3;
    const ENUM_VARIANT: u32 = 4;
    const CONST: u32 = 5;
    const STATIC: u32 = 6;
    const TRAIT: u32 = 7;
    const TYPE_ALIAS: u32 = 8;
    const BUILTIN: u32 = 9;
    const MACRO2: u32 = 10;
    const MACRO_RULES: u32 = 11;
    const PROC_MACRO: u32 = 12;
    const MODULE: u32 = 13;
    const COMPACT_PAYLOAD_MASK: u32 = (1 << 28) - 1;

    fn new(def: ModuleDefId) -> Self {
        match def {
            ModuleDefId::ModuleId(id) => Self(id.as_id().as_bits()),
            ModuleDefId::FunctionId(id) => Self::from_id(Self::FUNCTION, id),
            ModuleDefId::AdtId(AdtId::StructId(id)) => Self::from_id(Self::STRUCT, id),
            ModuleDefId::AdtId(AdtId::UnionId(id)) => Self::from_id(Self::UNION, id),
            ModuleDefId::AdtId(AdtId::EnumId(id)) => Self::from_id(Self::ENUM, id),
            ModuleDefId::EnumVariantId(id) => Self::from_id(Self::ENUM_VARIANT, id),
            ModuleDefId::ConstId(id) => Self::from_id(Self::CONST, id),
            ModuleDefId::StaticId(id) => Self::from_id(Self::STATIC, id),
            ModuleDefId::TraitId(id) => Self::from_id(Self::TRAIT, id),
            ModuleDefId::TypeAliasId(id) => Self::from_id(Self::TYPE_ALIAS, id),
            ModuleDefId::BuiltinType(builtin) => {
                Self(Self::pack(Self::BUILTIN, Self::builtin_index(builtin)))
            }
            ModuleDefId::MacroId(MacroId::Macro2Id(id)) => Self::from_id(Self::MACRO2, id),
            ModuleDefId::MacroId(MacroId::MacroRulesId(id)) => Self::from_id(Self::MACRO_RULES, id),
            ModuleDefId::MacroId(MacroId::ProcMacroId(id)) => Self::from_id(Self::PROC_MACRO, id),
        }
    }

    fn get(self) -> ModuleDefId {
        if self.0 as u32 <= salsa::Id::MAX_U32 {
            return ModuleId::from_id(salsa::Id::from_bits(self.0)).into();
        }
        let id = || salsa::Id::from_bits(u64::from(self.payload()));
        match self.kind() {
            Self::FUNCTION => crate::FunctionId::from_id(id()).into(),
            Self::STRUCT => crate::StructId::from_id(id()).into(),
            Self::UNION => crate::UnionId::from_id(id()).into(),
            Self::ENUM => crate::EnumId::from_id(id()).into(),
            Self::ENUM_VARIANT => crate::EnumVariantId::from_id(id()).into(),
            Self::CONST => ConstId::from_id(id()).into(),
            Self::STATIC => crate::StaticId::from_id(id()).into(),
            Self::TRAIT => TraitId::from_id(id()).into(),
            Self::TYPE_ALIAS => crate::TypeAliasId::from_id(id()).into(),
            Self::BUILTIN => ModuleDefId::BuiltinType(Self::builtin(self.payload())),
            Self::MACRO2 => crate::Macro2Id::from_id(id()).into(),
            Self::MACRO_RULES => crate::MacroRulesId::from_id(id()).into(),
            Self::PROC_MACRO => crate::ProcMacroId::from_id(id()).into(),
            kind => unreachable!("invalid compact module definition kind {kind}"),
        }
    }

    fn from_id(kind: u32, id: impl AsId) -> Self {
        let id = id.as_id();
        assert_eq!(id.generation(), 0, "interned definition ID unexpectedly has a generation");
        let payload = id.index().checked_add(1).expect("interned definition ID exceeds u32");
        Self(Self::pack(kind, payload))
    }

    const fn pack(kind: u32, payload: u32) -> u64 {
        (payload as u64) << 32 | (Self::COMPACT_START + kind) as u64
    }

    const fn kind(self) -> u32 {
        self.0 as u32 - Self::COMPACT_START
    }

    const fn payload(self) -> u32 {
        (self.0 >> 32) as u32
    }

    fn compact(self) -> Option<u32> {
        if self.0 as u32 <= salsa::Id::MAX_U32 {
            let raw = u32::try_from(self.0).ok()?;
            return (raw <= Self::COMPACT_PAYLOAD_MASK).then_some(Self::MODULE << 28 | raw);
        }
        let payload = self.payload();
        (payload <= Self::COMPACT_PAYLOAD_MASK).then_some(self.kind() << 28 | payload)
    }

    fn from_compact(compact: u32) -> Self {
        let kind = compact >> 28;
        let payload = compact & Self::COMPACT_PAYLOAD_MASK;
        if kind == Self::MODULE {
            Self(u64::from(payload))
        } else {
            Self(Self::pack(kind, payload))
        }
    }

    const fn builtin_index(builtin: BuiltinType) -> u32 {
        match builtin {
            BuiltinType::Char => 0,
            BuiltinType::Bool => 1,
            BuiltinType::Str => 2,
            BuiltinType::Int(BuiltinInt::Isize) => 3,
            BuiltinType::Int(BuiltinInt::I8) => 4,
            BuiltinType::Int(BuiltinInt::I16) => 5,
            BuiltinType::Int(BuiltinInt::I32) => 6,
            BuiltinType::Int(BuiltinInt::I64) => 7,
            BuiltinType::Int(BuiltinInt::I128) => 8,
            BuiltinType::Uint(BuiltinUint::Usize) => 9,
            BuiltinType::Uint(BuiltinUint::U8) => 10,
            BuiltinType::Uint(BuiltinUint::U16) => 11,
            BuiltinType::Uint(BuiltinUint::U32) => 12,
            BuiltinType::Uint(BuiltinUint::U64) => 13,
            BuiltinType::Uint(BuiltinUint::U128) => 14,
            BuiltinType::Float(BuiltinFloat::F16) => 15,
            BuiltinType::Float(BuiltinFloat::F32) => 16,
            BuiltinType::Float(BuiltinFloat::F64) => 17,
            BuiltinType::Float(BuiltinFloat::F128) => 18,
        }
    }

    const fn builtin(index: u32) -> BuiltinType {
        match index {
            0 => BuiltinType::Char,
            1 => BuiltinType::Bool,
            2 => BuiltinType::Str,
            3 => BuiltinType::Int(BuiltinInt::Isize),
            4 => BuiltinType::Int(BuiltinInt::I8),
            5 => BuiltinType::Int(BuiltinInt::I16),
            6 => BuiltinType::Int(BuiltinInt::I32),
            7 => BuiltinType::Int(BuiltinInt::I64),
            8 => BuiltinType::Int(BuiltinInt::I128),
            9 => BuiltinType::Uint(BuiltinUint::Usize),
            10 => BuiltinType::Uint(BuiltinUint::U8),
            11 => BuiltinType::Uint(BuiltinUint::U16),
            12 => BuiltinType::Uint(BuiltinUint::U32),
            13 => BuiltinType::Uint(BuiltinUint::U64),
            14 => BuiltinType::Uint(BuiltinUint::U128),
            15 => BuiltinType::Float(BuiltinFloat::F16),
            16 => BuiltinType::Float(BuiltinFloat::F32),
            17 => BuiltinType::Float(BuiltinFloat::F64),
            18 => BuiltinType::Float(BuiltinFloat::F128),
            _ => unreachable!(),
        }
    }
}

impl fmt::Debug for ScopeDefId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.get().fmt(f)
    }
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
struct ScopeItem(u64);

type ScopeTypesItem = ScopeItem;
type ScopeValuesItem = ScopeItem;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeItemFull {
    def: ScopeDefId,
    vis: ScopeVisibility,
    import: ScopeImportId,
}

impl ScopeItemFull {
    fn sort_key(self) -> (u64, u32, Option<NonZeroU32>) {
        (self.def.0, self.vis.0, self.import.0)
    }
}

impl ScopeItem {
    fn new_value(
        item: ValuesItem,
        vis: ScopeVisibility,
        imports: &mut ThinVec<ScopeImportOrExternCrate>,
        overflow: &mut ThinVec<ScopeItemFull>,
    ) -> Self {
        let import = ScopeImportId::new(item.import.map(Into::into), imports);
        Self::pack(ScopeItemFull { def: ScopeDefId::new(item.def), vis, import }, overflow)
    }

    fn get_value(
        self,
        visibilities: &[Visibility],
        imports: &[ScopeImportOrExternCrate],
        overflow: &[ScopeItemFull],
    ) -> ValuesItem {
        let ScopeItemFull { def, vis, import } = self.full(overflow);
        ValuesItem {
            def: def.get(),
            vis: vis.get(visibilities),
            import: import.get(imports).map(|import| {
                import.import_or_glob().expect("value namespace contains an extern-crate import")
            }),
        }
    }
}

impl ScopeItem {
    const OVERFLOW: u64 = 1 << 63;
    const VISIBILITY_SHIFT: u32 = 32;
    const IMPORT_SHIFT: u32 = 44;
    const VISIBILITY_MASK: u32 = (1 << 12) - 1;
    const IMPORT_MASK: u32 = (1 << 19) - 1;

    fn new_type(
        item: TypesItem,
        vis: ScopeVisibility,
        imports: &mut ThinVec<ScopeImportOrExternCrate>,
        overflow: &mut ThinVec<ScopeItemFull>,
    ) -> Self {
        let import = ScopeImportId::new(item.import, imports);
        Self::pack(ScopeItemFull { def: ScopeDefId::new(item.def), vis, import }, overflow)
    }

    fn pack(item: ScopeItemFull, overflow: &mut ThinVec<ScopeItemFull>) -> Self {
        let vis = if item.vis == ScopeVisibility::PUBLIC {
            Some(0)
        } else {
            item.vis.0.checked_add(1).filter(|&vis| vis <= Self::VISIBILITY_MASK)
        };
        let import = item.import.0.map_or(0, NonZeroU32::get);
        if let (Some(def), Some(vis), true) = (item.def.compact(), vis, import <= Self::IMPORT_MASK)
        {
            return Self(
                u64::from(def)
                    | u64::from(vis) << Self::VISIBILITY_SHIFT
                    | u64::from(import) << Self::IMPORT_SHIFT,
            );
        }

        let index =
            u64::try_from(overflow.len()).expect("ItemScope has more than u64::MAX entries");
        overflow.push(item);
        Self(Self::OVERFLOW | index)
    }

    fn full(self, overflow: &[ScopeItemFull]) -> ScopeItemFull {
        if self.0 & Self::OVERFLOW != 0 {
            return overflow[(self.0 & !Self::OVERFLOW) as usize];
        }
        let def = ScopeDefId::from_compact(self.0 as u32);
        let vis = ((self.0 >> Self::VISIBILITY_SHIFT) as u32) & Self::VISIBILITY_MASK;
        let vis = if vis == 0 { ScopeVisibility::PUBLIC } else { ScopeVisibility(vis - 1) };
        let import = ((self.0 >> Self::IMPORT_SHIFT) as u32) & Self::IMPORT_MASK;
        let import = ScopeImportId(NonZeroU32::new(import));
        ScopeItemFull { def, vis, import }
    }

    fn get_type(
        self,
        visibilities: &[Visibility],
        imports: &[ScopeImportOrExternCrate],
        overflow: &[ScopeItemFull],
    ) -> TypesItem {
        let ScopeItemFull { def, vis, import } = self.full(overflow);
        TypesItem { def: def.get(), vis: vis.get(visibilities), import: import.get(imports) }
    }
}

const _: () = assert!(std::mem::size_of::<ScopeVisibility>() == 4);
const _: () = assert!(std::mem::size_of::<ScopeImportId>() == 4);
const _: () = assert!(ScopeDefId::PROC_MACRO <= u32::MAX - salsa::Id::MAX_U32);
const _: () = assert!(std::mem::size_of::<ScopeValuesItem>() == 8);
const _: () = assert!(std::mem::size_of::<ScopeImportOrExternCrate>() == 12);
const _: () = assert!(std::mem::size_of::<ScopeTypesItem>() == 8);

#[derive(Debug)]
struct ScopeNameIndex(Box<[u8]>);

impl ScopeNameIndex {
    fn from_sorted(indices: Vec<u32>) -> Self {
        if indices.is_empty() {
            return Self(Box::new([]));
        }
        let width = if indices.len() <= u8::MAX as usize + 1 {
            1
        } else if indices.len() <= u16::MAX as usize + 1 {
            2
        } else {
            4
        };
        let mut packed = Vec::with_capacity(1 + indices.len() * width);
        packed.push(width as u8);
        for index in indices {
            match width {
                1 => packed.push(u8::try_from(index).unwrap()),
                2 => packed.extend_from_slice(&u16::try_from(index).unwrap().to_ne_bytes()),
                4 => packed.extend_from_slice(&index.to_ne_bytes()),
                _ => unreachable!(),
            }
        }
        Self(packed.into_boxed_slice())
    }

    fn len(&self) -> usize {
        self.0.first().map_or(0, |&width| (self.0.len() - 1) / usize::from(width))
    }

    fn get(&self, position: usize) -> usize {
        let width = usize::from(self.0[0]);
        let start = 1 + position * width;
        match width {
            1 => usize::from(self.0[start]),
            2 => usize::from(u16::from_ne_bytes(self.0[start..start + 2].try_into().unwrap())),
            4 => u32::from_ne_bytes(self.0[start..start + 4].try_into().unwrap()) as usize,
            _ => unreachable!("scope name index has a valid width"),
        }
    }

    fn binary_search_by(
        &self,
        mut compare: impl FnMut(usize) -> std::cmp::Ordering,
    ) -> Option<usize> {
        let (mut left, mut right) = (0, self.len());
        while left < right {
            let middle = left + (right - left) / 2;
            match compare(self.get(middle)) {
                std::cmp::Ordering::Less => left = middle + 1,
                std::cmp::Ordering::Greater => right = middle,
                std::cmp::Ordering::Equal => return Some(middle),
            }
        }
        None
    }

    #[cfg(test)]
    fn packed_bytes(&self) -> usize {
        self.0.len()
    }
}

#[derive(Debug)]
enum ScopeMap<V> {
    Mutable(FxIndexMap<Name, V>),
    Frozen { entries: Box<[(Name, V)]>, by_name: ScopeNameIndex },
}

impl<V> Default for ScopeMap<V> {
    fn default() -> Self {
        Self::Mutable(FxIndexMap::default())
    }
}

impl<V: PartialEq> PartialEq for ScopeMap<V> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Frozen { entries: left_entries, by_name: left_by_name },
                Self::Frozen { entries: right_entries, by_name: right_by_name },
            ) => {
                left_by_name.len() == right_by_name.len()
                    && (0..left_by_name.len()).all(|position| {
                        let left = left_by_name.get(position);
                        let right = right_by_name.get(position);
                        let (left_name, left_value) = &left_entries[left];
                        let (right_name, right_value) = &right_entries[right];
                        left_name == right_name && left_value == right_value
                    })
            }
            _ => {
                self.iter().count() == other.iter().count()
                    && self.iter().all(|(name, value)| other.get(name) == Some(value))
            }
        }
    }
}

impl<V: Eq> Eq for ScopeMap<V> {}

impl<V> ScopeMap<V> {
    fn get(&self, name: &Name) -> Option<&V> {
        match self {
            Self::Mutable(map) => map.get(name),
            Self::Frozen { entries, by_name } => {
                let index = by_name.binary_search_by(|index| entries[index].0.cmp(name))?;
                Some(&entries[by_name.get(index)].1)
            }
        }
    }

    fn get_mut(&mut self, name: &Name) -> Option<&mut V> {
        match self {
            Self::Mutable(map) => map.get_mut(name),
            Self::Frozen { entries, by_name } => {
                let index = by_name.binary_search_by(|index| entries[index].0.cmp(name))?;
                Some(&mut entries[by_name.get(index)].1)
            }
        }
    }

    #[cfg(test)]
    fn insert(&mut self, name: Name, value: V) -> Option<V> {
        match self {
            Self::Mutable(map) => map.insert(name, value),
            Self::Frozen { .. } => panic!("cannot insert into a frozen item scope"),
        }
    }

    fn shift_remove(&mut self, name: &Name) -> Option<V> {
        match self {
            Self::Mutable(map) => map.shift_remove(name),
            Self::Frozen { .. } => panic!("cannot remove from a frozen item scope"),
        }
    }

    fn entry(&mut self, name: Name) -> Entry<'_, Name, V> {
        match self {
            Self::Mutable(map) => map.entry(name),
            Self::Frozen { .. } => panic!("cannot insert into a frozen item scope"),
        }
    }

    fn iter(&self) -> impl Iterator<Item = (&Name, &V)> {
        match self {
            Self::Mutable(map) => Either::Left(map.iter()),
            Self::Frozen { entries, .. } => {
                Either::Right(entries.iter().map(|(name, value)| (name, value)))
            }
        }
    }

    fn keys(&self) -> impl Iterator<Item = &Name> {
        self.iter().map(|(name, _)| name)
    }

    fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, value)| value)
    }

    fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        match self {
            Self::Mutable(map) => Either::Left(map.values_mut()),
            Self::Frozen { entries, .. } => {
                Either::Right(entries.iter_mut().map(|(_, value)| value))
            }
        }
    }

    fn shrink_to_fit(&mut self) {
        let map = match std::mem::take(self) {
            Self::Mutable(map) => map,
            frozen @ Self::Frozen { .. } => {
                *self = frozen;
                return;
            }
        };
        let entries = map.into_iter().collect::<Vec<_>>().into_boxed_slice();
        let len = u32::try_from(entries.len()).expect("ItemScope has more than u32::MAX entries");
        let mut by_name = (0..len).collect::<Vec<_>>();
        by_name.sort_unstable_by(|&left, &right| {
            entries[left as usize].0.cmp(&entries[right as usize].0)
        });
        *self = Self::Frozen { entries, by_name: ScopeNameIndex::from_sorted(by_name) };
    }

    #[cfg(test)]
    fn secondary_index_bytes(&self) -> usize {
        match self {
            Self::Mutable(_) => 0,
            Self::Frozen { by_name, .. } => by_name.packed_bytes(),
        }
    }
}

#[derive(Debug)]
enum ScopeHashMap<K, V> {
    Mutable(Box<FxHashMap<K, V>>),
    Frozen(Box<[(K, V)]>),
}

impl<K, V> Default for ScopeHashMap<K, V> {
    fn default() -> Self {
        Self::Frozen(Box::new([]))
    }
}

impl<K: Eq + Hash, V: PartialEq> PartialEq for ScopeHashMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().count() == other.iter().count()
            && self.iter().all(|(key, value)| other.get(key) == Some(value))
    }
}

impl<K: Eq + Hash, V: Eq> Eq for ScopeHashMap<K, V> {}

impl<K: Eq + Hash, V> ScopeHashMap<K, V> {
    fn get(&self, key: &K) -> Option<&V> {
        match self {
            Self::Mutable(map) => map.get(key),
            Self::Frozen(entries) => {
                entries.iter().find_map(|(stored, value)| (stored == key).then_some(value))
            }
        }
    }

    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match self {
            Self::Mutable(map) => map.get_mut(key),
            Self::Frozen(entries) => {
                entries.iter_mut().find_map(|(stored, value)| (stored == key).then_some(value))
            }
        }
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.mutable().insert(key, value)
    }

    fn entry(&mut self, key: K) -> std::collections::hash_map::Entry<'_, K, V> {
        self.mutable().entry(key)
    }

    fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        match self {
            Self::Mutable(map) => Either::Left(map.iter()),
            Self::Frozen(entries) => Either::Right(entries.iter().map(|(key, value)| (key, value))),
        }
    }

    fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(key, _)| key)
    }

    fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, value)| value)
    }

    fn shrink_to_fit(&mut self) {
        match std::mem::take(self) {
            Self::Mutable(map) => {
                *self = Self::Frozen((*map).into_iter().collect::<Vec<_>>().into_boxed_slice())
            }
            frozen @ Self::Frozen(_) => *self = frozen,
        }
    }

    fn mutable(&mut self) -> &mut FxHashMap<K, V> {
        if matches!(self, Self::Frozen(_)) {
            let Self::Frozen(entries) = std::mem::take(self) else { unreachable!() };
            *self = Self::Mutable(Box::new(entries.into_vec().into_iter().collect()));
        }
        let Self::Mutable(map) = self else { unreachable!() };
        map
    }
}

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
    types: ScopeMap<ScopeTypesItem>,
    item_overflow: ThinVec<ScopeItemFull>,
    values: ScopeMap<ScopeValuesItem>,
    macros: FxIndexMap<Name, MacrosItem>,
    /// Deduplicated visibilities referenced by type and value entries.
    visibilities: ThinVec<Visibility>,
    /// Deduplicated import provenance referenced by type and value entries.
    imports: ThinVec<ScopeImportOrExternCrate>,
    unresolved: ScopeHashMap<Name, ()>,

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
    use_imports_types: ScopeHashMap<ImportOrExternCrate, ImportOrDef>,
    use_imports_values: ScopeHashMap<ImportOrGlob, ImportOrDef>,
    use_imports_macros: ScopeHashMap<ImportOrExternCrate, ImportOrDef>,

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
    legacy_macros: ScopeHashMap<Name, SmallVec<[MacroId; 1]>>,
    /// The attribute macro invocations in this scope.
    attr_macros: ScopeHashMap<AstId<ast::Item>, MacroCallId>,
    /// The macro invocations in this scope.
    macro_invocations: ScopeHashMap<AstId<ast::MacroCall>, MacroCallId>,
    /// The derive macro invocations in this scope, keyed by the owner item over the actual derive attributes
    /// paired with the derive macro invocations for the specific attribute.
    derive_macros: ScopeHashMap<AstId<ast::Adt>, SmallVec<[DeriveMacroInvocation; 1]>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::visibility::VisibilityExplicitness;

    #[test]
    fn values_scope_entry_is_compact() {
        assert_eq!(std::mem::size_of::<ScopeValuesItem>(), 8);
    }

    #[test]
    fn type_scope_entry_is_compact() {
        assert_eq!(std::mem::size_of::<ScopeTypesItem>(), 8);
    }

    #[test]
    fn compact_scope_definitions_roundtrip_every_kind() {
        let id = salsa::Id::from_bits(42);
        let mut definitions = vec![
            ModuleDefId::ModuleId(ModuleId::from_id(id.with_generation(7))),
            ModuleDefId::FunctionId(crate::FunctionId::from_id(id)),
            ModuleDefId::AdtId(AdtId::StructId(crate::StructId::from_id(id))),
            ModuleDefId::AdtId(AdtId::UnionId(crate::UnionId::from_id(id))),
            ModuleDefId::AdtId(AdtId::EnumId(crate::EnumId::from_id(id))),
            ModuleDefId::EnumVariantId(crate::EnumVariantId::from_id(id)),
            ModuleDefId::ConstId(ConstId::from_id(id)),
            ModuleDefId::StaticId(crate::StaticId::from_id(id)),
            ModuleDefId::TraitId(TraitId::from_id(id)),
            ModuleDefId::TypeAliasId(crate::TypeAliasId::from_id(id)),
            ModuleDefId::MacroId(MacroId::Macro2Id(crate::Macro2Id::from_id(id))),
            ModuleDefId::MacroId(MacroId::MacroRulesId(crate::MacroRulesId::from_id(id))),
            ModuleDefId::MacroId(MacroId::ProcMacroId(crate::ProcMacroId::from_id(id))),
        ];
        definitions.extend(
            BuiltinType::all_builtin_types()
                .into_iter()
                .map(|(_, builtin)| ModuleDefId::BuiltinType(builtin)),
        );

        assert_eq!(std::mem::size_of::<ScopeDefId>(), 8);
        for definition in definitions {
            assert_eq!(ScopeDefId::new(definition).get(), definition);
        }
    }

    #[test]
    fn compact_type_scope_entry_preserves_full_width_ids_in_overflow() {
        let item = ScopeItemFull {
            def: ScopeDefId::new(ModuleDefId::ModuleId(ModuleId::from_id(
                salsa::Id::from_bits(42).with_generation(7),
            ))),
            vis: ScopeVisibility::PUBLIC,
            import: ScopeImportId::NONE,
        };
        let mut overflow = ThinVec::new();

        let packed = ScopeTypesItem::pack(item, &mut overflow);

        assert_eq!(overflow.as_slice(), [item]);
        assert_eq!(packed.full(&overflow), item);
    }

    #[test]
    fn overflow_type_scope_equality_is_insertion_order_independent() {
        let names = [
            Name::new_symbol_root(intern::Symbol::intern("first")),
            Name::new_symbol_root(intern::Symbol::intern("second")),
        ];
        let definitions = [
            ModuleDefId::ModuleId(ModuleId::from_id(salsa::Id::from_bits(42).with_generation(7))),
            ModuleDefId::ModuleId(ModuleId::from_id(salsa::Id::from_bits(42).with_generation(8))),
        ];
        let mut first = ItemScope::default();
        let mut second = ItemScope::default();

        for (scope, order) in [(&mut first, [0, 1]), (&mut second, [1, 0])] {
            for index in order {
                let item = ScopeItemFull {
                    def: ScopeDefId::new(definitions[index]),
                    vis: ScopeVisibility::PUBLIC,
                    import: ScopeImportId::NONE,
                };
                scope.types.insert(
                    names[index].clone(),
                    ScopeTypesItem::pack(item, &mut scope.item_overflow),
                );
            }
            scope.shrink_to_fit();
        }

        assert_eq!(first, second);
    }

    #[test]
    fn frozen_scope_map_preserves_lookup_and_insertion_order() {
        let first = Name::new_symbol_root(intern::Symbol::intern("first"));
        let second = Name::new_symbol_root(intern::Symbol::intern("second"));
        let third = Name::new_symbol_root(intern::Symbol::intern("third"));
        let mut map = ScopeMap::default();

        map.entry(second.clone()).or_insert(2);
        map.entry(first.clone()).or_insert(1);
        map.entry(third.clone()).or_insert(3);
        map.shrink_to_fit();

        assert_eq!(map.secondary_index_bytes(), 4);
        assert_eq!(map.get(&first), Some(&1));
        assert_eq!(map.get(&second), Some(&2));
        assert_eq!(map.get(&third), Some(&3));
        assert_eq!(
            map.iter().map(|(name, &value)| (name.clone(), value)).collect::<Vec<_>>(),
            [(second.clone(), 2), (first.clone(), 1), (third.clone(), 3),]
        );

        let mut reordered = ScopeMap::default();
        reordered.entry(third.clone()).or_insert(3);
        reordered.entry(first.clone()).or_insert(1);
        reordered.entry(second.clone()).or_insert(2);
        reordered.shrink_to_fit();
        assert_eq!(map, reordered, "map equality must remain independent of insertion order");
    }

    #[test]
    fn packed_scope_name_index_preserves_wide_indices() {
        for (len, expected_bytes) in [(257, 515), (65_537, 262_149)] {
            let index = ScopeNameIndex::from_sorted((0..len as u32).collect());

            assert_eq!(index.packed_bytes(), expected_bytes);
            assert_eq!(index.len(), len);
            assert_eq!(index.get(len - 1), len - 1);
            assert_eq!(index.binary_search_by(|stored| stored.cmp(&(len / 2))), Some(len / 2));
        }
    }

    #[test]
    fn frozen_scope_hash_map_preserves_lookup_iteration_and_equality() {
        let first = Name::new_symbol_root(intern::Symbol::intern("first"));
        let second = Name::new_symbol_root(intern::Symbol::intern("second"));
        let third = Name::new_symbol_root(intern::Symbol::intern("third"));
        let mut map = ScopeHashMap::default();

        map.insert(second.clone(), 2);
        map.insert(first.clone(), 1);
        map.insert(third.clone(), 3);
        let iteration_order = map.iter().map(|(name, &value)| (name.clone(), value)).collect_vec();
        map.shrink_to_fit();

        assert_eq!(map.get(&first), Some(&1));
        assert_eq!(map.get(&second), Some(&2));
        assert_eq!(map.get(&third), Some(&3));
        assert_eq!(
            map.iter().map(|(name, &value)| (name.clone(), value)).collect_vec(),
            iteration_order
        );

        let mut reordered = ScopeHashMap::default();
        reordered.insert(third, 3);
        reordered.insert(first, 1);
        reordered.insert(second, 2);
        reordered.shrink_to_fit();
        assert_eq!(map, reordered, "map equality must remain independent of insertion order");

        let fourth = Name::new_symbol_root(intern::Symbol::intern("fourth"));
        assert_eq!(map.insert(fourth.clone(), 4), None);
        assert_eq!(map.get(&fourth), Some(&4));
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
                ScopeTypesItem::new_type(
                    TypesItem { def, vis: type_vis, import: Some(type_import) },
                    type_id,
                    &mut scope.imports,
                    &mut scope.item_overflow,
                ),
            );
            scope.values.insert(
                Name::missing(),
                ScopeValuesItem::new_value(
                    ValuesItem { def, vis: value_vis, import: Some(value_import) },
                    value_id,
                    &mut scope.imports,
                    &mut scope.item_overflow,
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
        let mut overflow = ThinVec::new();
        let compact_type = ScopeTypesItem::new_type(
            type_item,
            ScopeVisibility::PUBLIC,
            &mut stored,
            &mut overflow,
        );
        let compact_value = ScopeValuesItem::new_value(
            value_item,
            ScopeVisibility::PUBLIC,
            &mut stored,
            &mut overflow,
        );

        assert_eq!(stored.len(), imports.len() + 1);
        assert!(overflow.is_empty());
        assert_eq!(compact_type.get_type(&[], &stored, &overflow), type_item);
        assert_eq!(compact_value.get_value(&[], &stored, &overflow), value_item);
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
            .chain(self.unresolved.keys())
            .sorted()
            .dedup()
            .map(move |name| (name, self.get(name)))
    }

    pub fn values(&self) -> impl Iterator<Item = (&Name, Item<ModuleDefId, ImportOrGlob>)> + '_ {
        self.values.iter().map(|(name, &item)| {
            (name, item.get_value(&self.visibilities, &self.imports, &self.item_overflow))
        })
    }

    pub fn types(
        &self,
    ) -> impl Iterator<Item = (&Name, Item<ModuleDefId, ImportOrExternCrate>)> + '_ {
        self.types.iter().map(|(name, &item)| {
            (name, item.get_type(&self.visibilities, &self.imports, &self.item_overflow))
        })
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
        self.types.values().filter_map(|ns| match ns.full(&self.item_overflow) {
            ScopeItemFull { def, vis, .. } if let ModuleDefId::ModuleId(module) = def.get() => {
                Some((module, vis.get(&self.visibilities)))
            }
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
                .map(|item| item.get_type(&self.visibilities, &self.imports, &self.item_overflow)),
            values: self
                .values
                .get(name)
                .copied()
                .map(|item| item.get_value(&self.visibilities, &self.imports, &self.item_overflow)),
            macros: self.macros.get(name).copied(),
        }
    }

    pub(crate) fn type_(&self, name: &Name) -> Option<(ModuleDefId, Visibility)> {
        self.types.get(name).map(|&item| {
            let item = item.full(&self.item_overflow);
            (item.def.get(), item.vis.get(&self.visibilities))
        })
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
            ItemInNs::Types(def) => {
                let def = ScopeDefId::new(def);
                self.types.iter().find_map(|(name, other_def)| {
                    let other_def = other_def.full(&self.item_overflow);
                    (other_def.def == def).then_some((
                        name,
                        other_def.vis.get(&self.visibilities),
                        other_def.import.is_none(),
                    ))
                })
            }
            ItemInNs::Values(def) => {
                let def = ScopeDefId::new(def);
                self.values.iter().find_map(|(name, other_def)| {
                    let other_def = other_def.full(&self.item_overflow);
                    (other_def.def == def).then_some((
                        name,
                        other_def.vis.get(&self.visibilities),
                        other_def.import.is_none(),
                    ))
                })
            }
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
            ItemInNs::Types(def) => {
                let def = ScopeDefId::new(def);
                self.types
                    .iter()
                    .filter_map(|(name, other_def)| {
                        let other_def = other_def.full(&self.item_overflow);
                        (other_def.def == def).then_some((
                            name,
                            other_def.vis.get(&self.visibilities),
                            other_def.import.is_none(),
                        ))
                    })
                    .find_map(|(a, b, c)| cb(a, b, c))
            }
            ItemInNs::Values(def) => {
                let def = ScopeDefId::new(def);
                self.values
                    .iter()
                    .filter_map(|(name, other_def)| {
                        let other_def = other_def.full(&self.item_overflow);
                        (other_def.def == def).then_some((
                            name,
                            other_def.vis.get(&self.visibilities),
                            other_def.import.is_none(),
                        ))
                    })
                    .find_map(|(a, b, c)| cb(a, b, c))
            }
        }
    }

    pub(crate) fn traits(&self) -> impl Iterator<Item = TraitId> + '_ {
        self.types
            .values()
            .filter_map(|def| match def.full(&self.item_overflow).def.get() {
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
        if self
            .values
            .get(name)
            .is_some_and(|entry| entry.full(&self.item_overflow).def == ScopeDefId::new(def))
        {
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
            let overflow = &mut self.item_overflow;
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
                    entry.insert(ScopeTypesItem::new_type(fld, vis, imports, overflow));
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
                                    .get_type(visibilities, imports, overflow)
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
                                entry.insert(ScopeTypesItem::new_type(fld, vis, imports, overflow));
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
            let overflow = &mut self.item_overflow;
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
                    entry.insert(ScopeValuesItem::new_value(fld, vis, imports, overflow));
                    changed = true;
                }
                Entry::Occupied(mut entry)
                    if !matches!(import, Some(ImportOrExternCrate::Glob(..))) =>
                {
                    let import = import.and_then(ImportOrExternCrate::import_or_glob);
                    if glob_imports.values.remove(&lookup)
                        || entry
                            .get()
                            .get_value(visibilities, imports, overflow)
                            .is_reresolved_by(&fld.def, import)
                    {
                        cov_mark::hit!(import_shadowed);

                        let prev = std::mem::replace(&mut fld.import, import);
                        if let Some(import) = import {
                            self.use_imports_values
                                .insert(import, prev.map_or(ImportOrDef::Def(fld.def), Into::into));
                        }
                        entry.insert(ScopeValuesItem::new_value(fld, vis, imports, overflow));
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

        if def.is_none() && self.unresolved.insert(lookup.1, ()).is_none() {
            changed = true;
        }

        changed
    }

    /// Marks everything that is not a procedural macro as private to `this_module`.
    pub(crate) fn censor_non_proc_macros(&mut self, krate: Crate) {
        let visibility = Visibility::PubCrate(krate);
        let vis = self.intern_visibility(visibility);
        for item in self.types.values_mut().chain(self.values.values_mut()) {
            let mut full = item.full(&self.item_overflow);
            full.vis = vis;
            *item = ScopeItem::pack(full, &mut self.item_overflow);
        }
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
        let old_imports = std::mem::take(&mut self.imports);
        let old_item_overflow = std::mem::take(&mut self.item_overflow);
        for item in self.types.values_mut().chain(self.values.values_mut()) {
            let mut full = item.full(&old_item_overflow);
            full.vis =
                ScopeVisibility::new(full.vis.get(&old_visibilities), &mut self.visibilities);
            full.import = ScopeImportId::new(full.import.get(&old_imports), &mut self.imports);
            *item = ScopeItem::pack(full, &mut self.item_overflow);
        }
        if self.item_overflow.len() > 1 {
            let old_item_overflow = std::mem::take(&mut self.item_overflow);
            let mut sorted_item_overflow = old_item_overflow.iter().copied().collect::<Vec<_>>();
            sorted_item_overflow.sort_unstable_by_key(|item| item.sort_key());
            sorted_item_overflow.dedup();
            for item in self
                .types
                .values_mut()
                .chain(self.values.values_mut())
                .filter(|item| item.0 & ScopeItem::OVERFLOW != 0)
            {
                let full = item.full(&old_item_overflow);
                let index = sorted_item_overflow
                    .binary_search_by_key(&full.sort_key(), |item| item.sort_key())
                    .expect("overflow item disappeared while sorting");
                *item = ScopeItem(
                    ScopeItem::OVERFLOW
                        | u64::try_from(index).expect("ItemScope has more than u64::MAX entries"),
                );
            }
            self.item_overflow = sorted_item_overflow.into_iter().collect();
        }

        // Exhaustive match to require handling new fields.
        let Self {
            types,
            item_overflow,
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
        item_overflow.shrink_to_fit();
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
        let mut full = res.full(&self.item_overflow);
        full.vis = vis;
        *res = ScopeItem::pack(full, &mut self.item_overflow);
    }

    pub(crate) fn update_visibility_values(&mut self, name: &Name, vis: Visibility) {
        let vis = self.intern_visibility(vis);
        let res =
            self.values.get_mut(name).expect("tried to update visibility of non-existent value");
        let mut full = res.full(&self.item_overflow);
        full.vis = vis;
        *res = ScopeItem::pack(full, &mut self.item_overflow);
    }

    pub(crate) fn update_visibility_macros(&mut self, name: &Name, vis: Visibility) {
        let res =
            self.macros.get_mut(name).expect("tried to update visibility of non-existent macro");
        res.vis = vis;
    }

    pub(crate) fn update_def_types(&mut self, name: &Name, def: ModuleDefId, vis: Visibility) {
        let vis = self.intern_visibility(vis);
        let res = self.types.get_mut(name).expect("tried to update def of non-existent type");
        let mut full = res.full(&self.item_overflow);
        full.def = ScopeDefId::new(def);
        full.vis = vis;
        *res = ScopeItem::pack(full, &mut self.item_overflow);
    }

    pub(crate) fn update_def_values(&mut self, name: &Name, def: ModuleDefId, vis: Visibility) {
        let vis = self.intern_visibility(vis);
        let res = self.values.get_mut(name).expect("tried to update def of non-existent value");
        let mut full = res.full(&self.item_overflow);
        full.def = ScopeDefId::new(def);
        full.vis = vis;
        *res = ScopeItem::pack(full, &mut self.item_overflow);
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
