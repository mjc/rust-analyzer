//! Pre-type IR item generics
use std::{
    fmt,
    hash::{Hash, Hasher},
    ops,
};

use base_db::SourceDatabase;
use hir_expand::name::Name;
use la_arena::{Arena, Idx, RawIdx};
use salsa::SalsaValue;
use stdx::impl_from;
use thin_vec::ThinVec;

use crate::{
    AdtId, ConstParamId, GenericDefId, LifetimeParamId, TypeOrConstParamId, TypeParamId,
    expr_store::{ExpressionStore, ExpressionStoreSourceMap},
    signatures::{
        ConstSignature, EnumSignature, FunctionSignature, ImplSignature, StaticSignature,
        StructSignature, TraitSignature, TypeAliasSignature, UnionSignature,
    },
    type_ref::{ConstRef, LifetimeRefId, TypeBound, TypeRefId},
};

pub type LocalTypeOrConstParamId = Idx<TypeOrConstParamData>;
pub type LocalLifetimeParamId = Idx<LifetimeParamData>;

/// Data about a generic type parameter (to a function, struct, impl, ...).
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct TypeParamData {
    /// [`None`] only if the type ref is an [`crate::type_ref::TypeRef::ImplTrait`].
    pub name: Option<Name>,
    pub default: Option<TypeRefId>,
    pub provenance: TypeParamProvenance,
}

/// Data about a generic lifetime parameter (to a function, struct, impl, ...).
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct LifetimeParamData {
    pub name: Name,
    pub bound_type: LifetimeBoundType,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum LifetimeBoundType {
    EarlyBound,
    LateBound,
}

impl LifetimeParamData {
    pub fn is_late_bound(&self) -> bool {
        self.bound_type == LifetimeBoundType::LateBound
    }
}

/// Data about a generic const parameter (to a function, struct, impl, ...).
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct ConstParamData {
    pub name: Name,
    pub ty: TypeRefId,
    pub default: Option<ConstRef>,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum TypeParamProvenance {
    TypeParamList,
    TraitSelf,
    ArgumentImplTrait,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, SalsaValue)]
pub enum TypeOrConstParamData {
    TypeParamData(TypeParamData),
    ConstParamData(ConstParamData),
}

impl TypeOrConstParamData {
    pub fn name(&self) -> Option<&Name> {
        match self {
            TypeOrConstParamData::TypeParamData(it) => it.name.as_ref(),
            TypeOrConstParamData::ConstParamData(it) => Some(&it.name),
        }
    }

    pub fn has_default(&self) -> bool {
        match self {
            TypeOrConstParamData::TypeParamData(it) => it.default.is_some(),
            TypeOrConstParamData::ConstParamData(it) => it.default.is_some(),
        }
    }

    pub fn type_param(&self) -> Option<&TypeParamData> {
        match self {
            TypeOrConstParamData::TypeParamData(it) => Some(it),
            TypeOrConstParamData::ConstParamData(_) => None,
        }
    }

    pub fn const_param(&self) -> Option<&ConstParamData> {
        match self {
            TypeOrConstParamData::TypeParamData(_) => None,
            TypeOrConstParamData::ConstParamData(it) => Some(it),
        }
    }

    pub fn is_trait_self(&self) -> bool {
        match self {
            TypeOrConstParamData::TypeParamData(it) => {
                it.provenance == TypeParamProvenance::TraitSelf
            }
            TypeOrConstParamData::ConstParamData(_) => false,
        }
    }
}

impl_from!(TypeParamData, ConstParamData for TypeOrConstParamData);

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum GenericParamData {
    TypeParamData(TypeParamData),
    ConstParamData(ConstParamData),
    LifetimeParamData(LifetimeParamData),
}

impl GenericParamData {
    pub fn name(&self) -> Option<&Name> {
        match self {
            GenericParamData::TypeParamData(it) => it.name.as_ref(),
            GenericParamData::ConstParamData(it) => Some(&it.name),
            GenericParamData::LifetimeParamData(it) => Some(&it.name),
        }
    }

    pub fn type_param(&self) -> Option<&TypeParamData> {
        match self {
            GenericParamData::TypeParamData(it) => Some(it),
            _ => None,
        }
    }

    pub fn const_param(&self) -> Option<&ConstParamData> {
        match self {
            GenericParamData::ConstParamData(it) => Some(it),
            _ => None,
        }
    }

    pub fn lifetime_param(&self) -> Option<&LifetimeParamData> {
        match self {
            GenericParamData::LifetimeParamData(it) => Some(it),
            _ => None,
        }
    }
}

impl_from!(TypeParamData, ConstParamData, LifetimeParamData for GenericParamData);

#[derive(Debug, Clone, Copy)]
pub enum GenericParamDataRef<'a> {
    TypeParamData(&'a TypeParamData),
    ConstParamData(&'a ConstParamData),
    LifetimeParamData(&'a LifetimeParamData),
}

/// Data about the generic parameters of a function, struct, impl, etc.
#[derive(PartialEq, Eq, Debug, Hash)]
struct GenericParamsData {
    pub(crate) type_or_consts: Arena<TypeOrConstParamData>,
    pub(crate) lifetimes: Arena<LifetimeParamData>,
    pub(crate) where_predicates: Box<[WherePredicate]>,
}

#[derive(Default)]
pub struct GenericParams(Option<Box<GenericParamsData>>);

static EMPTY: GenericParams = GenericParams(None);
static EMPTY_TYPE_OR_CONSTS: Arena<TypeOrConstParamData> = Arena::new();
static EMPTY_LIFETIMES: Arena<LifetimeParamData> = Arena::new();

impl PartialEq for GenericParams {
    fn eq(&self, other: &Self) -> bool {
        self.type_or_consts() == other.type_or_consts()
            && self.lifetimes() == other.lifetimes()
            && self.where_predicates() == other.where_predicates()
    }
}

impl Eq for GenericParams {}

impl Hash for GenericParams {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.type_or_consts().hash(state);
        self.lifetimes().hash(state);
        self.where_predicates().hash(state);
    }
}

impl fmt::Debug for GenericParams {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("GenericParams")
            .field("type_or_consts", self.type_or_consts())
            .field("lifetimes", self.lifetimes())
            .field("where_predicates", &self.where_predicates())
            .finish()
    }
}

impl ops::Index<LocalTypeOrConstParamId> for GenericParams {
    type Output = TypeOrConstParamData;
    fn index(&self, index: LocalTypeOrConstParamId) -> &TypeOrConstParamData {
        &self.type_or_consts()[index]
    }
}

impl ops::Index<LocalLifetimeParamId> for GenericParams {
    type Output = LifetimeParamData;
    fn index(&self, index: LocalLifetimeParamId) -> &LifetimeParamData {
        &self.lifetimes()[index]
    }
}

/// A single predicate from a where clause, i.e. `where Type: Trait`. Combined
/// where clauses like `where T: Foo + Bar` are turned into multiple of these.
/// It might still result in multiple actual predicates though, because of
/// associated type bindings like `Iterator<Item = u32>`.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum WherePredicate {
    TypeBound { lifetimes: Option<ThinVec<Name>>, target: TypeRefId, bound: TypeBound },
    Lifetime { target: LifetimeRefId, bound: LifetimeRefId },
}

impl GenericParams {
    /// The index of the self param in the generic of the non-parent definition.
    pub const SELF_PARAM_ID_IN_SELF: la_arena::Idx<TypeOrConstParamData> =
        LocalTypeOrConstParamId::from_raw(RawIdx::from_u32(0));

    #[inline]
    pub fn empty() -> &'static GenericParams {
        &EMPTY
    }

    pub(crate) fn new(
        type_or_consts: Arena<TypeOrConstParamData>,
        lifetimes: Arena<LifetimeParamData>,
        where_predicates: Box<[WherePredicate]>,
    ) -> Self {
        if type_or_consts.is_empty() && lifetimes.is_empty() && where_predicates.is_empty() {
            Self(None)
        } else {
            Self(Some(Box::new(GenericParamsData { type_or_consts, lifetimes, where_predicates })))
        }
    }

    fn type_or_consts(&self) -> &Arena<TypeOrConstParamData> {
        self.0.as_deref().map_or(&EMPTY_TYPE_OR_CONSTS, |data| &data.type_or_consts)
    }

    fn lifetimes(&self) -> &Arena<LifetimeParamData> {
        self.0.as_deref().map_or(&EMPTY_LIFETIMES, |data| &data.lifetimes)
    }

    pub fn of(db: &dyn SourceDatabase, def: GenericDefId) -> &GenericParams {
        Self::with_store(db, def).0
    }

    pub fn with_store(
        db: &dyn SourceDatabase,
        def: GenericDefId,
    ) -> (&GenericParams, &ExpressionStore) {
        match def {
            GenericDefId::AdtId(AdtId::EnumId(id)) => {
                let sig = EnumSignature::of(db, id);
                (&sig.generic_params, &sig.store)
            }
            GenericDefId::AdtId(AdtId::StructId(id)) => {
                let sig = StructSignature::of(db, id);
                (&sig.generic_params, &sig.store)
            }
            GenericDefId::AdtId(AdtId::UnionId(id)) => {
                let sig = UnionSignature::of(db, id);
                (&sig.generic_params, &sig.store)
            }
            GenericDefId::ConstId(id) => {
                let sig = ConstSignature::of(db, id);
                (&EMPTY, &sig.store)
            }
            GenericDefId::FunctionId(id) => {
                let sig = FunctionSignature::of(db, id);
                (&sig.generic_params, &sig.store)
            }
            GenericDefId::ImplId(id) => {
                let sig = ImplSignature::of(db, id);
                (&sig.generic_params, &sig.store)
            }
            GenericDefId::StaticId(id) => {
                let sig = StaticSignature::of(db, id);
                (&EMPTY, &sig.store)
            }
            GenericDefId::TraitId(id) => {
                let sig = TraitSignature::of(db, id);
                (&sig.generic_params, &sig.store)
            }
            GenericDefId::TypeAliasId(id) => {
                let sig = TypeAliasSignature::of(db, id);
                (&sig.generic_params, &sig.store)
            }
        }
    }

    pub fn with_source_map(
        db: &dyn SourceDatabase,
        def: GenericDefId,
    ) -> (&GenericParams, &ExpressionStore, &ExpressionStoreSourceMap) {
        match def {
            GenericDefId::AdtId(AdtId::EnumId(id)) => {
                let (sig, sm) = EnumSignature::with_source_map(db, id);
                (&sig.generic_params, &sig.store, sm)
            }
            GenericDefId::AdtId(AdtId::StructId(id)) => {
                let (sig, sm) = StructSignature::with_source_map(db, id);
                (&sig.generic_params, &sig.store, sm)
            }
            GenericDefId::AdtId(AdtId::UnionId(id)) => {
                let (sig, sm) = UnionSignature::with_source_map(db, id);
                (&sig.generic_params, &sig.store, sm)
            }
            GenericDefId::ConstId(id) => {
                let (sig, sm) = ConstSignature::with_source_map(db, id);
                (&EMPTY, &sig.store, sm)
            }
            GenericDefId::FunctionId(id) => {
                let (sig, sm) = FunctionSignature::with_source_map(db, id);
                (&sig.generic_params, &sig.store, sm)
            }
            GenericDefId::ImplId(id) => {
                let (sig, sm) = ImplSignature::with_source_map(db, id);
                (&sig.generic_params, &sig.store, sm)
            }
            GenericDefId::StaticId(id) => {
                let (sig, sm) = StaticSignature::with_source_map(db, id);
                (&EMPTY, &sig.store, sm)
            }
            GenericDefId::TraitId(id) => {
                let (sig, sm) = TraitSignature::with_source_map(db, id);
                (&sig.generic_params, &sig.store, sm)
            }
            GenericDefId::TypeAliasId(id) => {
                let (sig, sm) = TypeAliasSignature::with_source_map(db, id);
                (&sig.generic_params, &sig.store, sm)
            }
        }
    }

    /// Number of Generic parameters (type_or_consts + lifetimes)
    #[inline]
    pub fn len(&self) -> usize {
        self.type_or_consts().len() + self.lifetimes().len()
    }

    #[inline]
    pub fn len_lifetimes(&self) -> usize {
        self.lifetimes().len() - self.len_late_bound_lifetimes()
    }

    #[inline]
    pub fn len_late_bound_lifetimes(&self) -> usize {
        self.lifetimes()
            .iter()
            .filter(|(_, p)| p.bound_type == LifetimeBoundType::LateBound)
            .count()
    }

    #[inline]
    pub fn len_type_or_consts(&self) -> usize {
        self.type_or_consts().len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn has_no_predicates(&self) -> bool {
        self.where_predicates().is_empty()
    }

    #[inline]
    pub fn where_predicates(&self) -> &[WherePredicate] {
        self.0.as_deref().map_or(&[], |data| &data.where_predicates)
    }

    /// Iterator of type_or_consts field
    #[inline]
    pub fn iter_type_or_consts(
        &self,
    ) -> impl DoubleEndedIterator<Item = (LocalTypeOrConstParamId, &TypeOrConstParamData)> {
        self.type_or_consts().iter()
    }

    /// Iterator of lifetimes field
    #[inline]
    pub fn iter_lt(
        &self,
    ) -> impl DoubleEndedIterator<Item = (LocalLifetimeParamId, &LifetimeParamData)> {
        self.lifetimes().iter()
    }

    #[inline]
    pub fn iter_early_bound_lt(
        &self,
    ) -> impl DoubleEndedIterator<Item = (LocalLifetimeParamId, &LifetimeParamData)> {
        self.lifetimes().iter().filter(|(_, p)| p.bound_type == LifetimeBoundType::EarlyBound)
    }

    #[inline]
    pub fn iter_late_bound_lt(
        &self,
    ) -> impl DoubleEndedIterator<Item = (LocalLifetimeParamId, &LifetimeParamData)> {
        self.lifetimes().iter().filter(|(_, p)| p.bound_type == LifetimeBoundType::LateBound)
    }

    pub fn find_type_by_name(&self, name: &Name, parent: GenericDefId) -> Option<TypeParamId> {
        self.type_or_consts().iter().find_map(|(id, p)| {
            if p.name().as_ref() == Some(&name) && p.type_param().is_some() {
                Some(TypeParamId::from_unchecked(TypeOrConstParamId { local_id: id, parent }))
            } else {
                None
            }
        })
    }

    pub fn find_const_by_name(&self, name: &Name, parent: GenericDefId) -> Option<ConstParamId> {
        self.type_or_consts().iter().find_map(|(id, p)| {
            if p.name().as_ref() == Some(&name) && p.const_param().is_some() {
                Some(ConstParamId::from_unchecked(TypeOrConstParamId { local_id: id, parent }))
            } else {
                None
            }
        })
    }

    #[inline]
    pub fn trait_self_param(&self) -> Option<LocalTypeOrConstParamId> {
        if self.type_or_consts().is_empty() {
            return None;
        }
        matches!(
            self.type_or_consts()[Self::SELF_PARAM_ID_IN_SELF],
            TypeOrConstParamData::TypeParamData(TypeParamData {
                provenance: TypeParamProvenance::TraitSelf,
                ..
            })
        )
        .then(|| Self::SELF_PARAM_ID_IN_SELF)
    }

    pub fn find_lifetime_by_name(
        &self,
        name: &Name,
        parent: GenericDefId,
    ) -> Option<LifetimeParamId> {
        self.lifetimes().iter().find_map(|(id, p)| {
            if &p.name == name { Some(LifetimeParamId { local_id: id, parent }) } else { None }
        })
    }

    pub fn lifetime_param_idx(
        &self,
        lifetime_param_id: &LocalLifetimeParamId,
    ) -> Option<(usize, bool)> {
        let mut late_bound_idx = 0;
        self.iter_lt().enumerate().find_map(|(idx, (param_id, param_data))| {
            let idx = if param_data.is_late_bound() {
                let prev = late_bound_idx;
                late_bound_idx += 1;
                prev
            } else {
                idx - late_bound_idx
            };

            (param_id == *lifetime_param_id).then(|| (idx, param_data.is_late_bound()))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn generic_params_are_one_pointer_when_empty() {
        assert_eq!(std::mem::size_of::<GenericParams>(), 8);
        assert!(GenericParams::default().is_empty());
        assert!(GenericParams::default().has_no_predicates());
    }

    #[test]
    fn nonempty_generic_params_preserve_ids_and_iteration() {
        let type_name = Name::new_symbol_root(intern::Symbol::intern("Type"));
        let lifetime_name = Name::new_symbol_root(intern::Symbol::intern("lifetime"));
        let mut type_or_consts = Arena::new();
        let type_id = type_or_consts.alloc(
            TypeParamData {
                name: Some(type_name.clone()),
                default: None,
                provenance: TypeParamProvenance::TypeParamList,
            }
            .into(),
        );
        let mut lifetimes = Arena::new();
        let lifetime_id = lifetimes.alloc(LifetimeParamData {
            name: lifetime_name.clone(),
            bound_type: LifetimeBoundType::EarlyBound,
        });

        let params = GenericParams::new(type_or_consts, lifetimes, Box::new([]));

        assert_eq!(params.len(), 2);
        assert_eq!(params[type_id].name(), Some(&type_name));
        assert_eq!(params[lifetime_id].name, lifetime_name);
        assert_eq!(params.iter_type_or_consts().map(|(id, _)| id).collect::<Vec<_>>(), [type_id]);
        assert_eq!(params.iter_lt().map(|(id, _)| id).collect::<Vec<_>>(), [lifetime_id]);
    }
}
