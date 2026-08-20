use std::fmt;
use std::ops::Deref;

use rustc_data_structures::intern::Interned;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::find_attr;
use rustc_macros::StableHash;
use rustc_type_ir::{Flags, TypeFlags};

use super::{self as ty, Pattern, PatternKind, Ty, TyCtxt};

pub type RefinementDefinition<'tcx> = rustc_type_ir::RefinementDefinition<TyCtxt<'tcx>>;

#[derive(Clone, Copy, PartialEq, Eq, Hash, StableHash)]
#[rustc_pass_by_value]
pub struct RefinementTypeKey<'tcx>(pub Interned<'tcx, RefinementDefinition<'tcx>>);

impl<'tcx> Deref for RefinementTypeKey<'tcx> {
    type Target = RefinementDefinition<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<'tcx> rustc_type_ir::inherent::IntoKind for RefinementTypeKey<'tcx> {
    type Kind = RefinementDefinition<'tcx>;

    fn kind(self) -> Self::Kind {
        *self
    }
}

impl fmt::Debug for RefinementTypeKey<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}
impl fmt::Display for RefinementTypeKey<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match **self {
            RefinementDefinition::Pattern(pattern) => fmt::Display::fmt(&*pattern, f),
            RefinementDefinition::Constructor { variant_def_id } => {
                crate::ty::tls::with(|tcx| write!(f, "{}", tcx.def_path_str(variant_def_id)))
            }
        }
    }
}

impl Flags for RefinementTypeKey<'_> {
    fn flags(&self) -> TypeFlags {
        match **self {
            RefinementDefinition::Pattern(pattern) => pattern.flags(),
            RefinementDefinition::Constructor { .. } => TypeFlags::empty(),
        }
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        match **self {
            RefinementDefinition::Pattern(pattern) => pattern.outer_exclusive_binder(),
            RefinementDefinition::Constructor { .. } => rustc_type_ir::INNERMOST,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefinementLayoutAuthority<'tcx> {
    ScalarPattern(Pattern<'tcx>),
    BaseRepresentation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownConstructor {
    None,
    Variant(DefId),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefinementTypeIdentity<'tcx> {
    Pattern(Pattern<'tcx>),
    Constructor(DefId),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefinementTypeInvariant<'tcx> {
    ScalarPattern(Pattern<'tcx>),
    ExactConstructor(DefId),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactConstructorType<'tcx> {
    pub base: Ty<'tcx>,
    pub variant_def_id: DefId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefinementUnsizeKind {
    TransparentBase,
    Unsupported,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefinementConversion<'tcx> {
    Identity,
    ForgetExactConstructor,
    ForgetSharedExactConstructor { relation_source: Ty<'tcx> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefinementImplHead<'tcx> {
    ExactConstructor { base: Ty<'tcx>, owner: DefId },
    Pattern { base: Ty<'tcx> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefinementJoinConversion {
    Identity,
    ForgetExactConstructor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RefinementJoin<'tcx> {
    pub target: Ty<'tcx>,
    pub left: RefinementJoinConversion,
    pub right: RefinementJoinConversion,
}

impl<'tcx> TyCtxt<'tcx> {
    pub fn refinement_for_pattern(self, pattern: Pattern<'tcx>) -> RefinementTypeKey<'tcx> {
        self.intern_refinement_definition(RefinementDefinition::Pattern(pattern))
    }

    pub fn refinement_for_constructor(self, variant_def_id: DefId) -> RefinementTypeKey<'tcx> {
        if self.def_kind(variant_def_id) != DefKind::Variant {
            bug!("constructor refinement requested for non-variant {variant_def_id:?}");
        }
        self.intern_refinement_definition(RefinementDefinition::Constructor { variant_def_id })
    }

    pub fn exact_variant_ty(self, base: Ty<'tcx>, variant_def_id: DefId) -> Ty<'tcx> {
        if self.def_kind(variant_def_id) != DefKind::Variant {
            bug!("exact variant type requested for non-variant {variant_def_id:?}");
        }
        let family_def_id = self.parent(variant_def_id);
        let ty::Adt(adt_def, _) = *base.kind() else {
            bug!("exact variant base was not an ADT: {base:?}");
        };
        if adt_def.did() != family_def_id {
            bug!(
                "exact variant {:?} belongs to {}, but base type was {}",
                variant_def_id,
                self.def_path_str(family_def_id),
                base
            );
        }
        Ty::new_refined(self, base, self.refinement_for_constructor(variant_def_id))
    }

    pub fn enum_preserves_exact_variants(self, enum_def_id: DefId) -> bool {
        self.def_kind(enum_def_id) == DefKind::Enum
            && find_attr!(self, enum_def_id, ExactVariants(..))
    }
    pub fn enum_refinement_is_representation_uniform(self, enum_def_id: DefId) -> bool {
        if self.def_kind(enum_def_id) != DefKind::Enum {
            return true;
        }
        let identity = self.type_of(enum_def_id).instantiate_identity().skip_norm_wip();
        self.adt_def(enum_def_id).variants().iter().all(|variant| {
            match self.variant_scheme(variant.def_id) {
                ty::VariantScheme::Ordinary => true,
                ty::VariantScheme::Refined(scheme) => scheme.result == identity,
                ty::VariantScheme::Invalid(_) => false,
            }
        })
    }

    pub fn exact_constructor_type(self, ty: Ty<'tcx>) -> Option<ExactConstructorType<'tcx>> {
        let ty::Refined(base, refinement) = *ty.kind() else {
            return None;
        };
        let RefinementTypeInvariant::ExactConstructor(variant_def_id) =
            self.refinement_type_invariant(refinement)
        else {
            return None;
        };
        Some(ExactConstructorType { base, variant_def_id })
    }
    pub fn refinement_forget_target(self, source: Ty<'tcx>) -> Option<Ty<'tcx>> {
        if let Some(exact) = self.exact_constructor_type(source) {
            return Some(exact.base);
        }
        let ty::Ref(region, pointee, rustc_hir::Mutability::Not) = *source.kind() else {
            return None;
        };
        let exact = self.exact_constructor_type(pointee)?;
        Some(Ty::new_ref(self, region, exact.base, rustc_hir::Mutability::Not))
    }

    pub fn refinement_construction_variant(
        self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
    ) -> Option<DefId> {
        let exact = self.exact_constructor_type(target)?;
        (exact.base == source).then_some(exact.variant_def_id)
    }

    pub fn refinement_impl_head(self, ty: Ty<'tcx>) -> Option<RefinementImplHead<'tcx>> {
        let ty::Refined(base, refinement) = *ty.kind() else {
            return None;
        };
        match self.refinement_type_invariant(refinement) {
            RefinementTypeInvariant::ExactConstructor(_) => {
                let ty::Adt(def, _) = *base.kind() else {
                    bug!("exact constructor refinement had non-ADT base {base:?}");
                };
                Some(RefinementImplHead::ExactConstructor { base, owner: def.did() })
            }
            RefinementTypeInvariant::ScalarPattern(_) => Some(RefinementImplHead::Pattern { base }),
        }
    }

    pub fn refinement_conversion(
        self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
    ) -> Option<RefinementConversion<'tcx>> {
        if source == target {
            return Some(RefinementConversion::Identity);
        }
        if self.exact_constructor_type(source).is_some_and(|exact| exact.base == target) {
            return Some(RefinementConversion::ForgetExactConstructor);
        }
        let (
            ty::Ref(source_region, source_pointee, rustc_hir::Mutability::Not),
            ty::Ref(_, target_pointee, rustc_hir::Mutability::Not),
        ) = (*source.kind(), *target.kind())
        else {
            return None;
        };
        let exact = self.exact_constructor_type(source_pointee)?;
        if exact.base != target_pointee {
            return None;
        }
        Some(RefinementConversion::ForgetSharedExactConstructor {
            relation_source: Ty::new_ref(
                self,
                source_region,
                exact.base,
                rustc_hir::Mutability::Not,
            ),
        })
    }

    pub fn refinement_join(self, left: Ty<'tcx>, right: Ty<'tcx>) -> Option<RefinementJoin<'tcx>> {
        if left == right {
            return Some(RefinementJoin {
                target: left,
                left: RefinementJoinConversion::Identity,
                right: RefinementJoinConversion::Identity,
            });
        }

        let left_base = self.exact_constructor_type(left).map(|exact| exact.base);
        let right_base = self.exact_constructor_type(right).map(|exact| exact.base);

        match (left_base, right_base) {
            (Some(left_base), Some(right_base)) if left_base == right_base => {
                Some(RefinementJoin {
                    target: left_base,
                    left: RefinementJoinConversion::ForgetExactConstructor,
                    right: RefinementJoinConversion::ForgetExactConstructor,
                })
            }
            (Some(left_base), None) if left_base == right => Some(RefinementJoin {
                target: right,
                left: RefinementJoinConversion::ForgetExactConstructor,
                right: RefinementJoinConversion::Identity,
            }),
            (None, Some(right_base)) if left == right_base => Some(RefinementJoin {
                target: left,
                left: RefinementJoinConversion::Identity,
                right: RefinementJoinConversion::ForgetExactConstructor,
            }),
            _ => None,
        }
    }
    pub fn refinement_type_identity(
        self,
        key: RefinementTypeKey<'tcx>,
    ) -> RefinementTypeIdentity<'tcx> {
        match *key {
            RefinementDefinition::Pattern(pattern) => RefinementTypeIdentity::Pattern(pattern),
            RefinementDefinition::Constructor { variant_def_id } => {
                RefinementTypeIdentity::Constructor(variant_def_id)
            }
        }
    }
    pub fn refinement_type_invariant(
        self,
        key: RefinementTypeKey<'tcx>,
    ) -> RefinementTypeInvariant<'tcx> {
        match *key {
            RefinementDefinition::Pattern(pattern) => {
                RefinementTypeInvariant::ScalarPattern(pattern)
            }
            RefinementDefinition::Constructor { variant_def_id } => {
                RefinementTypeInvariant::ExactConstructor(variant_def_id)
            }
        }
    }
    pub fn refinement_unsize_kind(self, key: RefinementTypeKey<'tcx>) -> RefinementUnsizeKind {
        match *key {
            RefinementDefinition::Pattern(pattern) if matches!(*pattern, PatternKind::NotNull) => {
                RefinementUnsizeKind::TransparentBase
            }
            RefinementDefinition::Pattern(_) | RefinementDefinition::Constructor { .. } => {
                RefinementUnsizeKind::Unsupported
            }
        }
    }

    pub fn refinement_layout_authority(
        self,
        key: RefinementTypeKey<'tcx>,
    ) -> RefinementLayoutAuthority<'tcx> {
        match *key {
            RefinementDefinition::Pattern(pattern) => {
                RefinementLayoutAuthority::ScalarPattern(pattern)
            }
            RefinementDefinition::Constructor { .. } => {
                RefinementLayoutAuthority::BaseRepresentation
            }
        }
    }

    pub fn refinement_known_constructor(self, key: RefinementTypeKey<'tcx>) -> KnownConstructor {
        match *key {
            RefinementDefinition::Pattern(_) => KnownConstructor::None,
            RefinementDefinition::Constructor { variant_def_id } => {
                KnownConstructor::Variant(variant_def_id)
            }
        }
    }
}
