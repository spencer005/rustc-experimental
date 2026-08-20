//! Constraint construction and representation
//!
//! The second pass over the HIR determines the set of constraints.
//! We walk the set of items and, for each member, generate new constraints.

use hir::def_id::{DefId, LocalDefId};
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, GenericArgKind, GenericArgsRef, Ty, TyCtxt};
use rustc_middle::{bug, span_bug};
use tracing::{debug, instrument};

use super::terms::VarianceTerm::*;
use super::terms::*;

pub(crate) struct ConstraintContext<'a, 'tcx> {
    pub terms_cx: TermsContext<'a, 'tcx>,

    // These are pointers to common `ConstantTerm` instances
    covariant: VarianceTermPtr<'a>,
    contravariant: VarianceTermPtr<'a>,
    invariant: VarianceTermPtr<'a>,
    bivariant: VarianceTermPtr<'a>,

    pub constraints: Vec<Constraint<'a>>,
}

/// Declares that the variable `decl_id` appears in a location with
/// variance `variance`.
#[derive(Copy, Clone)]
pub(crate) struct Constraint<'a> {
    pub inferred: InferredIndex,
    pub variance: &'a VarianceTerm<'a>,
}

/// To build constraints, we visit one item (type, trait) at a time
/// and look at its contents. So e.g., if we have
/// ```ignore (illustrative)
/// struct Foo<T> {
///     b: Bar<T>
/// }
/// ```
/// then while we are visiting `Bar<T>`, the `CurrentItem` would have
/// the `DefId` and the start of `Foo`'s inferreds.
struct CurrentItem {
    inferred_start: InferredIndex,
    param_index_map: Option<Vec<Option<u32>>>,
}

pub(crate) fn add_constraints_from_crate<'a, 'tcx>(
    terms_cx: TermsContext<'a, 'tcx>,
) -> ConstraintContext<'a, 'tcx> {
    let tcx = terms_cx.tcx;
    let covariant = terms_cx.arena.alloc(ConstantTerm(ty::Covariant));
    let contravariant = terms_cx.arena.alloc(ConstantTerm(ty::Contravariant));
    let invariant = terms_cx.arena.alloc(ConstantTerm(ty::Invariant));
    let bivariant = terms_cx.arena.alloc(ConstantTerm(ty::Bivariant));
    let mut constraint_cx = ConstraintContext {
        terms_cx,
        covariant,
        contravariant,
        invariant,
        bivariant,
        constraints: Vec::new(),
    };

    let crate_items = tcx.hir_crate_items(());

    for def_id in crate_items.definitions() {
        let def_kind = tcx.def_kind(def_id);
        match def_kind {
            DefKind::Struct | DefKind::Union | DefKind::Enum => {
                constraint_cx.build_constraints_for_item(def_id);

                let adt = tcx.adt_def(def_id);
                for variant in adt.variants() {
                    if let Some(ctor_def_id) = variant.ctor_def_id() {
                        constraint_cx.build_constraints_for_item(ctor_def_id.expect_local());
                    }
                }
            }
            DefKind::Fn | DefKind::AssocFn => constraint_cx.build_constraints_for_item(def_id),
            _ => {}
        }
    }

    constraint_cx
}

impl<'a, 'tcx> ConstraintContext<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.terms_cx.tcx
    }

    fn refined_variant_family_index_map(
        &self,
        family_def_id: LocalDefId,
        variant_def_id: LocalDefId,
    ) -> Vec<Option<u32>> {
        let tcx = self.tcx();
        let family_generics = tcx.generics_of(family_def_id);
        let binders = tcx.variant_binder_scheme(variant_def_id);
        binders
            .family
            .iter()
            .map(|scheme_param| {
                family_generics
                    .own_params
                    .iter()
                    .find(|family_param| family_param.def_id == scheme_param.def_id)
                    .map(|family_param| family_param.index)
            })
            .chain(std::iter::repeat_n(None, binders.local.len()))
            .collect()
    }

    fn scheme_arg_is_family_param(
        &self,
        arg: ty::GenericArg<'tcx>,
        scheme: &ty::RefinedVariantScheme<'tcx>,
        family_param: &ty::GenericParamDef,
    ) -> bool {
        let Some(scheme_param) = scheme
            .binders
            .family
            .iter()
            .find(|scheme_param| scheme_param.def_id == family_param.def_id)
        else {
            return false;
        };

        match (arg.kind(), &scheme_param.kind) {
            (GenericArgKind::Type(ty), ty::GenericParamDefKind::Type { .. }) => {
                matches!(*ty.kind(), ty::Param(param) if param.index == scheme_param.index)
            }
            (
                GenericArgKind::Lifetime(region),
                ty::GenericParamDefKind::Lifetime | ty::GenericParamDefKind::OriginLifetime,
            ) => matches!(region.kind(), ty::ReEarlyParam(param) if param.index == scheme_param.index),
            (GenericArgKind::Const(ct), ty::GenericParamDefKind::Const { .. }) => {
                matches!(ct.kind(), ty::ConstKind::Param(param) if param.index == scheme_param.index)
            }
            _ => false,
        }
    }

    fn refined_result_preserves_family_param(
        &self,
        family_def_id: LocalDefId,
        variant_def_id: LocalDefId,
        family_param_position: usize,
        family_param: &ty::GenericParamDef,
    ) -> bool {
        let tcx = self.tcx();
        let ty::VariantScheme::Refined(scheme) = tcx.variant_scheme(variant_def_id) else {
            return false;
        };
        let ty::Adt(result_def, result_args) = *scheme.result.kind() else {
            return false;
        };
        if result_def.did() != family_def_id.to_def_id() {
            return false;
        }
        let Some(&arg) = result_args.get(family_param_position) else {
            return false;
        };
        self.scheme_arg_is_family_param(arg, scheme, family_param)
    }

    fn add_refined_result_variance_floor(
        &mut self,
        family_def_id: LocalDefId,
        current_item: &CurrentItem,
    ) {
        let tcx = self.tcx();
        let family_generics = tcx.generics_of(family_def_id);
        let variants = tcx.adt_def(family_def_id).variants();
        for (position, family_param) in family_generics.own_params.iter().enumerate() {
            let uniform = variants.iter().all(|variant| {
                let Some(variant_def_id) = variant.def_id.as_local() else {
                    return false;
                };
                self.refined_result_preserves_family_param(
                    family_def_id,
                    variant_def_id,
                    position,
                    family_param,
                )
            });
            if !uniform {
                self.add_constraint(current_item, family_param.index, self.invariant);
            }
        }
    }

    fn build_constraints_for_item(&mut self, def_id: LocalDefId) {
        let tcx = self.tcx();
        debug!("build_constraints_for_item({})", tcx.def_path_str(def_id));

        // Skip items with no generics - there's nothing to infer in them.
        if tcx.generics_of(def_id).is_empty() {
            return;
        }

        let inferred_start = self.terms_cx.inferred_starts[&def_id];
        let current_item = &CurrentItem { inferred_start, param_index_map: None };
        let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
        let ty = tcx.exact_constructor_type(ty).map_or(ty, |exact| exact.base);

        match ty.kind() {
            ty::Adt(def, _) => {
                // Not entirely obvious: constraints on structs/enums do not
                // affect the variance of their type parameters. See discussion
                // in comment at top of module.
                //
                // self.add_constraints_from_generics(generics);

                match tcx.hir_node_by_def_id(def_id) {
                    hir::Node::Item(item) => {
                        let hir::ItemKind::Enum(_, _, enum_def) = item.kind else {
                            for field in def.all_fields() {
                                self.add_constraints_from_ty(
                                    current_item,
                                    tcx.type_of(field.did).instantiate_identity().skip_norm_wip(),
                                    self.covariant,
                                );
                            }
                            return;
                        };

                        for variant in def.variants() {
                            let variant_def_id = variant.def_id.expect_local();
                            let hir::Node::Variant(hir_variant) =
                                tcx.hir_node_by_def_id(variant_def_id)
                            else {
                                span_bug!(
                                    tcx.def_span(variant_def_id),
                                    "variant DefId did not map to HIR"
                                )
                            };
                            match hir_variant.scheme {
                                hir::VariantSchemeSyntax::Ordinary => {
                                    for field in &variant.fields {
                                        self.add_constraints_from_ty(
                                            current_item,
                                            tcx.type_of(field.did)
                                                .instantiate_identity()
                                                .skip_norm_wip(),
                                            self.covariant,
                                        );
                                    }
                                }
                                hir::VariantSchemeSyntax::Refined { .. } => {
                                    let mapped_item = CurrentItem {
                                        inferred_start,
                                        param_index_map: Some(
                                            self.refined_variant_family_index_map(
                                                def_id,
                                                variant_def_id,
                                            ),
                                        ),
                                    };
                                    for field in &variant.fields {
                                        self.add_constraints_from_ty(
                                            &mapped_item,
                                            tcx.type_of(field.did)
                                                .instantiate_identity()
                                                .skip_norm_wip(),
                                            self.covariant,
                                        );
                                    }
                                }
                            }
                        }
                        if enum_def
                            .variants
                            .iter()
                            .any(|variant| matches!(variant.scheme, hir::VariantSchemeSyntax::Refined { .. }))
                        {
                            self.add_refined_result_variance_floor(def_id, current_item);
                        }

                    }
                    hir::Node::Ctor(_) => {
                        for field in def.all_fields() {
                            self.add_constraints_from_ty(
                                current_item,
                                tcx.type_of(field.did).instantiate_identity().skip_norm_wip(),
                                self.covariant,
                            );
                        }
                    }
                    node => span_bug!(
                        tcx.def_span(def_id),
                        "ADT-typed definition had unexpected HIR node {node:?}"
                    ),
                }
                return;
            }


            ty::FnDef(..) => {
                self.add_constraints_from_sig(
                    current_item,
                    tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip(),
                    self.covariant,
                );
            }

            ty::Error(_) => {}

            _ => {
                span_bug!(
                    tcx.def_span(def_id),
                    "`build_constraints_for_item` unsupported for this item"
                );
            }
        }
    }

    fn add_constraint(&mut self, current: &CurrentItem, index: u32, variance: VarianceTermPtr<'a>) {
        let index = match &current.param_index_map {
            Some(map) => match map.get(index as usize).copied().flatten() {
                Some(index) => index,
                None => return,
            },
            None => index,
        };
        debug!("add_constraint(index={}, variance={:?})", index, variance);
        self.constraints.push(Constraint {
            inferred: InferredIndex(current.inferred_start.0 + index as usize),
            variance,
        });
    }

    fn contravariant(&mut self, variance: VarianceTermPtr<'a>) -> VarianceTermPtr<'a> {
        self.xform(variance, self.contravariant)
    }

    fn invariant(&mut self, variance: VarianceTermPtr<'a>) -> VarianceTermPtr<'a> {
        self.xform(variance, self.invariant)
    }

    fn constant_term(&self, v: ty::Variance) -> VarianceTermPtr<'a> {
        match v {
            ty::Covariant => self.covariant,
            ty::Invariant => self.invariant,
            ty::Contravariant => self.contravariant,
            ty::Bivariant => self.bivariant,
        }
    }

    fn xform(&mut self, v1: VarianceTermPtr<'a>, v2: VarianceTermPtr<'a>) -> VarianceTermPtr<'a> {
        match (*v1, *v2) {
            (_, ConstantTerm(ty::Covariant)) => {
                // Applying a "covariant" transform is always a no-op
                v1
            }

            (ConstantTerm(c1), ConstantTerm(c2)) => self.constant_term(c1.xform(c2)),

            _ => &*self.terms_cx.arena.alloc(TransformTerm(v1, v2)),
        }
    }

    #[instrument(level = "debug", skip(self, current))]
    fn add_constraints_from_invariant_args(
        &mut self,
        current: &CurrentItem,
        args: GenericArgsRef<'tcx>,
        variance: VarianceTermPtr<'a>,
    ) {
        // Trait are always invariant so we can take advantage of that.
        let variance_i = self.invariant(variance);

        for arg in args {
            match arg.kind() {
                GenericArgKind::Lifetime(lt) => {
                    self.add_constraints_from_region(current, lt, variance_i)
                }
                GenericArgKind::Type(ty) => self.add_constraints_from_ty(current, ty, variance_i),
                GenericArgKind::Const(val) => {
                    self.add_constraints_from_const(current, val, variance_i)
                }
            }
        }
    }

    /// Adds constraints appropriate for an instance of `ty` appearing
    /// in a context with the generics defined in `generics` and
    /// ambient variance `variance`
    #[instrument(level = "debug", skip(self, current))]
    fn add_constraints_from_ty(
        &mut self,
        current: &CurrentItem,
        ty: Ty<'tcx>,
        variance: VarianceTermPtr<'a>,
    ) {
        match *ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Foreign(..) => {
                // leaf type -- noop
            }

            ty::FnDef(..) | ty::Coroutine(..) | ty::Closure(..) | ty::CoroutineClosure(..) => {
                bug!("Unexpected unnameable type in variance computation: {ty}");
            }

            ty::Ref(region, ty, mutbl) => {
                self.add_constraints_from_region(current, region, variance);
                self.add_constraints_from_mt(current, &ty::TypeAndMut { ty, mutbl }, variance);
            }

            ty::Array(typ, len) => {
                self.add_constraints_from_const(current, len, variance);
                self.add_constraints_from_ty(current, typ, variance);
            }

            ty::Refined(typ, refinement) => {
                if let ty::RefinementTypeInvariant::ScalarPattern(pattern) =
                    self.tcx().refinement_type_invariant(refinement)
                {
                    self.add_constraints_from_pat(current, variance, pattern);
                }
                self.add_constraints_from_ty(current, typ, variance);
            }

            ty::Slice(typ) => {
                self.add_constraints_from_ty(current, typ, variance);
            }

            ty::RawPtr(ty, mutbl) => {
                self.add_constraints_from_mt(current, &ty::TypeAndMut { ty, mutbl }, variance);
            }

            ty::Tuple(subtys) => {
                for subty in subtys {
                    self.add_constraints_from_ty(current, subty, variance);
                }
            }

            ty::Adt(def, args) => {
                self.add_constraints_from_args(current, def.did(), args, variance);
            }

            ty::Alias(
                _,
                ty::AliasTy {
                    kind: ty::Projection { .. } | ty::Inherent { .. } | ty::Opaque { .. },
                    args,
                    ..
                },
            ) => {
                self.add_constraints_from_invariant_args(current, args, variance);
            }

            ty::Alias(_, ty::AliasTy { kind: ty::Free { .. }, .. }) => {
                let ty = self.tcx().expand_free_alias_tys(ty);
                self.add_constraints_from_ty(current, ty, variance);
            }

            ty::Dynamic(data, r) => {
                // The type `dyn Trait<T> +'a` is covariant w/r/t `'a`:
                self.add_constraints_from_region(current, r, variance);

                if let Some(poly_trait_ref) = data.principal() {
                    self.add_constraints_from_invariant_args(
                        current,
                        poly_trait_ref.skip_binder().args,
                        variance,
                    );
                }

                for projection in data.projection_bounds() {
                    match projection.skip_binder().term.kind() {
                        ty::TermKind::Ty(ty) => {
                            self.add_constraints_from_ty(current, ty, self.invariant);
                        }
                        ty::TermKind::Const(c) => {
                            self.add_constraints_from_const(current, c, self.invariant)
                        }
                    }
                }
            }

            ty::Param(ref data) => {
                self.add_constraint(current, data.index, variance);
            }

            ty::FnPtr(sig_tys, hdr) => {
                self.add_constraints_from_sig(current, sig_tys.with(hdr), variance);
            }

            ty::UnsafeBinder(ty) => {
                // FIXME(unsafe_binders): This is covariant, right?
                self.add_constraints_from_ty(current, ty.skip_binder(), variance);
            }

            ty::Error(_) => {
                // we encounter this when walking the trait references for object
                // types, where we use Error as the Self type
            }

            ty::Placeholder(..) | ty::CoroutineWitness(..) | ty::Bound(..) | ty::Infer(..) => {
                bug!("unexpected type encountered in variance inference: {}", ty);
            }
        }
    }

    fn add_constraints_from_pat(
        &mut self,
        current: &CurrentItem,
        variance: VarianceTermPtr<'a>,
        pat: ty::Pattern<'tcx>,
    ) {
        match *pat {
            ty::PatternKind::Range { start, end } => {
                self.add_constraints_from_const(current, start, variance);
                self.add_constraints_from_const(current, end, variance);
            }
            ty::PatternKind::NotNull => {}
            ty::PatternKind::Or(patterns) => {
                for pat in patterns {
                    self.add_constraints_from_pat(current, variance, pat)
                }
            }
        }
    }

    /// Adds constraints appropriate for a nominal type (enum, struct,
    /// object, etc) appearing in a context with ambient variance `variance`
    fn add_constraints_from_args(
        &mut self,
        current: &CurrentItem,
        def_id: DefId,
        args: GenericArgsRef<'tcx>,
        variance: VarianceTermPtr<'a>,
    ) {
        debug!(
            "add_constraints_from_args(def_id={:?}, args={:?}, variance={:?})",
            def_id, args, variance
        );

        // We don't record `inferred_starts` entries for empty generics.
        if args.is_empty() {
            return;
        }

        let (local, remote) = if let Some(def_id) = def_id.as_local() {
            (Some(self.terms_cx.inferred_starts[&def_id]), None)
        } else {
            (None, Some(self.tcx().variances_of(def_id)))
        };

        for (i, arg) in args.iter().enumerate() {
            let variance_decl = if let Some(InferredIndex(start)) = local {
                // Parameter on an item defined within current crate:
                // variance not yet inferred, so return a symbolic
                // variance.
                self.terms_cx.inferred_terms[start + i]
            } else {
                // Parameter on an item defined within another crate:
                // variance already inferred, just look it up.
                self.constant_term(remote.as_ref().unwrap()[i])
            };
            let variance_i = self.xform(variance, variance_decl);
            debug!(
                "add_constraints_from_args: variance_decl={:?} variance_i={:?}",
                variance_decl, variance_i
            );
            match arg.kind() {
                GenericArgKind::Lifetime(lt) => {
                    self.add_constraints_from_region(current, lt, variance_i)
                }
                GenericArgKind::Type(ty) => self.add_constraints_from_ty(current, ty, variance_i),
                GenericArgKind::Const(val) => {
                    self.add_constraints_from_const(current, val, variance)
                }
            }
        }
    }

    /// Adds constraints appropriate for a const expression `val`
    /// in a context with ambient variance `variance`
    fn add_constraints_from_const(
        &mut self,
        current: &CurrentItem,
        c: ty::Const<'tcx>,
        variance: VarianceTermPtr<'a>,
    ) {
        debug!("add_constraints_from_const(c={:?}, variance={:?})", c, variance);

        match &c.kind() {
            ty::ConstKind::Alias(_, alias_const) => {
                self.add_constraints_from_invariant_args(current, alias_const.args, variance);
            }
            _ => {}
        }
    }

    /// Adds constraints appropriate for a function with signature
    /// `sig` appearing in a context with ambient variance `variance`
    fn add_constraints_from_sig(
        &mut self,
        current: &CurrentItem,
        sig: ty::PolyFnSig<'tcx>,
        variance: VarianceTermPtr<'a>,
    ) {
        let contra = self.contravariant(variance);
        for &input in sig.skip_binder().inputs() {
            self.add_constraints_from_ty(current, input, contra);
        }
        self.add_constraints_from_ty(current, sig.skip_binder().output(), variance);
    }

    /// Adds constraints appropriate for a region appearing in a
    /// context with ambient variance `variance`
    fn add_constraints_from_region(
        &mut self,
        current: &CurrentItem,
        region: ty::Region<'tcx>,
        variance: VarianceTermPtr<'a>,
    ) {
        match region.kind() {
            ty::ReEarlyParam(ref data) => {
                self.add_constraint(current, data.index, variance);
            }

            ty::ReStatic => {}

            ty::ReBound(..) => {
                // Either a higher-ranked region inside of a type or a
                // late-bound function parameter.
                //
                // We do not compute constraints for either of these.
            }

            ty::ReError(_) => {}

            ty::ReLateParam(..) | ty::ReVar(..) | ty::RePlaceholder(..) | ty::ReErased => {
                // We don't expect to see anything but 'static or bound
                // regions when visiting member types or method types.
                bug!(
                    "unexpected region encountered in variance \
                      inference: {:?}",
                    region
                );
            }
        }
    }

    /// Adds constraints appropriate for a mutability-type pair
    /// appearing in a context with ambient variance `variance`
    fn add_constraints_from_mt(
        &mut self,
        current: &CurrentItem,
        mt: &ty::TypeAndMut<'tcx>,
        variance: VarianceTermPtr<'a>,
    ) {
        match mt.mutbl {
            hir::Mutability::Mut => {
                let invar = self.invariant(variance);
                self.add_constraints_from_ty(current, mt.ty, invar);
            }

            hir::Mutability::Not => {
                self.add_constraints_from_ty(current, mt.ty, variance);
            }
        }
    }
}
