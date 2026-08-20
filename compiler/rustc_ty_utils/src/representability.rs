use rustc_hir::def::DefKind;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::bug;
use rustc_middle::query::Providers;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::def_id::LocalDefId;

pub(crate) fn provide(providers: &mut Providers) {
    *providers = Providers {
        check_representability,
        check_representability_adt_ty,
        params_in_repr,
        ..*providers
    };
}

fn check_representability(tcx: TyCtxt<'_>, def_id: LocalDefId) {
    match tcx.def_kind(def_id) {
        DefKind::Struct | DefKind::Union | DefKind::Enum => {
            for variant in tcx.adt_def(def_id).variants() {
                for field in variant.fields.iter() {
                    tcx.ensure_ok().check_representability(field.did.expect_local());
                }
            }
        }
        DefKind::Field => {
            check_representability_ty(
                tcx,
                tcx.type_of(def_id).instantiate_identity().skip_norm_wip(),
            );
        }
        def_kind => bug!("unexpected {def_kind:?}"),
    }
}

fn check_representability_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) {
    match *ty.kind() {
        // This one must be a query rather than a vanilla `check_representability_adt_ty` call. See
        // the comment on `check_representability_adt_ty` below for why.
        ty::Adt(..) => {
            tcx.ensure_ok().check_representability_adt_ty(ty);
        }
        // FIXME(#11924) allow zero-length arrays?
        ty::Array(ty, _) => {
            check_representability_ty(tcx, ty);
        }
        ty::Tuple(tys) => {
            for ty in tys {
                check_representability_ty(tcx, ty);
            }
        }
        _ => {}
    }
}

// The reason for this being a separate query is very subtle. Consider this
// infinitely sized struct: `struct Foo(Box<Foo>, Bar<Foo>)`. When calling
// check_representability(Foo), a query cycle will occur:
//
//   check_representability(Foo)
//     -> check_representability_adt_ty(Bar<Foo>)
//     -> check_representability(Foo)
//
// For the diagnostic output (in `check_representability`), we want to detect
// that the `Foo` in the *second* field of the struct is culpable. This
// requires traversing the HIR of the struct and calling `params_in_repr(Bar)`.
// But we can't call params_in_repr for a given type unless it is known to be
// representable. params_in_repr will cycle/panic on infinitely sized types.
// Looking at the query cycle above, we know that `Bar` is representable
// because `check_representability_adt_ty(Bar<..>)` is in the cycle and
// `check_representability(Bar)` is *not* in the cycle.
fn check_representability_adt_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) {
    let ty::Adt(adt, args) = ty.kind() else { bug!("expected adt") };
    if let Some(def_id) = adt.did().as_local() {
        tcx.ensure_ok().check_representability(def_id);
    }
    // At this point, we know that the item of the ADT type is representable;
    // but the type parameters may cause a cycle with an upstream type
    let params_in_repr = tcx.params_in_repr(adt.did());
    for (i, arg) in args.iter().enumerate() {
        if let ty::GenericArgKind::Type(ty) = arg.kind() {
            if params_in_repr.contains(i as u32) {
                check_representability_ty(tcx, ty);
            }
        }
    }
}

fn params_in_repr(tcx: TyCtxt<'_>, def_id: LocalDefId) -> DenseBitSet<u32> {
    let adt_def = tcx.adt_def(def_id);
    let generics = tcx.generics_of(def_id);
    let mut params_in_repr = DenseBitSet::new_empty(generics.own_params.len());
    for variant in adt_def.variants() {
        if !adt_def.is_enum() {
            for field in &variant.fields {
                params_in_repr_ty(
                    tcx,
                    tcx.type_of(field.did).instantiate_identity().skip_norm_wip(),
                    None,
                    &mut params_in_repr,
                );
            }
            continue;
        }
        match tcx.variant_scheme(variant.def_id) {
            ty::VariantScheme::Ordinary => {
                for field in &variant.fields {
                    params_in_repr_ty(
                        tcx,
                        tcx.type_of(field.did).instantiate_identity().skip_norm_wip(),
                        None,
                        &mut params_in_repr,
                    );
                }
            }
            ty::VariantScheme::Invalid(_) => {}
            ty::VariantScheme::Refined(scheme) => {
                let mut scheme_param_to_family =
                    vec![None; scheme.binders.family.len() + scheme.binders.local.len()];

                for scheme_param in &scheme.binders.family {
                    let family_param = generics
                        .own_params
                        .iter()
                        .find(|family_param| family_param.def_id == scheme_param.def_id)
                        .unwrap_or_else(|| {
                            bug!(
                                "refined variant family binder {:?} is not a parameter of {:?}",
                                scheme_param.def_id,
                                def_id
                            )
                        });
                    scheme_param_to_family[scheme_param.index as usize] = Some(family_param.index);
                }

                for recovery in &scheme.recoveries {
                    let scheme_param = scheme
                        .binders
                        .family
                        .iter()
                        .chain(&scheme.binders.local)
                        .find(|param| param.def_id == recovery.binder_def_id)
                        .unwrap_or_else(|| {
                            bug!(
                                "recovery for non-scheme binder {:?} in {:?}",
                                recovery.binder_def_id,
                                variant.def_id
                            )
                        });
                    let Some(&ty::VariantResultProjection::GenericArg(family_index)) =
                        recovery.path.first()
                    else {
                        bug!(
                            "recovery for binder {:?} in {:?} does not start at a family argument",
                            recovery.binder_def_id,
                            variant.def_id
                        )
                    };
                    if family_index as usize >= generics.own_params.len() {
                        bug!(
                            "recovery for binder {:?} in {:?} references family argument {} but {:?} has only {} parameters",
                            recovery.binder_def_id,
                            variant.def_id,
                            family_index,
                            def_id,
                            generics.own_params.len()
                        )
                    }
                    scheme_param_to_family[scheme_param.index as usize] = Some(family_index);
                }

                for field in &scheme.fields {
                    params_in_repr_ty(
                        tcx,
                        field.ty,
                        Some(&scheme_param_to_family),
                        &mut params_in_repr,
                    );
                }
            }
        }
    }
    params_in_repr
}

fn params_in_repr_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_index_map: Option<&[Option<u32>]>,
    params_in_repr: &mut DenseBitSet<u32>,
) {
    match *ty.kind() {
        ty::Adt(adt, args) => {
            let inner_params_in_repr = tcx.params_in_repr(adt.did());
            for (i, arg) in args.iter().enumerate() {
                if let ty::GenericArgKind::Type(ty) = arg.kind()
                    && inner_params_in_repr.contains(i as u32)
                {
                    params_in_repr_ty(tcx, ty, param_index_map, params_in_repr);
                }
            }
        }
        ty::Array(ty, _) => params_in_repr_ty(tcx, ty, param_index_map, params_in_repr),
        ty::Tuple(tys) => {
            tys.iter().for_each(|ty| params_in_repr_ty(tcx, ty, param_index_map, params_in_repr))
        }
        ty::Param(param) => {
            let family_index = if let Some(param_index_map) = param_index_map {
                param_index_map
                    .get(param.index as usize)
                    .copied()
                    .flatten()
                    .unwrap_or_else(|| {
                        bug!(
                            "representation field references scheme parameter {} without a family recovery",
                            param.index
                        )
                    })
            } else {
                param.index
            };
            params_in_repr.insert(family_index);
        }
        _ => {}
    }
}
