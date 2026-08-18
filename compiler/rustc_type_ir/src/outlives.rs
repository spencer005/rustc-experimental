//! The outlives relation `T: 'a` or `'a: 'b`. This code frequently
//! refers to rules defined in RFC 1214 (`OutlivesFooBar`), so see that
//! RFC for reference.

use derive_where::derive_where;
use smallvec::{SmallVec, smallvec};

use crate::data_structures::SsoHashSet;
use crate::inherent::*;
use crate::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitableExt as _, TypeVisitor};
use crate::{self as ty, AliasTy, Interner, OutlivesClause, Region, Unnormalized};

#[derive_where(Debug; I: Interner)]
pub enum Component<I: Interner> {
    Region(Region<I>),
    Param(I::ParamTy),
    Placeholder(ty::PlaceholderType<I>),
    UnresolvedInferenceVariable(ty::InferTy),

    // Projections like `T::Foo` are tricky because a constraint like
    // `T::Foo: 'a` can be satisfied in so many ways. There may be a
    // where-clause that says `T::Foo: 'a`, or the defining trait may
    // include a bound like `type Foo: 'static`, or -- in the most
    // conservative way -- we can prove that `T: 'a` (more generally,
    // that all components in the projection outlive `'a`). This code
    // is not in a position to judge which is the best technique, so
    // we just product the projection as a component and leave it to
    // the consumer to decide (but see `EscapingProjection` below).
    //
    // We have to track rigidness because it's also used in param env
    // elaboration where things are not normalized yet.
    Alias(ty::IsRigid, ty::AliasTy<I>),

    // In the case where a projection has escaping regions -- meaning
    // regions bound within the type itself -- we always use
    // the most conservative rule, which requires that all components
    // outlive the bound. So for example if we had a type like this:
    //
    //     for<'a> Trait1<  <T as Trait2<'a,'b>>::Foo  >
    //                      ~~~~~~~~~~~~~~~~~~~~~~~~~
    //
    // then the inner projection (underlined) has an escaping region
    // `'a`. We consider that outer trait `'c` to meet a bound if `'b`
    // outlives `'b: 'c`, and we don't consider whether the trait
    // declares that `Foo: 'static` etc. Therefore, we just return the
    // free components of such a projection (in this case, `'b`).
    //
    // However, in the future, we may want to get smarter, and
    // actually return a "higher-ranked projection" here. Therefore,
    // we mark that these components are part of an escaping
    // projection, so that implied bounds code can avoid relying on
    // them. This gives us room to improve the regionck reasoning in
    // the future without breaking backwards compat.
    EscapingAlias(Vec<Component<I>>),
}

/// Push onto `out` all the things that must outlive `'a` for the condition
/// `ty0: 'a` to hold. Note that `ty0` must be a **fully resolved type**.
pub fn push_outlives_components<I: Interner>(
    cx: I,
    ty: I::Ty,
    out: &mut SmallVec<[Component<I>; 4]>,
) {
    push_outlives_components_inner(cx, ty, false, out);
}

/// Like [`push_outlives_components`], but also preserves callable-interface components when the
/// outlives target is `'static` or is still permitted to resolve to `'static`.
pub fn push_static_outlives_components<I: Interner>(
    cx: I,
    ty: I::Ty,
    out: &mut SmallVec<[Component<I>; 4]>,
) {
    push_outlives_components_inner(cx, ty, true, out);
}

fn push_outlives_components_inner<I: Interner>(
    cx: I,
    ty: I::Ty,
    preserve_static_identity: bool,
    out: &mut SmallVec<[Component<I>; 4]>,
) {
    ty.visit_with(&mut OutlivesCollector {
        cx,
        preserve_static_identity,
        out,
        visited: Default::default(),
    });
}

struct OutlivesCollector<'a, I: Interner> {
    cx: I,
    preserve_static_identity: bool,
    out: &'a mut SmallVec<[Component<I>; 4]>,
    visited: SsoHashSet<I::Ty>,
}

impl<I: Interner> TypeVisitor<I> for OutlivesCollector<'_, I> {
    #[cfg(not(feature = "nightly"))]
    type Result = ();

    fn visit_ty(&mut self, ty: I::Ty) -> Self::Result {
        if !self.visited.insert(ty) {
            return;
        }
        // Descend through the types, looking for the various "base"
        // components and collecting them into `out`. This is not written
        // with `collect()` because of the need to sometimes skip subtrees
        // in the `subtys` iterator (e.g., when encountering a
        // projection).
        match ty.kind() {
            ty::FnDef(_, args) => {
                let args = args.no_bound_vars().unwrap();
                // Keep ignoring shallow lifetime arguments for compatibility with #70917.
                // A lifetime only participates in static identity if it is observable through
                // the instantiated callable signature.
                for child in args.iter() {
                    match child.kind() {
                        ty::GenericArgKind::Lifetime(_) => {}
                        ty::GenericArgKind::Type(_) | ty::GenericArgKind::Const(_) => {
                            child.visit_with(self);
                        }
                    }
                }

                if self.preserve_static_identity {
                    ty.fn_sig(self.cx).inputs_and_output().visit_with(self);
                }
            }

            // Closure and coroutine parent args are not independently observable. Only args
            // present in their signature or stored state constrain structural outlives.
            ty::Closure(_, args) => {
                let args = args.as_closure();
                args.tupled_upvars_ty().visit_with(self);
                if self.preserve_static_identity {
                    args.sig_as_fn_ptr_ty().visit_with(self);
                }
            }

            ty::CoroutineClosure(_, args) => {
                let args = args.as_coroutine_closure();
                args.tupled_upvars_ty().visit_with(self);
                if self.preserve_static_identity {
                    args.signature_parts_ty().visit_with(self);
                    args.coroutine_captures_by_ref_ty().visit_with(self);
                }
            }

            ty::Coroutine(_, args) => {
                let args = args.as_coroutine();
                args.tupled_upvars_ty().visit_with(self);

                // Coroutines may not outlive a region unless the resume type outlives that
                // region. The resume value may be stored across yield points.
                args.resume_ty().visit_with(self);

                if self.preserve_static_identity {
                    // Yield and return types are part of the coroutine's observable identity even
                    // when no value of either type is currently stored in the frame.
                    args.yield_ty().visit_with(self);
                    args.return_ty().visit_with(self);
                }
            }

            // All regions are bound inside a witness, and we don't emit
            // higher-ranked outlives components currently.
            ty::CoroutineWitness(..) => {}

            // OutlivesTypeParameterEnv -- the actual checking that `X:'a`
            // is implied by the environment is done in regionck.
            ty::Param(p) => {
                self.out.push(Component::Param(p));
            }

            ty::Placeholder(p) => {
                self.out.push(Component::Placeholder(p));
            }

            // For projections, we prefer to generate an obligation like
            // `<P0 as Trait<P1...Pn>>::Foo: 'a`, because this gives the
            // regionck more ways to prove that it holds. However,
            // regionck is not (at least currently) prepared to deal with
            // higher-ranked regions that may appear in the
            // trait-ref. Therefore, if we see any higher-ranked regions,
            // we simply fallback to the most restrictive rule, which
            // requires that `Pi: 'a` for all `i`.
            ty::Alias(is_rigid, alias_ty) => {
                if !alias_ty.has_escaping_bound_vars() {
                    // best case: no escaping regions, so push the
                    // projection and skip the subtree (thus generating no
                    // constraints for Pi). This defers the choice between
                    // the rules OutlivesProjectionEnv,
                    // OutlivesProjectionTraitDef, and
                    // OutlivesProjectionComponents to regionck.
                    self.out.push(Component::Alias(is_rigid, alias_ty));
                } else {
                    // fallback case: hard code
                    // OutlivesProjectionComponents. Continue walking
                    // through and constrain Pi.
                    let mut subcomponents = smallvec![];
                    compute_alias_components_recursive_inner(
                        self.cx,
                        alias_ty,
                        self.preserve_static_identity,
                        &mut subcomponents,
                    );
                    self.out.push(Component::EscapingAlias(subcomponents.into_iter().collect()));
                }
            }

            // We assume that inference variables are fully resolved.
            // So, if we encounter an inference variable, just record
            // the unresolved variable as a component.
            ty::Infer(infer_ty) => {
                self.out.push(Component::UnresolvedInferenceVariable(infer_ty));
            }

            // Most types do not introduce any region binders, nor
            // involve any other subtle cases, and so the WF relation
            // simply constraints any regions referenced directly by
            // the type and then visits the types that are lexically
            // contained within.
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Error(_) => {
                // Trivial
            }

            ty::Bound(_, _) => {
                // FIXME: Bound vars matter here!
            }

            ty::Adt(_, _)
            | ty::Foreign(_)
            | ty::Array(_, _)
            | ty::Pat(_, _)
            | ty::Slice(_)
            | ty::RawPtr(_, _)
            | ty::Ref(_, _, _)
            | ty::FnPtr(..)
            | ty::UnsafeBinder(_)
            | ty::Dynamic(_, _)
            | ty::Tuple(_) => {
                ty.super_visit_with(self);
            }
        }
    }

    fn visit_region(&mut self, lt: Region<I>) -> Self::Result {
        if !lt.is_bound() {
            self.out.push(Component::Region(lt));
        }
    }
}

/// Collect [Component]s for *all* the args of `alias_ty`.
///
/// This should not be used to get the components of `alias_ty` itself.
/// Use [push_outlives_components] instead.
pub fn compute_alias_components_recursive<I: Interner>(
    cx: I,
    alias_ty: ty::AliasTy<I>,
    out: &mut SmallVec<[Component<I>; 4]>,
) {
    compute_alias_components_recursive_inner(cx, alias_ty, false, out);
}

/// Like [`compute_alias_components_recursive`], but preserves callable-interface components when
/// the outlives target is `'static` or is still permitted to resolve to `'static`.
pub fn compute_alias_components_recursive_for_static<I: Interner>(
    cx: I,
    alias_ty: ty::AliasTy<I>,
    out: &mut SmallVec<[Component<I>; 4]>,
) {
    compute_alias_components_recursive_inner(cx, alias_ty, true, out);
}

fn compute_alias_components_recursive_inner<I: Interner>(
    cx: I,
    alias_ty: ty::AliasTy<I>,
    preserve_static_identity: bool,
    out: &mut SmallVec<[Component<I>; 4]>,
) {
    let opt_variances = cx.opt_alias_variances(alias_ty.kind);

    let mut visitor = OutlivesCollector {
        cx,
        preserve_static_identity,
        out,
        visited: Default::default(),
    };

    for (index, child) in alias_ty.args.iter().enumerate() {
        if opt_variances.and_then(|variances| variances.get(index)) == Some(ty::Bivariant) {
            continue;
        }
        child.visit_with(&mut visitor);
    }
}

/// Given a projection like `<T as Foo<'x>>::Bar`, returns any bounds
/// declared in the trait definition. For example, if the trait were
///
/// ```rust
/// trait Foo<'a> {
///     type Bar: 'a;
/// }
/// ```
///
/// If we were given `<T as Foo<'b>>::Bar`, we would return
/// `'b`. This doesn't work for higher-ranked bounds such as:
///
/// ```ignore (this does compile today, previously was marked as compile_fail,E0311)
/// trait Foo<'a, 'b>
/// where for<'x> <Self as Foo<'x, 'b>>::Bar: 'x
/// {
///     type Bar;
/// }
/// ```
///
/// This is for simplicity, and because we are not really smart
/// enough to cope with such bounds anywhere.
pub fn declared_bounds_from_definition<I: Interner>(
    cx: I,
    alias_ty: AliasTy<I>,
) -> impl Iterator<Item = Region<I>> {
    let def_id = match alias_ty.kind {
        ty::AliasTyKind::Projection { def_id } => def_id.into(),
        ty::AliasTyKind::Inherent { def_id } => def_id.into(),
        ty::AliasTyKind::Opaque { def_id } => def_id.into(),
        ty::AliasTyKind::Free { def_id } => def_id.into(),
    };

    let bounds = cx.item_self_bounds(def_id);
    bounds
        .iter_instantiated(cx, alias_ty.args)
        .map(Unnormalized::skip_norm_wip)
        .filter_map(|c| c.as_type_outlives_clause())
        .filter_map(|c| c.no_bound_vars())
        .map(|OutlivesClause(_, r)| r)
}
