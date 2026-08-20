use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_infer::infer::SubregionOrigin;
use rustc_infer::infer::canonical::{QueryRegionConstraint, QueryRegionConstraints};
use rustc_infer::infer::outlives::env::RegionBoundPairs;
use rustc_infer::infer::outlives::obligations::{TypeOutlives, TypeOutlivesDelegate};
use rustc_infer::infer::region_constraints::{GenericKind, VerifyBound};
use rustc_middle::ty::{
    self, GenericArgKind, RegionExt, TyCtxt, TypeFoldable, TypeVisitableExt, elaborate,
    fold_regions,
};
use rustc_span::Span;
use smallvec::SmallVec;
use tracing::{debug, instrument};

use crate::constraints::OutlivesConstraint;
use crate::region_infer::TypeTest;
use crate::type_check::free_region_relations::UniversalRegionRelations;
use crate::type_check::{Locations, MirTypeckRegionConstraints};
use crate::universal_regions::UniversalRegions;
use crate::{
    BorrowckInferCtxt, ClosureOutlivesSubject, ClosureRegionRequirements, ConstraintCategory,
};

struct StaticOutlivesRegions {
    regions: SmallVec<[ty::RegionVid; 8]>,
}

impl StaticOutlivesRegions {
    fn contains(&self, region: ty::RegionVid) -> bool {
        self.regions.contains(&region)
    }

    fn insert(&mut self, region: ty::RegionVid) {
        if !self.contains(region) {
            self.regions.push(region);
        }
    }
}

pub(crate) struct ConstraintConversion<'a, 'tcx> {
    infcx: &'a BorrowckInferCtxt<'tcx>,
    universal_region_relations: &'a UniversalRegionRelations<'tcx>,
    /// Each RBP `GK: 'a` is assumed to be true. These encode
    /// relationships like `T: 'a` that are added via implicit bounds
    /// or the `param_env`.
    ///
    /// Each region here is guaranteed to be a key in the `indices`
    /// map. We use the "original" regions (i.e., the keys from the
    /// map, and not the values) because the code in
    /// `process_registered_region_obligations` has some special-cased
    /// logic expecting to see (e.g.) `ReStatic`, and if we supplied
    /// our special inference variable there, we would mess that up.
    region_bound_pairs: &'a RegionBoundPairs<'tcx>,
    known_type_outlives_obligations: &'a [ty::PolyTypeOutlivesClause<'tcx>],
    locations: Locations,
    span: Span,
    category: ConstraintCategory<'tcx>,
    from_closure: bool,
    constraints: &'a mut MirTypeckRegionConstraints<'tcx>,
}

impl<'a, 'tcx> ConstraintConversion<'a, 'tcx> {
    pub(crate) fn new(
        infcx: &'a BorrowckInferCtxt<'tcx>,
        universal_region_relations: &'a UniversalRegionRelations<'tcx>,
        region_bound_pairs: &'a RegionBoundPairs<'tcx>,
        known_type_outlives_obligations: &'a [ty::PolyTypeOutlivesClause<'tcx>],
        locations: Locations,
        span: Span,
        category: ConstraintCategory<'tcx>,
        constraints: &'a mut MirTypeckRegionConstraints<'tcx>,
    ) -> Self {
        Self {
            infcx,
            universal_region_relations,
            region_bound_pairs,
            known_type_outlives_obligations,
            locations,
            span,
            category,
            constraints,
            from_closure: false,
        }
    }

    #[instrument(skip(self), level = "debug")]
    pub(super) fn convert_all(&mut self, query_constraints: &QueryRegionConstraints<'tcx>) {
        let QueryRegionConstraints { constraints, assumptions } = query_constraints;
        let assumptions =
            elaborate::elaborate_outlives_assumptions(self.infcx.tcx, assumptions.iter().copied());
        let region_edges = constraints.iter().flat_map(|constraint| {
            constraint.constraint.iter_outlives().filter_map(|ty::OutlivesClause(arg, sub)| {
                match arg.kind() {
                    GenericArgKind::Lifetime(sup) => Some((sup, sub)),
                    GenericArgKind::Type(_) | GenericArgKind::Const(_) => None,
                }
            })
        });
        let static_outlives = self.static_outlives_regions(region_edges);

        for &QueryRegionConstraint { constraint, category, .. } in constraints {
            constraint.iter_outlives().for_each(|predicate| {
                self.convert(predicate, category, &assumptions, &static_outlives);
            });
        }
    }

    /// Given an instance of the closure type, this method instantiates the "extra" requirements
    /// that we computed for the closure. This has the effect of adding new outlives obligations
    /// to existing region variables in `closure_args`.
    #[instrument(skip(self), level = "debug")]
    pub(crate) fn apply_closure_requirements(
        &mut self,
        closure_requirements: &ClosureRegionRequirements<'tcx>,
        closure_def_id: LocalDefId,
        closure_args: ty::GenericArgsRef<'tcx>,
    ) {
        // Extract the values of the free regions in `closure_args`
        // into a vector. These are the regions that we will be
        // relating to one another.
        let closure_mapping = &UniversalRegions::closure_mapping(
            self.infcx.tcx,
            closure_args,
            closure_requirements.num_external_vids,
            closure_def_id,
        );
        debug!(?closure_mapping);

        let region_edges =
            closure_requirements.outlives_requirements.iter().filter_map(|requirement| {
                let sub = closure_mapping[requirement.outlived_free_region];
                match requirement.subject {
                    ClosureOutlivesSubject::Region(region) => Some((closure_mapping[region], sub)),
                    ClosureOutlivesSubject::Ty(_) => None,
                }
            });
        let static_outlives = self.static_outlives_regions(region_edges);

        // Create the predicates.
        let backup = (self.category, self.span, self.from_closure);
        self.from_closure = true;
        for outlives_requirement in &closure_requirements.outlives_requirements {
            let outlived_region = closure_mapping[outlives_requirement.outlived_free_region];
            let subject = match outlives_requirement.subject {
                ClosureOutlivesSubject::Region(re) => closure_mapping[re].into(),
                ClosureOutlivesSubject::Ty(subject_ty) => {
                    subject_ty.instantiate(self.infcx.tcx, |vid| closure_mapping[vid]).into()
                }
            };

            self.category = outlives_requirement.category;
            self.span = outlives_requirement.blame_span;
            self.convert(
                ty::OutlivesClause(subject, outlived_region),
                self.category,
                &Default::default(),
                &static_outlives,
            );
        }
        (self.category, self.span, self.from_closure) = backup;
    }

    fn convert(
        &mut self,
        clause: ty::ArgOutlivesClause<'tcx>,
        constraint_category: ConstraintCategory<'tcx>,
        higher_ranked_assumptions: &FxHashSet<ty::ArgOutlivesClause<'tcx>>,
        static_outlives: &StaticOutlivesRegions,
    ) {
        let tcx = self.infcx.tcx;
        debug!("generate: constraints at: {:#?}", self.locations);

        // Extract out various useful fields we'll need below.
        let ConstraintConversion {
            infcx: _,
            universal_region_relations,
            region_bound_pairs,
            known_type_outlives_obligations,
            ..
        } = *self;
        let universal_regions = &universal_region_relations.universal_regions;

        // Constraint is implied by a coroutine's well-formedness.
        if self.infcx.tcx.sess.opts.unstable_opts.higher_ranked_assumptions
            && higher_ranked_assumptions.contains(&clause)
        {
            return;
        }

        let ty::OutlivesClause(k1, r2) = clause;
        match k1.kind() {
            GenericArgKind::Lifetime(r1) => {
                let r1_vid = self.to_region_vid(r1);
                let r2_vid = self.to_region_vid(r2);
                self.add_outlives(r1_vid, r2_vid, constraint_category);
            }

            GenericArgKind::Type(mut t1) => {
                // Scraped constraints may have had inference vars.
                t1 = self.infcx.resolve_vars_if_possible(t1);

                let r2_vid = self.to_region_vid(r2);
                let preserve_static_identity =
                    r2.is_placeholder() || static_outlives.contains(r2_vid);
                let implicit_region_bound =
                    ty::Region::new_var(tcx, universal_regions.implicit_region_bound());
                // we don't actually use this for anything, but
                // the `TypeOutlives` code needs an origin.
                let origin = SubregionOrigin::RelateParamBound(self.span, t1, None);
                let outlives = &mut TypeOutlives::new(
                    &mut *self,
                    tcx,
                    region_bound_pairs,
                    Some(implicit_region_bound),
                    known_type_outlives_obligations,
                );
                if preserve_static_identity {
                    outlives.type_must_outlive_with_static_identity(
                        origin,
                        t1,
                        r2,
                        constraint_category,
                    );
                } else {
                    outlives.type_must_outlive(origin, t1, r2, constraint_category);
                }
            }

            GenericArgKind::Const(_) => unreachable!(),
        }
    }
    fn static_outlives_regions(
        &mut self,
        region_edges: impl IntoIterator<Item = (ty::Region<'tcx>, ty::Region<'tcx>)>,
    ) -> StaticOutlivesRegions {
        let mut additional_edges = SmallVec::<[(ty::RegionVid, ty::RegionVid); 8]>::new();
        for (sup, sub) in region_edges {
            let sup = self.to_region_vid(sup);
            let sub = self.to_region_vid(sub);
            additional_edges.push((sup, sub));
        }

        let universal_regions = &self.universal_region_relations.universal_regions;
        let mut static_outlives = StaticOutlivesRegions { regions: SmallVec::new() };
        for region in universal_regions.universal_regions_iter() {
            if self.universal_region_relations.outlives(region, universal_regions.fr_static) {
                static_outlives.insert(region);
            }
        }

        let mut next = 0;
        while next < static_outlives.regions.len() {
            let sub = static_outlives.regions[next];
            next += 1;

            for constraint in self.constraints.outlives_constraints.outlives().iter() {
                let applies = match (self.locations, constraint.locations) {
                    (_, Locations::All(_)) => true,
                    (Locations::Single(required), Locations::Single(edge)) => required == edge,
                    (Locations::All(_), Locations::Single(_)) => false,
                };
                if applies && constraint.sub == sub {
                    static_outlives.insert(constraint.sup);
                }
            }
            for &(sup, edge_sub) in &additional_edges {
                if edge_sub == sub {
                    static_outlives.insert(sup);
                }
            }
        }

        static_outlives
    }

    /// Placeholder regions need to be converted eagerly because it may
    /// create new region variables, which we must not do when verifying
    /// our region bounds.
    ///
    /// FIXME: This should get removed once higher ranked region obligations
    /// are dealt with during trait solving.
    fn replace_placeholders_with_nll<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, value: T) -> T {
        if value.has_placeholders() {
            fold_regions(self.infcx.tcx, value, |r, _| match r.kind() {
                ty::RePlaceholder(placeholder) => {
                    self.constraints.placeholder_region(self.infcx, placeholder)
                }
                _ => r,
            })
        } else {
            value
        }
    }

    fn verify_to_type_test(
        &mut self,
        generic_kind: GenericKind<'tcx>,
        region: ty::Region<'tcx>,
        verify_bound: VerifyBound<'tcx>,
    ) -> TypeTest<'tcx> {
        let lower_bound = self.to_region_vid(region);
        TypeTest { generic_kind, lower_bound, span: self.span, verify_bound }
    }

    fn to_region_vid(&mut self, r: ty::Region<'tcx>) -> ty::RegionVid {
        if let ty::RePlaceholder(placeholder) = r.kind() {
            self.constraints.placeholder_region(self.infcx, placeholder).as_var()
        } else {
            self.universal_region_relations.universal_regions.to_region_vid(r)
        }
    }

    fn add_outlives(
        &mut self,
        sup: ty::RegionVid,
        sub: ty::RegionVid,
        category: ConstraintCategory<'tcx>,
    ) {
        let category = match self.category {
            ConstraintCategory::Boring | ConstraintCategory::BoringNoLocation => category,
            _ => self.category,
        };
        self.constraints.outlives_constraints.push(OutlivesConstraint {
            locations: self.locations,
            category,
            span: self.span,
            sub,
            sup,
            variance_info: ty::VarianceDiagInfo::default(),
            from_closure: self.from_closure,
        });
    }

    fn add_type_test(&mut self, type_test: TypeTest<'tcx>) {
        debug!("add_type_test(type_test={:?})", type_test);
        self.constraints.type_tests.push(type_test);
    }
}

impl<'a, 'b, 'tcx> TypeOutlivesDelegate<'tcx> for &'a mut ConstraintConversion<'b, 'tcx> {
    fn push_sub_region_constraint(
        &mut self,
        _origin: SubregionOrigin<'tcx>,
        a: ty::Region<'tcx>,
        b: ty::Region<'tcx>,
        constraint_category: ConstraintCategory<'tcx>,
    ) {
        let b = self.to_region_vid(b);
        let a = self.to_region_vid(a);
        self.add_outlives(b, a, constraint_category);
    }

    fn push_verify(
        &mut self,
        _origin: SubregionOrigin<'tcx>,
        kind: GenericKind<'tcx>,
        a: ty::Region<'tcx>,
        bound: VerifyBound<'tcx>,
    ) {
        let kind = self.replace_placeholders_with_nll(kind);
        let bound = self.replace_placeholders_with_nll(bound);
        let type_test = self.verify_to_type_test(kind, a, bound);
        self.add_type_test(type_test);
    }
}
