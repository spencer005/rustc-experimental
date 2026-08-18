use std::collections::VecDeque;
use std::ops::ControlFlow;

use rustc_middle::mir::{
    BasicBlock, Body, Local, Operand, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::{
    self, OriginContract, OriginContractAnalysis, OriginContractError, OriginContractErrorKind,
    OriginRequirement, OriginSlot, RegionSlot, TyCtxt, TypeVisitable, TypeVisitor,
};

fn visit_region_occurrences<'tcx>(
    value: impl TypeVisitable<TyCtxt<'tcx>>,
    f: impl FnMut(ty::Region<'tcx>) -> ControlFlow<()>,
) -> ControlFlow<()> {
    struct Visitor<F>(F);

    impl<'tcx, F> TypeVisitor<TyCtxt<'tcx>> for Visitor<F>
    where
        F: FnMut(ty::Region<'tcx>) -> ControlFlow<()>,
    {
        type Result = ControlFlow<()>;

        fn visit_region(&mut self, region: ty::Region<'tcx>) -> Self::Result {
            if matches!(region.kind(), ty::ReBound(..)) {
                ControlFlow::Continue(())
            } else {
                (self.0)(region)
            }
        }
    }

    value.visit_with(&mut Visitor(f))
}

fn region_occurrences<'tcx>(value: impl TypeVisitable<TyCtxt<'tcx>>) -> Vec<ty::Region<'tcx>> {
    let mut regions = Vec::new();
    let _ = visit_region_occurrences(value, |region| {
        regions.push(region);
        ControlFlow::Continue(())
    });
    regions
}

fn region_occurrence_count<'tcx>(value: impl TypeVisitable<TyCtxt<'tcx>>) -> usize {
    let mut count = 0;
    let _ = visit_region_occurrences(value, |_| {
        count += 1;
        ControlFlow::Continue(())
    });
    count
}

fn has_region_occurrence<'tcx>(value: impl TypeVisitable<TyCtxt<'tcx>>) -> bool {
    matches!(visit_region_occurrences(value, |_| ControlFlow::Break(())), ControlFlow::Break(()))
}

fn region_slot<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: rustc_hir::def_id::LocalDefId,
    region: ty::Region<'tcx>,
) -> Option<RegionSlot> {
    let def_id = match region.kind() {
        ty::ReEarlyParam(param) => tcx.generics_of(owner).region_param(param, tcx).def_id,
        ty::ReLateParam(param) => param.kind.get_id()?,
        _ => return None,
    };
    RegionSlot::from_def_id(tcx, def_id)
}

fn origin_slot<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: rustc_hir::def_id::LocalDefId,
    region: ty::Region<'tcx>,
) -> Option<OriginSlot> {
    let ty::ReEarlyParam(param) = region.kind() else { return None };
    OriginSlot::from_param(tcx.generics_of(owner).region_param(param, tcx))
}

struct Layout {
    offsets: Vec<usize>,
    words_per_set: usize,
    unknown_bit: usize,
}

impl Layout {
    fn new<'tcx>(body: &Body<'tcx>, source_count: usize) -> Self {
        let mut offsets = Vec::with_capacity(body.local_decls.len() + 1);
        offsets.push(0);
        for decl in body.local_decls.iter() {
            offsets.push(offsets.last().copied().unwrap() + region_occurrence_count(decl.ty));
        }
        let unknown_bit = source_count;
        let words_per_set = (source_count + 1).div_ceil(64);
        Self { offsets, words_per_set, unknown_bit }
    }

    fn local_slots(&self, local: Local) -> std::ops::Range<usize> {
        self.offsets[local.index()]..self.offsets[local.index() + 1]
    }

    fn state_words(&self) -> usize {
        self.offsets.last().copied().unwrap() * self.words_per_set
    }

    fn max_local_slots(&self) -> usize {
        self.offsets.windows(2).map(|window| window[1] - window[0]).max().unwrap_or(0)
    }

    fn slot_words(&self, slot: usize) -> std::ops::Range<usize> {
        let start = slot * self.words_per_set;
        start..start + self.words_per_set
    }

    fn clear_local(&self, state: &mut [u64], local: Local) {
        for slot in self.local_slots(local) {
            state[self.slot_words(slot)].fill(0);
        }
    }

    fn set_bit(&self, state: &mut [u64], slot: usize, bit: usize) {
        let words = self.slot_words(slot);
        state[words.start + bit / 64] |= 1 << (bit % 64);
    }

    fn set_unknown_local(&self, state: &mut [u64], local: Local) {
        self.clear_local(state, local);
        for slot in self.local_slots(local) {
            self.set_bit(state, slot, self.unknown_bit);
        }
    }

    fn copy_local(&self, state: &mut [u64], destination: Local, source: Local) {
        let dst = self.local_slots(destination);
        let src = self.local_slots(source);
        if dst.len() != src.len() {
            self.set_unknown_local(state, destination);
            return;
        }
        if destination == source {
            return;
        }
        self.clear_local(state, destination);
        for (destination_slot, source_slot) in dst.zip(src) {
            let destination_words = self.slot_words(destination_slot);
            let source_words = self.slot_words(source_slot);
            for offset in 0..self.words_per_set {
                state[destination_words.start + offset] = state[source_words.start + offset];
            }
        }
    }
}

fn merge_state(destination: &mut [u64], source: &[u64]) -> bool {
    let mut changed = false;
    for (destination, source) in destination.iter_mut().zip(source) {
        let old = *destination;
        *destination |= *source;
        changed |= old != *destination;
    }
    changed
}

fn propagate_state(
    entries: &mut [u64],
    reached: &mut [bool],
    queued: &mut [bool],
    queue: &mut VecDeque<BasicBlock>,
    state_words: usize,
    target: BasicBlock,
    state: &[u64],
) {
    let start = target.index() * state_words;
    let entry = &mut entries[start..start + state_words];
    let changed = if reached[target.index()] {
        merge_state(entry, state)
    } else {
        entry.copy_from_slice(state);
        reached[target.index()] = true;
        true
    };
    if changed && !queued[target.index()] {
        queued[target.index()] = true;
        queue.push_back(target);
    }
}


fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    }
}

fn assign_operand<'tcx>(
    layout: &Layout,
    state: &mut [u64],
    destination: Local,
    operand: &Operand<'tcx>,
) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            if let Some(source) = place.as_local() {
                layout.copy_local(state, destination, source);
            } else {
                layout.set_unknown_local(state, destination);
            }
        }
        Operand::Constant(_) | Operand::RuntimeChecks(_) => layout.clear_local(state, destination),
    }
}

fn assign_ref(
    layout: &Layout,
    state: &mut [u64],
    destination: Local,
    place: &rustc_middle::mir::Place<'_>,
) {
    let destination_slots = layout.local_slots(destination);
    let source_slots = layout.local_slots(place.local);
    if matches!(place.projection.first(), Some(ProjectionElem::Deref))
        && destination_slots.len() == source_slots.len()
    {
        layout.copy_local(state, destination, place.local);
    } else {
        layout.set_unknown_local(state, destination);
    }
}

fn assign_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    layout: &Layout,
    state: &mut [u64],
    scratch: &mut Vec<u64>,
    destination: Local,
    rvalue: &Rvalue<'tcx>,
) {
    match rvalue {
        Rvalue::Use(operand, _) => assign_operand(layout, state, destination, operand),
        Rvalue::CopyForDeref(place) => {
            if let Some(source) = place.as_local() {
                layout.copy_local(state, destination, source);
            } else {
                layout.set_unknown_local(state, destination);
            }
        }
        Rvalue::Ref(_, _, place) => assign_ref(layout, state, destination, place),
        Rvalue::Repeat(operand, _) | Rvalue::Cast(_, operand, _) | Rvalue::WrapUnsafeBinder(operand, _) => {
            let destination_slots = layout.local_slots(destination).len();
            let source_slots = operand.ty(&body.local_decls, tcx);
            if destination_slots == region_occurrence_count(source_slots) {
                assign_operand(layout, state, destination, operand);
            } else if destination_slots == 0 {
                layout.clear_local(state, destination);
            } else {
                layout.set_unknown_local(state, destination);
            }
        }
        Rvalue::Aggregate(_, operands) => {
            let destination_range = layout.local_slots(destination);
            scratch.clear();
            for operand in operands {
                let slots = region_occurrence_count(operand.ty(&body.local_decls, tcx));
                match operand_local(operand) {
                    Some(local) if layout.local_slots(local).len() == slots => {
                        for slot in layout.local_slots(local) {
                            scratch.extend_from_slice(&state[layout.slot_words(slot)]);
                        }
                    }
                    None if matches!(operand, Operand::Constant(_) | Operand::RuntimeChecks(_)) => {
                        scratch.resize(scratch.len() + slots * layout.words_per_set, 0);
                    }
                    _ => {
                        scratch.resize(scratch.len() + slots * layout.words_per_set, 0);
                        let start = scratch.len() - slots * layout.words_per_set;
                        for slot in 0..slots {
                            let word = start + slot * layout.words_per_set + layout.unknown_bit / 64;
                            scratch[word] |= 1 << (layout.unknown_bit % 64);
                        }
                    }
                }
            }
            layout.clear_local(state, destination);
            if scratch.len() == destination_range.len() * layout.words_per_set {
                for (index, slot) in destination_range.enumerate() {
                    let start = index * layout.words_per_set;
                    state[layout.slot_words(slot)]
                        .copy_from_slice(&scratch[start..start + layout.words_per_set]);
                }
            } else {
                layout.set_unknown_local(state, destination);
            }
        }
        _ => {
            if has_region_occurrence(rvalue.ty(&body.local_decls, tcx)) {
                layout.set_unknown_local(state, destination);
            } else {
                layout.clear_local(state, destination);
            }
        }
    }
}

fn switch_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    block: BasicBlock,
    discr: &Operand<'tcx>,
) -> Option<u128> {
    let typing_env = ty::TypingEnv::post_analysis(tcx, body.source.def_id());
    let constant = match discr {
        Operand::Constant(constant) => Some(constant),
        Operand::Copy(place) | Operand::Move(place) => {
            let local = place.as_local()?;
            let statement = body.basic_blocks[block].statements.last()?;
            let StatementKind::Assign(assign) = &statement.kind else { return None };
            let (destination, Rvalue::Use(Operand::Constant(constant), _)) = &**assign else {
                return None;
            };
            (destination.as_local() == Some(local)).then_some(constant)
        }
        Operand::RuntimeChecks(_) => None,
    }?;
    constant.const_.try_eval_bits(tcx, typing_env)
}


pub(crate) fn infer<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::LocalDefId,
) -> &'tcx OriginContractAnalysis<'tcx> {
    tcx.arena.alloc(infer_inner(tcx, def_id))
}

fn infer_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::LocalDefId,
) -> OriginContractAnalysis<'tcx> {
    let generics = tcx.generics_of(def_id);
    if generics.own_origin_lifetime_count() == 0 {
        return OriginContractAnalysis::Contract(OriginContract { requirements: &[] });
    }

    let (body, _) = tcx.mir_promoted(def_id);
    let body = body.borrow();
    let sig = tcx.liberate_late_bound_regions(
        def_id.to_def_id(),
        tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip(),
    );

    assert!(sig.inputs().len() <= body.arg_count);
    let mut input_region_offsets = Vec::with_capacity(sig.inputs().len() + 1);
    let mut input_regions = Vec::new();
    input_region_offsets.push(0);
    for input in sig.inputs() {
        input_regions.extend(region_occurrences(*input));
        input_region_offsets.push(input_regions.len());
    }

    let mut sources = Vec::<RegionSlot>::new();
    for &region in &input_regions {
        if region.is_static() {
            continue;
        }
        let Some(source) = region_slot(tcx, def_id, region) else {
            continue;
        };
        if !sources.contains(&source) {
            sources.push(source);
        }
    }

    let layout = Layout::new(&body, sources.len());
    let mut start = vec![0u64; layout.state_words()];
    for local_index in 1..=body.arg_count {
        let local = Local::from_usize(local_index);
        let slots = layout.local_slots(local);
        let Some(&region_start) = input_region_offsets.get(local_index - 1) else {
            for slot in slots {
                layout.set_bit(&mut start, slot, layout.unknown_bit);
            }
            continue;
        };
        let Some(&region_end) = input_region_offsets.get(local_index) else {
            for slot in slots {
                layout.set_bit(&mut start, slot, layout.unknown_bit);
            }
            continue;
        };
        let regions = &input_regions[region_start..region_end];
        assert_eq!(slots.len(), regions.len());
        for (slot, &region) in slots.zip(regions) {
            if region.is_static() {
                continue;
            }
            if let Some(source) = region_slot(tcx, def_id, region)
                && let Some(source_index) = sources.iter().position(|&candidate| candidate == source)
            {
                layout.set_bit(&mut start, slot, source_index);
            } else {
                layout.set_bit(&mut start, slot, layout.unknown_bit);
            }
        }
    }

    let state_words = layout.state_words();
    let mut entries = vec![0u64; body.basic_blocks.len() * state_words];
    entries[..state_words].copy_from_slice(&start);
    let mut reached = vec![false; body.basic_blocks.len()];
    reached[rustc_middle::mir::START_BLOCK.index()] = true;
    let mut queued = vec![false; body.basic_blocks.len()];
    queued[rustc_middle::mir::START_BLOCK.index()] = true;
    let mut queue = VecDeque::from([rustc_middle::mir::START_BLOCK]);
    let output_slots = layout.local_slots(RETURN_PLACE).len();
    let mut returned = vec![0u64; output_slots * layout.words_per_set];
    let mut state = vec![0u64; state_words];
    let mut edge_state = vec![0u64; state_words];
    let mut rvalue_scratch = Vec::with_capacity(layout.max_local_slots() * layout.words_per_set);
    while let Some(block) = queue.pop_front() {
        queued[block.index()] = false;
        let entry_start = block.index() * state_words;
        state.copy_from_slice(&entries[entry_start..entry_start + state_words]);
        let data = &body.basic_blocks[block];

        for statement in &data.statements {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    if let Some(destination) = place.as_local() {
                        assign_rvalue(tcx, &body, &layout, &mut state, &mut rvalue_scratch, destination, rvalue);
                    } else if has_region_occurrence(place.ty(&*body, tcx).ty) {
                        layout.set_unknown_local(&mut state, place.local);
                    }
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    layout.clear_local(&mut state, *local);
                }
                _ => {}
            }
        }

        let terminator = data.terminator();
        match &terminator.kind {
            TerminatorKind::Return => {
                for (output, slot) in layout.local_slots(RETURN_PLACE).enumerate() {
                    let destination =
                        &mut returned[output * layout.words_per_set..(output + 1) * layout.words_per_set];
                    merge_state(destination, &state[layout.slot_words(slot)]);
                }
            }
            TerminatorKind::SwitchInt { discr, targets, .. } => {
                if let Some(value) = switch_value(tcx, &body, block, discr) {
                    propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, targets.target_for_value(value), &state);
                } else {
                    for target in terminator.successors() {
                        propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, target, &state);
                    }
                }
            }
            TerminatorKind::Call { args, destination, target, .. } => {
                if let Some(target) = target {
                    if args.iter().any(|arg| has_region_occurrence(arg.node.ty(&body.local_decls, tcx))) {
                        return OriginContractAnalysis::Unrepresentable(OriginContractError {
                            span: terminator.source_info.span,
                            kind: OriginContractErrorKind::CallMayMutateOrigin,
                        });
                    }
                    edge_state.copy_from_slice(&state);
                    if let Some(destination) = destination.as_local() {
                        if !layout.local_slots(destination).is_empty() {
                            layout.set_unknown_local(&mut edge_state, destination);
                        }
                    } else if has_region_occurrence(destination.ty(&*body, tcx).ty) {
                        layout.set_unknown_local(&mut edge_state, destination.local);
                    }
                    propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, *target, &edge_state);
                    for successor in terminator.successors().filter(|successor| successor != target) {
                        propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, successor, &state);
                    }
                } else {
                    for successor in terminator.successors() {
                        propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, successor, &state);
                    }
                }
            }
            TerminatorKind::Drop { place, target, .. } => {
                if has_region_occurrence(place.ty(&*body, tcx).ty) {
                    return OriginContractAnalysis::Unrepresentable(OriginContractError {
                        span: terminator.source_info.span,
                        kind: OriginContractErrorKind::DropMayMutateOrigin,
                    });
                }
                propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, *target, &state);
                for successor in terminator.successors().filter(|successor| successor != target) {
                    propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, successor, &state);
                }
            }
            _ => {
                for target in terminator.successors() {
                    propagate_state(&mut entries, &mut reached, &mut queued, &mut queue, state_words, target, &state);
                }
            }
        }
    }

    let output_regions = region_occurrences(sig.output());
    assert_eq!(output_regions.len(), output_slots);
    let mut requirements = Vec::new();
    for (output, region) in output_regions.into_iter().enumerate() {
        let Some(target) = origin_slot(tcx, def_id, region) else { continue };
        let words = &returned[output * layout.words_per_set..(output + 1) * layout.words_per_set];
        if words[layout.unknown_bit / 64] & (1 << (layout.unknown_bit % 64)) != 0 {
            return OriginContractAnalysis::Unrepresentable(OriginContractError {
                span: body.span,
                kind: OriginContractErrorKind::UnrepresentableValue,
            });
        }
        for (source_index, &source) in sources.iter().enumerate() {
            if words[source_index / 64] & (1 << (source_index % 64)) != 0 {
                requirements.push(OriginRequirement::new(source, target));
            }
        }
    }

    let requirements = tcx.arena.alloc_slice(&requirements);
    OriginContractAnalysis::Contract(OriginContract { requirements })
}
