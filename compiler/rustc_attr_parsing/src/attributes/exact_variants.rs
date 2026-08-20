use rustc_feature::AttributeStability;
use rustc_hir::Target;
use rustc_hir::attrs::AttributeKind;
use rustc_span::{Span, Symbol, sym};

use crate::attributes::NoArgsAttributeParser;
use crate::target_checking::AllowedTargets;
use crate::target_checking::Policy::Allow;
use crate::unstable;

pub(crate) struct ExactVariantsParser;

impl NoArgsAttributeParser for ExactVariantsParser {
    const PATH: &[Symbol] = &[sym::exact_variants];
    const ALLOWED_TARGETS: AllowedTargets<'_> =
        AllowedTargets::AllowList(&[Allow(Target::Enum)]);
    const STABILITY: AttributeStability = unstable!(refined_enums);
    const CREATE: fn(Span) -> AttributeKind = AttributeKind::ExactVariants;
}

