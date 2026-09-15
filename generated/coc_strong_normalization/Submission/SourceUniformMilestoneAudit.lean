import Submission

/-!
Round-eleven candidate: normalization uniform in every finite universe bound.

The stage induction is noncircular. A SourceTransportStage r d records
actual renaming, substitution, context transport, conversion and compatible
context extension at retained depth d. Its next constructor first builds
renaming at d+1 from carrier comparisons through d, then substitution at
d+1 using that renaming. Context transport follows from identity substitution
and preceding context admissibility. The operational casts, typed application,
lambda and beta laws then use preceding carrier conversion. Structural
induction on Step supplies reduction at d+1, including annotation reductions;
confluence supplies conversion at d+1. This closes the successor stage.

sourceTransportStage_uniform starts at the checked first coordinate and
constructs every depth through r+2. At the last depth SourceTypeEqPrefix
includes candidate equality, and canonicalization extends it to arbitrary
finite values. No source-universe bound decrease is used or asserted.

sourceBoundedModel r supplies every BoundedModel (r+2) field from these
proved laws. Its environments recover declared variable entries; they exist
for arbitrary lists. At well-formed contexts this gives full carrier
compatibility. Point, extension, typed validity, sorts, products, weakening,
application, abstraction, substitution and conversion have concrete proofs.
The existing general fundamental lemma then gives unconditional SN at r+2.
The checked bound-one theorem covers n<=1, and typing_bounded gives full SN.

All six original candidate declarations are intended to be checked below.
The official comparator/nanoda and the fresh independent reviewer must
accept the exact candidate before the benchmark is considered complete.
-/

-- SourceComparisonSecond
#print axioms Submission.Helpers.sourceGridEval_encoded_compare_second
#print axioms Submission.Helpers.sourceGridEval_lam_type_second

-- SourceReductionSecond
#print axioms Submission.Helpers.sourceGrid_step_second
#print axioms Submission.Helpers.sourceGrid_steps_second
#print axioms Submission.Helpers.sourceGrid_type_red_second
#print axioms Submission.Helpers.sourceGrid_type_conv_second

-- SourceStageData
#print axioms Submission.Helpers.SourceTransportStage
#print axioms Submission.Helpers.sourceTransportStage_one
#print axioms Submission.Helpers.sourceTransportStage_two

-- SourceStageHelpers
#print axioms Submission.Helpers.SourceTransportStage.type_rename
#print axioms Submission.Helpers.SourceTransportStage.type_substitute
#print axioms Submission.Helpers.SourceTransportStage.context_compatible
#print axioms Submission.Helpers.SourceTransportStage.typed_coherent
#print axioms Submission.Helpers.SourceTransportStage.substitution_up
#print axioms Submission.Helpers.SourceTransportStage.single_substitution
#print axioms Submission.Helpers.SourceTransportStage.conversion_input

-- SourceRenamingSuccessor
#print axioms Submission.Helpers.SourceTransportStage.inferred_rename_next
#print axioms Submission.Helpers.SourceTransportStage.product_rename_next
#print axioms Submission.Helpers.SourceTransportStage.renaming_frontier

-- SourceSubstitutionSuccessor
#print axioms Submission.Helpers.SourceTransportStage.inferred_substitute_next
#print axioms Submission.Helpers.SourceTransportStage.product_substitute_next
#print axioms Submission.Helpers.SourceTransportStage.substitution_frontier

-- SourceContextSuccessor
#print axioms Submission.Helpers.SourceTransportStage.extend_next
#print axioms Submission.Helpers.SourceTransportStage.typed_coherent_next
#print axioms Submission.Helpers.SourceTransportStage.single_next
#print axioms Submission.Helpers.SourceTransportStage.context_next

-- SourceNativeSuccessor
#print axioms Submission.Helpers.SourceTransportStage.lam_native_next
#print axioms Submission.Helpers.SourceTransportStage.app_native_next
#print axioms Submission.Helpers.SourceTransportStage.chosen_product

-- SourceBetaSuccessor
#print axioms Submission.Helpers.SourceTransportStage.beta_next

-- SourceTypedSuccessor
#print axioms Submission.Helpers.SourceTransportStage.app_typed_next
#print axioms Submission.Helpers.SourceTransportStage.lam_typed_next
#print axioms Submission.Helpers.SourceTransportStage.app_compare_next
#print axioms Submission.Helpers.SourceTransportStage.lam_body_next

-- SourceComparisonSuccessor
#print axioms Submission.Helpers.SourceTransportStage.encoded_compare_next
#print axioms Submission.Helpers.SourceTransportStage.lam_type_next

-- SourceReductionSuccessor
#print axioms Submission.Helpers.SourceTransportStage.step_next
#print axioms Submission.Helpers.SourceTransportStage.steps_next
#print axioms Submission.Helpers.SourceTransportStage.type_red_next
#print axioms Submission.Helpers.SourceTransportStage.conversion_next

-- SourceStagesUniform
#print axioms Submission.Helpers.SourceTransportStage.next
#print axioms Submission.Helpers.sourceTransportStage_uniform
#print axioms Submission.Helpers.sourceTransportStage_full
#print axioms Submission.Helpers.sourceGridEval_typed_full
#print axioms Submission.Helpers.sourceGridInterpretation_rename_full
#print axioms Submission.Helpers.sourceGridInterpretation_subst_full
#print axioms Submission.Helpers.sourceGridInterpretation_conv_full

-- SourceFullOperations
#print axioms Submission.Helpers.sourceGridEval_rename_full
#print axioms Submission.Helpers.sourceGridEval_app_full
#print axioms Submission.Helpers.sourceGridEval_lam_full
#print axioms Submission.Helpers.sourceGrid_abstraction_full

-- SourceModel
#print axioms Submission.Helpers.sourceModelAdmissible
#print axioms Submission.Helpers.sourceModelAdmissible_compatible
#print axioms Submission.Helpers.sourceModelAdmissible_of_compatible
#print axioms Submission.Helpers.sourceModel_environment
#print axioms Submission.Helpers.sourceBoundedModel
#print axioms Submission.Helpers.sourceBoundedModel_fundamental
#print axioms Submission.Helpers.sourceBoundedModel_normalization

-- SourceNormalization
#print axioms Submission.Helpers.bounded_normalization_uniform
#print axioms Submission.Helpers.typing_normalization_uniform

#check Submission.Helpers.SourceTransportStage.next
#check Submission.Helpers.sourceTransportStage_uniform
#check Submission.Helpers.sourceTransportStage_full
#check Submission.Helpers.sourceGridInterpretation_conv_full
#check Submission.Helpers.sourceGridInterpretation_subst_full
#check Submission.Helpers.sourceBoundedModel
#check Submission.Helpers.sourceBoundedModel_fundamental
#check Submission.Helpers.sourceBoundedModel_normalization
#check Submission.Helpers.bounded_normalization_uniform
#check Submission.Helpers.typing_normalization_uniform
#print axioms Submission.Helpers.two_sort_normalization
#print axioms Submission.Helpers.bound_two_fundamental
#print axioms Submission.Helpers.bound_two_normalization
#print axioms Submission.Helpers.bound_three_normalization
#check Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId
#check Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId_app
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId_app
#check Submission.LeanEval.ProgramVerification.CoCStrongNormalization.step_polyId_app
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.step_polyId_app
#check Submission.LeanEval.ProgramVerification.CoCStrongNormalization.subject_reduction
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.subject_reduction
#check Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#check Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
