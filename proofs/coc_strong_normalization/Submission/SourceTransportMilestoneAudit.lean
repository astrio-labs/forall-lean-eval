import Submission

/-!
Round-ten checkpoint: source transport by retained semantic coordinates.
137 new declarations, including 121 theorems, in 25 proof modules.

New actual source results, all uniform in source bound r+2:
* First value coordinate: typed renaming and simultaneous/single substitution,
  beta equality, all Step/Steps reductions (including annotations and binders),
  and conversion of type expressions. Conversion compares the first two
  carrier coordinates.
* Second value coordinate: typed renaming, simultaneous and single
  substitution, context conversion, declared-type prefix coherence, inert
  casts for universe introductions, applications and lambdas, universe
  elimination through three type carriers, and actual beta equality.
* SourceGridCompatible r d is an inhabited variable-compatibility invariant
  for well-formed contexts. Its extension theorem needs only argument
  coherence through d; later argument coordinates are unrestricted.
  At depth two, context conversion preserves this invariant as well.

Reusable stage theorems:
sourceGrid_rename_stage consumes carrier equalities below d and context
extension, producing value equality below d and type equality through d.
sourceGrid_substitute_stage consumes preceding carrier comparisons,
conversion below d and already-established renaming at d, producing the
same substitution prefixes. Its admissibility predicate is a parameter,
so the world may strengthen as the induction advances. Neither frontier
contains a substitution value equation, candidate equation, reducibility
fundamental lemma, or normalization assumption. Universe elimination and
lambda-cast removal also work at arbitrary d from preceding carrier
conversion. SourceTypeEqPrefix compares candidates when d reaches the last
value coordinate. These generic theorems include that boundary.

The generic frontier premises are concretely discharged at d=1 for
renaming and d=2 for renaming and substitution. They have NOT yet been
discharged for every d. Two retained semantic coordinates do not bound the
source universe level. No new unconditional normalization bound or
BoundedModel n for n >= 4 is claimed. Bound three remains the strongest
proved unconditional normalization theorem. The original full
strong_normalization remains explicitly admitted; consistency depends on it.

Next concrete obligation: prove sourceGrid_step_second under
SourceGridCompatible r 2, covering every Step constructor and its type
interpretation, then derive source type conversion through three carriers
by confluence. Actual beta, typed application/lambda operations, body
congruence, context conversion, and partial-context extension are available.
The substitution environment extension up_coherent allows this construction
to compare chosen and substituted domains through a prefix, without
requiring full argument validity in both domains.
Then replace the concrete first-to-second frontier construction by a
coordinate induction assembling renaming, substitution and conversion at
every depth, including candidates, before building BoundedModel (r+2).
-/

-- SourcePrefixTools
#print axioms Submission.Helpers.CausalGridType.Agree.codeEqBelow
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.coherent_forward
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.coherent_backward
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.symm
#print axioms Submission.Helpers.finiteTypeApplication_prefix_congr
#print axioms Submission.Helpers.finiteTypeLambda_prefix_congr
#print axioms Submission.Helpers.FiniteGridType.forceCoordinate
#print axioms Submission.Helpers.FiniteGridType.normalizeValue_of_coordinates
#print axioms Submission.Helpers.FiniteGridType.normalizeValue_prefix_congr

-- SourceOperationalCore
#print axioms Submission.Helpers.sourceGridStages_eval_agree
#print axioms Submission.Helpers.sourceGridEval_current
#print axioms Submission.Helpers.sourceGridInferred_complete
#print axioms Submission.Helpers.sourceGridEval_var_coordinate
#print axioms Submission.Helpers.sourceGridEval_var_normalize
#print axioms Submission.Helpers.sourceGridNativeApp
#print axioms Submission.Helpers.sourceGridEval_app_coordinate
#print axioms Submission.Helpers.sourceGridEval_app_normalize

-- SourceOperationalLambda
#print axioms Submission.Helpers.sourceGridNativeLambda
#print axioms Submission.Helpers.sourceGridEval_lam_coordinate
#print axioms Submission.Helpers.sourceGridEval_lam_normalize
#print axioms Submission.Helpers.sourceGridNativeLambda_beta

-- SourceOperationalUniverses
#print axioms Submission.Helpers.FiniteGridType.reify_coordinate_congr
#print axioms Submission.Helpers.uniformUniverseEncode_coordinate_congr
#print axioms Submission.Helpers.sourceGridStep_rawType_complete
#print axioms Submission.Helpers.sourceGridStep_rawCandidate_complete
#print axioms Submission.Helpers.SourceGridEncodedTerm
#print axioms Submission.Helpers.sourceGridStep_encode_raw
#print axioms Submission.Helpers.sourceGridEval_encode_coordinate
#print axioms Submission.Helpers.sourceGridEval_encode_normalize

-- SourceTransportTypes
#print axioms Submission.Helpers.SourceTypeEqPrefix
#print axioms Submission.Helpers.SourceTypeEqPrefix.of_eq
#print axioms Submission.Helpers.SourceTypeEqPrefix.full
#print axioms Submission.Helpers.sourceTypeEqPrefix_pi
#print axioms Submission.Helpers.sourceTypeEqPrefix_decode
#print axioms Submission.Helpers.uniformUniverseEncode_prefix_conversion
#print axioms Submission.Helpers.GridEnvironment.RenamedBelow
#print axioms Submission.Helpers.GridEnvironment.RenamedBelow.up
#print axioms Submission.Helpers.SourceRenamingFrontier

-- SourceRenamingStep
#print axioms Submission.Helpers.sourceGrid_rename_stage

-- SourceRenamingBase
#print axioms Submission.Helpers.chosenProduct_arity_components
#print axioms Submission.Helpers.sourceRenamingBase
#print axioms Submission.Helpers.sourceGridEval_rename_zero
#print axioms Submission.Helpers.sourceGridInterpretation_rename_prefix

-- SourceUniverseBoundaryBase
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.trans
#print axioms Submission.Helpers.SourceTypeEqPrefix.symm
#print axioms Submission.Helpers.SourceTypeEqPrefix.trans
#print axioms Submission.Helpers.FiniteGridValue.agree_one
#print axioms Submission.Helpers.uniformUniverseEncode_valid
#print axioms Submission.Helpers.uniformUniverseDecode_encode
#print axioms Submission.Helpers.sourceGridEval_encode_zero
#print axioms Submission.Helpers.sourceGridInterpretation_decode_first

-- SourceSubstitutionBaseTools
#print axioms Submission.Helpers.sourceGridCode_first_of_arity
#print axioms Submission.Helpers.sourceGridInferred_sub_first
#print axioms Submission.Helpers.upSub_not_kindAt
#print axioms Submission.Helpers.sourceGridEval_variable_zero
#print axioms Submission.Helpers.GridEnvironment.SubstitutedFirst
#print axioms Submission.Helpers.GridEnvironment.SubstitutedFirst.variable
#print axioms Submission.Helpers.GridEnvironment.SubstitutedFirst.up

-- SourceSubstitutionBase
#print axioms Submission.Helpers.sourceGrid_substitute_first

-- SourceContextFirst
#print axioms Submission.Helpers.SourceGridContextFirst
#print axioms Submission.Helpers.SourceGridContextFirst.up
#print axioms Submission.Helpers.SourceGridContextFirst.variable
#print axioms Submission.Helpers.sourceGridContextFirst_exists
#print axioms Submission.Helpers.sourceGrid_subst_first
#print axioms Submission.Helpers.sourceGridEval_subst_zero
#print axioms Submission.Helpers.sourceGridInterpretation_subst_first

-- SourceContextConversionFirst
#print axioms Submission.Helpers.BoundedSubCtx.convert_head
#print axioms Submission.Helpers.sourceGrid_context_conversion_first
#print axioms Submission.Helpers.sourceTypeEqPrefix_of_eval_first
#print axioms Submission.Helpers.sourceGridInferred_step_first

-- SourceBetaFirst
#print axioms Submission.Helpers.FiniteGridType.normalizeValue_recover_prefix
#print axioms Submission.Helpers.finiteTypeLambda_beta_prefix
#print axioms Submission.Helpers.sourceGridNativeLambda_beta_prefix
#print axioms Submission.Helpers.finiteTypeApplication_zero_code
#print axioms Submission.Helpers.sourceGridNativeApp_zero_code
#print axioms Submission.Helpers.sourceGridEval_app_native_zero
#print axioms Submission.Helpers.sourceGridNativeLambda_zero_code
#print axioms Submission.Helpers.sourceGridEval_lam_native_zero
#print axioms Submission.Helpers.sourceGridEval_beta_zero

-- SourceComparisonFirst
#print axioms Submission.Helpers.sourceGridValid_arity
#print axioms Submission.Helpers.sourceGridEval_application_compare_first
#print axioms Submission.Helpers.sourceGridEval_lambda_compare_first
#print axioms Submission.Helpers.sourceGridEval_encoded_compare_first

-- SourceReductionFirst
#print axioms Submission.Helpers.sourceGrid_step_first
#print axioms Submission.Helpers.sourceGrid_steps_first
#print axioms Submission.Helpers.sourceGrid_type_red_first
#print axioms Submission.Helpers.sourceGrid_type_conv_first

-- SourceRenamingSecond
#print axioms Submission.Helpers.GridEnvironment.RenamedBelow.mono
#print axioms Submission.Helpers.sourceGrid_type_rename_first
#print axioms Submission.Helpers.sourceGridInferred_rename_second
#print axioms Submission.Helpers.sourceGridProduct_rename_second
#print axioms Submission.Helpers.sourceRenamingSecond
#print axioms Submission.Helpers.sourceGrid_rename_second

-- SourceConversionFrontier
#print axioms Submission.Helpers.SourceCarrierConversion
#print axioms Submission.Helpers.SourceTypeEqPrefix.of_full
#print axioms Submission.Helpers.sourceGridEval_coherent_of_conversion
#print axioms Submission.Helpers.sourceGridEval_encode_prefix
#print axioms Submission.Helpers.sourceGridInterpretation_decode_prefix
#print axioms Submission.Helpers.sourceTypeEqPrefix_of_eval
#print axioms Submission.Helpers.sourceCarrierConversionFirst
#print axioms Submission.Helpers.sourceGridEval_coherent_second
#print axioms Submission.Helpers.sourceGridEval_encode_second
#print axioms Submission.Helpers.sourceGridInterpretation_decode_second

-- SourceSubstitutionFrontier
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.mono
#print axioms Submission.Helpers.GridEnvironment.SubstitutedBelow
#print axioms Submission.Helpers.GridEnvironment.SubstitutedBelow.mono
#print axioms Submission.Helpers.SourceSubstitutionFrontier
#print axioms Submission.Helpers.GridEnvironment.SubstitutedBelow.variable
#print axioms Submission.Helpers.GridEnvironment.SubstitutedBelow.up

-- SourceSubstitutionStep
#print axioms Submission.Helpers.sourceGrid_substitute_stage

-- SourceSubstitutionSecond
#print axioms Submission.Helpers.GridEnvironment.SubstitutedFirst.up_arity
#print axioms Submission.Helpers.sourceGrid_type_substitute_first
#print axioms Submission.Helpers.sourceGridInferred_substitute_second
#print axioms Submission.Helpers.sourceGridProduct_substitute_second
#print axioms Submission.Helpers.sourceSubstitutionSecond
#print axioms Submission.Helpers.sourceGrid_substitute_second

-- SourceContextPrefixes
#print axioms Submission.Helpers.SourceGridCompatible
#print axioms Submission.Helpers.SourceGridCompatible.mono
#print axioms Submission.Helpers.sourceGridCompatible_exists
#print axioms Submission.Helpers.sourceGridEval_head_prefix
#print axioms Submission.Helpers.SourceGridCompatible.up
#print axioms Submission.Helpers.SourceGridCompatible.up_second
#print axioms Submission.Helpers.sourceGrid_subst_second
#print axioms Submission.Helpers.SourceGridContextFirst.convert_head
#print axioms Submission.Helpers.sourceGrid_context_conversion_second
#print axioms Submission.Helpers.SourceGridCompatible.convert_head_second

-- SourceNativePrefixes
#print axioms Submission.Helpers.finiteTypeApplication_prefix_coherent
#print axioms Submission.Helpers.sourceGridEval_lam_native_prefix
#print axioms Submission.Helpers.sourceGridEval_lam_native_second
#print axioms Submission.Helpers.sourceGridEval_app_native_second
#print axioms Submission.Helpers.sourceGridChosenProduct_first

-- SourceBetaSecond
#print axioms Submission.Helpers.sourceGridEval_beta_second

-- SourceTypedPrefixes
#print axioms Submission.Helpers.sourceGridEval_app_typed_second
#print axioms Submission.Helpers.sourceGridEval_lam_typed_second
#print axioms Submission.Helpers.sourceGridEval_app_compare_second
#print axioms Submission.Helpers.sourceGridEval_lam_body_second

#check Submission.Helpers.sourceGridEval_var_normalize
#check Submission.Helpers.sourceGridEval_app_normalize
#check Submission.Helpers.sourceGridEval_lam_normalize
#check Submission.Helpers.sourceGridEval_encode_normalize
#check Submission.Helpers.sourceGrid_rename_stage
#check Submission.Helpers.sourceGrid_substitute_stage
#check Submission.Helpers.sourceGrid_type_conv_first
#check Submission.Helpers.sourceGrid_rename_second
#check Submission.Helpers.sourceGrid_substitute_second
#check Submission.Helpers.sourceGrid_subst_second
#check Submission.Helpers.sourceGridEval_beta_second
#check Submission.Helpers.sourceGridInterpretation_decode_prefix
#check Submission.Helpers.SourceGridCompatible.up
#check Submission.Helpers.sourceGridCompatible_exists
#check Submission.Helpers.sourceGridEval_app_typed_second
#check Submission.Helpers.sourceGridEval_lam_typed_second

-- Partially coherent arguments also extend substitution environments.
#print axioms Submission.Helpers.GridEnvironment.SubstitutedBelow.up_coherent
#check Submission.Helpers.GridEnvironment.SubstitutedBelow.up_coherent

-- Preserved normalization and honest root controls.
#check Submission.Helpers.bound_three_normalization
#print axioms Submission.Helpers.bound_three_normalization
#check Submission.Helpers.bound_two_normalization
#print axioms Submission.Helpers.bound_two_normalization
#check Submission.Helpers.two_sort_normalization
#print axioms Submission.Helpers.two_sort_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
