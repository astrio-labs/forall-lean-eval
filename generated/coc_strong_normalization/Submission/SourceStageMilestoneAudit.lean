import Submission

/-!
Round-nine checkpoint: a uniform source interpreter for bounds r+2.

The successor stage is defined by structural term recursion and uses the
previous stage for chosen-type carriers. It advances value coordinate j
and type-carrier coordinate j+1; the last stage supplies the candidate.
Both environment dependencies and prefix stability are proved. The full
interpreter has inferred-type validity, source typing formation, exact Pi
and sort interpretations, admissible environments, and the variable value
law. Source variables and applications interpret as universe decoding of
their computed values. These are statements about the actual source
interpreter, not just abstract finite carrier operations.

Semantic Pi types, application, and lambda values respect equality of
carriers on coherent data and candidates on valid values. Codomain and
body comparisons require equality only at valid domain arguments.
The prefix versions constrain only retained carrier coordinates and body
values; later coordinates and candidates are unconstrained. Universe
encoding before its final candidate coordinate respects equality one
carrier coordinate further. These versions support coordinate induction
without assuming whole semantic type equality in the induction step.

The root full strong_normalization theorem is still admitted. This cycle
adds no BoundedModel n for n >= 4 and no unconditional normalization bound.
Inferred-type validity is not validity at every convertible declared type.
Admissible environments exist, but context extension by a declared type
still needs the weakening/conversion laws.

Next concrete obligation: prove typed renaming/context transport and
substitution for sourceGridEval and sourceGridInterpretation by coordinate
induction, simultaneously with conversion at each completed prefix. Use
coherent Pi/application/lambda congruence to compare chosen products and
inferred types. Then derive declared-type validity, context extension,
application/abstraction equations, and candidate conversion, and assemble
BoundedModel (r+2). No source normalization premise is available for this
construction and no decrease in the source universe bound is assumed.
-/

-- FiniteTruncation
#print axioms Submission.Helpers.FiniteGridValue.Agree
#print axioms Submission.Helpers.FiniteGridValue.truncate
#print axioms Submission.Helpers.FiniteGridValue.truncate_congr
#print axioms Submission.Helpers.FiniteGridValue.truncate_below
#print axioms Submission.Helpers.FiniteGridValue.truncate_full
#print axioms Submission.Helpers.FiniteGridValue.truncate_nested
#print axioms Submission.Helpers.FiniteGridValue.Agree.mono
#print axioms Submission.Helpers.FiniteGridValue.Agree.toTower
#print axioms Submission.Helpers.FiniteGridValue.agree_ofTower
#print axioms Submission.Helpers.GridEnvironment
#print axioms Submission.Helpers.GridEnvironment.Agree
#print axioms Submission.Helpers.GridEnvironment.truncate
#print axioms Submission.Helpers.GridEnvironment.truncate_congr
#print axioms Submission.Helpers.GridEnvironment.truncate_below
#print axioms Submission.Helpers.GridEnvironment.truncate_nested
#print axioms Submission.Helpers.GridEnvironment.Agree.mono
#print axioms Submission.Helpers.GridEnvironment.Agree.push
#print axioms Submission.Helpers.GridEnvironment.truncate_push
#print axioms Submission.Helpers.FiniteGridValue.set
#print axioms Submission.Helpers.FiniteGridValue.set_same
#print axioms Submission.Helpers.FiniteGridValue.set_other
#print axioms Submission.Helpers.FiniteGridValue.set_below

-- UniformUniverseIO
#print axioms Submission.Helpers.finiteValueCast
#print axioms Submission.Helpers.finiteTypeCast
#print axioms Submission.Helpers.FiniteGridType.trivial
#print axioms Submission.Helpers.uniformUniverseEncode
#print axioms Submission.Helpers.uniformUniverseDecode
#print axioms Submission.Helpers.finiteUniverseEncode_cast
#print axioms Submission.Helpers.finiteUniverseDecode_cast
#print axioms Submission.Helpers.uniformUniverseEncode_at
#print axioms Submission.Helpers.uniformUniverseDecode_at

-- SourceGridMeaning
#print axioms Submission.Helpers.SourceGridMeaning
#print axioms Submission.Helpers.SourceGridMeaning.eval
#print axioms Submission.Helpers.SourceGridMeaning.interp
#print axioms Submission.Helpers.SourceGridMeaning.eval_causal
#print axioms Submission.Helpers.SourceGridMeaning.eval_agree
#print axioms Submission.Helpers.SourceGridMeaning.interp_causal
#print axioms Submission.Helpers.SourceGridMeaning.bodyMap
#print axioms Submission.Helpers.SourceGridMeaning.bodyFamily
#print axioms Submission.Helpers.sourceGridUpgrade
#print axioms Submission.Helpers.sourceGridUpgrade_before
#print axioms Submission.Helpers.sourceGridBaseType
#print axioms Submission.Helpers.sourceGridBase
#print axioms Submission.Helpers.sourceGridInferred
#print axioms Submission.Helpers.sourceGridForcedValue
#print axioms Submission.Helpers.sourceGridForcedValue_code

-- SourceGridStage
#print axioms Submission.Helpers.sourceGridStep
#print axioms Submission.Helpers.sourceGridStep_rawValue
#print axioms Submission.Helpers.sourceGridStep_rawType
#print axioms Submission.Helpers.sourceGridStep_eval_before
#print axioms Submission.Helpers.sourceGridStep_interp_before
#print axioms Submission.Helpers.sourceGridStages
#print axioms Submission.Helpers.sourceGridMeaning
#print axioms Submission.Helpers.sourceGridEval
#print axioms Submission.Helpers.sourceGridInterpretation
#print axioms Submission.Helpers.sourceGridEval_causal
#print axioms Submission.Helpers.sourceGridInterpretation_causal

-- SourceGridCoherence
#print axioms Submission.Helpers.sourceGridStep_code
#print axioms Submission.Helpers.sourceGridStages_eval_before
#print axioms Submission.Helpers.sourceGridStages_interp_before
#print axioms Submission.Helpers.sourceGridStages_coherent
#print axioms Submission.Helpers.sourceGridEval_inferred

-- SourceGridProducts
#print axioms Submission.Helpers.sourceGridApply
#print axioms Submission.Helpers.sourceGridApply_valid
#print axioms Submission.Helpers.sourceGridInterpretation_pi_candidate
#print axioms Submission.Helpers.sourceGridInterpretation_sort_candidate
#print axioms Submission.Helpers.sourceGridInterpretation_sort_canonical
#print axioms Submission.Helpers.sourceGridInterpretation_canonical_product

-- SourceGridFormationUniform
#print axioms Submission.Helpers.uniformUniverseDecode_formed
#print axioms Submission.Helpers.sourceGridUpgrade_formed
#print axioms Submission.Helpers.SourceGridMeaning.interp_formed
#print axioms Submission.Helpers.sourceGridBaseType_formed
#print axioms Submission.Helpers.sourceGridStep_raw_formed
#print axioms Submission.Helpers.sourceGridStages_formed
#print axioms Submission.Helpers.sourceGridInterpretation_formed

-- GridPrefixAgreement
#print axioms Submission.Helpers.CausalGridType.Agree
#print axioms Submission.Helpers.CausalGridType.Agree.mono
#print axioms Submission.Helpers.CausalGridType.telescopeAt_congr
#print axioms Submission.Helpers.UniversePrefix.rowArguments
#print axioms Submission.Helpers.prefixBindingObject
#print axioms Submission.Helpers.gridBindingObject_prefix
#print axioms Submission.Helpers.prefixPiCode
#print axioms Submission.Helpers.prefixPiApply
#print axioms Submission.Helpers.gridPiCode_prefix
#print axioms Submission.Helpers.gridPiApplyAt_prefix

-- GridOperationLocality
#print axioms Submission.Helpers.gridPiCode_types_congr
#print axioms Submission.Helpers.gridPiApplyAt_types_congr
#print axioms Submission.Helpers.gridApplicationPrefix_types_congr
#print axioms Submission.Helpers.gridPiType_types_congr
#print axioms Submission.Helpers.finitePiType_carrier_congr
#print axioms Submission.Helpers.gridApplication_types_congr

-- SourceGridProductCarriers
#print axioms Submission.Helpers.sourceGridInterpretation_zero
#print axioms Submission.Helpers.sourceGridStages_interp_agree
#print axioms Submission.Helpers.gridPiType_zero
#print axioms Submission.Helpers.sourceGridInterpretation_pi_carrier
#print axioms Submission.Helpers.FiniteGridType.ext_fields
#print axioms Submission.Helpers.sourceGridInterpretation_pi

-- SourceGridSorts
#print axioms Submission.Helpers.universeSortAt_zero
#print axioms Submission.Helpers.uniformSortCode_zero
#print axioms Submission.Helpers.sourceGridInterpretation_sort_carrier
#print axioms Submission.Helpers.sourceGridInterpretation_sort
#print axioms Submission.Helpers.sourceGridEval_arity

-- SourceGridEnvironments
#print axioms Submission.Helpers.SourceGridContextPrefix
#print axioms Submission.Helpers.sourceGridEnvironmentStep
#print axioms Submission.Helpers.sourceGridEnvironmentStep_before
#print axioms Submission.Helpers.sourceGridEnvironmentStep_code
#print axioms Submission.Helpers.sourceGridEnvironmentStep_coherent
#print axioms Submission.Helpers.sourceGridEnvironmentStages
#print axioms Submission.Helpers.sourceGridEnvironmentStages_coherent
#print axioms Submission.Helpers.sourceGridEnvironment_exists
#print axioms Submission.Helpers.SourceGridAdmissible
#print axioms Submission.Helpers.sourceGrid_admissible_exists

-- SourceGridVariables
#print axioms Submission.Helpers.sourceGridStages_variable
#print axioms Submission.Helpers.sourceGridEval_variable

-- CoherentPiFields
#print axioms Submission.Helpers.FiniteGridTypeEq.telescopeAt
#print axioms Submission.Helpers.gridApplicationPrefix_partial_coherent
#print axioms Submission.Helpers.coherentPi_domain_field
#print axioms Submission.Helpers.coherentPi_codomain_field

-- CoherentPiOperations
#print axioms Submission.Helpers.prefixBindingCode_congr
#print axioms Submission.Helpers.prefixApplyFields
#print axioms Submission.Helpers.prefixPiApply_fields
#print axioms Submission.Helpers.coherentPi_codomain_fields
#print axioms Submission.Helpers.finitePiCode_coherent_eq
#print axioms Submission.Helpers.finitePiApplyAt_coherent_eq
#print axioms Submission.Helpers.finiteApplicationPrefix_coherent_eq
#print axioms Submission.Helpers.finiteTypeApplication_coherent_eq
#print axioms Submission.Helpers.finitePiType_carrier_coherent_eq

-- CoherentPiConversion
#print axioms Submission.Helpers.Candidate.ext_contains
#print axioms Submission.Helpers.finitePiType_candidate_coherent_eq
#print axioms Submission.Helpers.finitePiType_coherent_eq

-- CoherentLambdaConversion
#print axioms Submission.Helpers.finiteGridMap_eq_partial
#print axioms Submission.Helpers.prefixLambdaFields
#print axioms Submission.Helpers.prefixLambdaFields_congr
#print axioms Submission.Helpers.gridLambdaAt_fields
#print axioms Submission.Helpers.finiteLambdaAt_coherent_eq
#print axioms Submission.Helpers.finiteLambdaPrefix_coherent_eq
#print axioms Submission.Helpers.finiteTypeLambda_coherent_eq

-- SourceGridDecoding
#print axioms Submission.Helpers.uniformUniverseDecode_causal
#print axioms Submission.Helpers.uniformUniverseDecode_zero
#print axioms Submission.Helpers.GridEnvironment.truncate_full
#print axioms Submission.Helpers.sourceGridStep_raw_eval
#print axioms Submission.Helpers.SourceGridDecodedTerm
#print axioms Submission.Helpers.sourceGridStep_decode_raw
#print axioms Submission.Helpers.sourceGridInterpretation_decode_carrier
#print axioms Submission.Helpers.sourceGridInterpretation_decode_candidate
#print axioms Submission.Helpers.sourceGridInterpretation_decode
#print axioms Submission.Helpers.sourceGridInterpretation_var

-- CoherentPiPrefixes
#print axioms Submission.Helpers.FiniteGridCodeEqBelow
#print axioms Submission.Helpers.FiniteGridTypeEq.codeEqBelow
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.telescopeAt
#print axioms Submission.Helpers.coherentPi_domain_field_below
#print axioms Submission.Helpers.coherentPi_codomain_field_below
#print axioms Submission.Helpers.coherentPi_codomain_fields_below
#print axioms Submission.Helpers.finitePiCode_below_eq
#print axioms Submission.Helpers.finitePiApplyAt_below_eq
#print axioms Submission.Helpers.finiteApplicationPrefix_below_eq
#print axioms Submission.Helpers.finitePiType_carrier_below_eq

-- CoherentLambdaPrefixes
#print axioms Submission.Helpers.finiteGridMap_eq_partial_below
#print axioms Submission.Helpers.finiteLambdaAt_below_eq
#print axioms Submission.Helpers.finiteLambdaPrefix_below_eq

-- CoherentUniversePrefixes
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.universePrefix
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.universeReify_proper
#print axioms Submission.Helpers.FiniteGridCodeEqBelow.reify_prefix

-- Principal theorem statements.
#check Submission.Helpers.sourceGridEval_causal
#check Submission.Helpers.sourceGridEval_inferred
#check Submission.Helpers.sourceGridInterpretation_formed
#check Submission.Helpers.sourceGridInterpretation_pi
#check Submission.Helpers.sourceGridInterpretation_sort
#check Submission.Helpers.sourceGridEnvironment_exists
#check Submission.Helpers.sourceGrid_admissible_exists
#check Submission.Helpers.sourceGridEval_variable
#check Submission.Helpers.sourceGridInterpretation_decode
#check Submission.Helpers.sourceGridInterpretation_var
#check Submission.Helpers.finitePiType_coherent_eq
#check Submission.Helpers.finiteTypeApplication_coherent_eq
#check Submission.Helpers.finiteTypeLambda_coherent_eq

#check Submission.Helpers.finiteApplicationPrefix_below_eq
#check Submission.Helpers.finiteLambdaPrefix_below_eq
#check Submission.Helpers.FiniteGridCodeEqBelow.reify_prefix

-- Previously checked normalization and honest incomplete controls.
#print axioms Submission.Helpers.bound_three_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
