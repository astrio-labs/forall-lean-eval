import Submission

/- This audit concerns the uniform carrier grid and its first source
refinement. Full strong normalization still has its explicit admitted gap. -/

#check Submission.Helpers.carrierGridArrows
#check Submission.Helpers.carrierGridQuantifiers
#check Submission.Helpers.carrierGrid_all_small
#check Submission.Helpers.carrierGrid_pi_small
#check Submission.Helpers.LayerCode.universe_decode_encode_iff
#check Submission.Helpers.carrierGridPrefixRepresentation
#check Submission.Helpers.carrierGridVertical
#check Submission.Helpers.carrierGridUniverseNext
#check Submission.Helpers.carrierGridUniverseBottom
#check Submission.Helpers.carrierGrid_binder_beta
#check Submission.Helpers.carrierGridBinderCandidate_lambda
#check Submission.Helpers.carrierGrid_candidate_family_roundtrip
#check Submission.Helpers.firstGridShape_pi
#check Submission.Helpers.firstGridShape_subst
#check Submission.Helpers.firstGridShape_conv
#check Submission.Helpers.firstGridBeta
#check Submission.Helpers.upperGridSemantics_typed_code
#check Submission.Helpers.upperGridSemantics_form
#check Submission.Helpers.upperGridSemantics_decode
#check Submission.Helpers.upperGridSemantics_subst_value
#check Submission.Helpers.upperGridSemantics_subst_carrier
#check Submission.Helpers.upperGridSemantics_carrier_conv
#check Submission.Helpers.secondGrid_environments
#check Submission.Helpers.secondGridBeta

#print axioms Submission.Helpers.carrierGridArrows
#print axioms Submission.Helpers.carrierGridQuantifiers
#print axioms Submission.Helpers.carrierGrid_arrow_beta
#print axioms Submission.Helpers.carrierGrid_all_beta
#print axioms Submission.Helpers.carrierGrid_arrow_small
#print axioms Submission.Helpers.carrierGrid_all_small
#print axioms Submission.Helpers.carrierGrid_pi_small
#print axioms Submission.Helpers.LayerCode.universe_decode_encode_iff
#print axioms Submission.Helpers.LayerCode.universe_decode_product
#print axioms Submission.Helpers.carrierGrid_encode_pi
#print axioms Submission.Helpers.carrierGrid_horizontal_roundtrip
#print axioms Submission.Helpers.carrierGrid_prefix_roundtrip
#print axioms Submission.Helpers.carrierGrid_vertical_code_roundtrip
#print axioms Submission.Helpers.carrierGrid_vertical_value_roundtrip
#print axioms Submission.Helpers.carrierGrid_universe_next_roundtrip
#print axioms Submission.Helpers.carrierGrid_universe_bottom_roundtrip
#print axioms Submission.Helpers.carrierGrid_telescope_beta
#print axioms Submission.Helpers.carrierGrid_binder_beta
#print axioms Submission.Helpers.carrierGridBinderCandidate_apply
#print axioms Submission.Helpers.carrierGridBinderCandidate_lambda
#print axioms Submission.Helpers.carrierGrid_candidate_family_roundtrip
#print axioms Submission.Helpers.MiddleCode.recode_roundtrip
#print axioms Submission.Helpers.firstGridCode_pi
#print axioms Submission.Helpers.firstGridShape_pi
#print axioms Submission.Helpers.firstGridShape_at_universe
#print axioms Submission.Helpers.firstGridShape_lower
#print axioms Submission.Helpers.firstGridShape_ren
#print axioms Submission.Helpers.firstGridShape_substitute
#print axioms Submission.Helpers.firstGridShape_subst
#print axioms Submission.Helpers.firstGridShape_step
#print axioms Submission.Helpers.firstGridShape_conv
#print axioms Submission.Helpers.inferredFirstGrid_eq
#print axioms Submission.Helpers.inferredFirstGrid_subst
#print axioms Submission.Helpers.FirstGridContext.up
#print axioms Submission.Helpers.FirstGridContext.var_code
#print axioms Submission.Helpers.defaultFirstGridEnv_context
#print axioms Submission.Helpers.firstGridShape_top_sort
#print axioms Submission.Helpers.firstGridUniverse_carrier
#print axioms Submission.Helpers.firstGrid_universe_roundtrip
#print axioms Submission.Helpers.firstGridUniverseEncode_typed
#print axioms Submission.Helpers.firstGridApply_code
#print axioms Submission.Helpers.firstGridBeta
#print axioms Submission.Helpers.firstGridLambda_typed
#print axioms Submission.Helpers.upperGridSemantics_typed_code
#print axioms Submission.Helpers.upperGridSemantics_pi
#print axioms Submission.Helpers.upperGridProduct_isSmall
#print axioms Submission.Helpers.upperGridProduct_isArity
#print axioms Submission.Helpers.upperGridSemantics_form
#print axioms Submission.Helpers.firstGridShape_sort
#print axioms Submission.Helpers.inferredFirstGrid_sort
#print axioms Submission.Helpers.upperGridEncode_typed_code
#print axioms Submission.Helpers.upperGridSemantics_pi_value
#print axioms Submission.Helpers.upperGridSemantics_sort_value
#print axioms Submission.Helpers.upperGridDecode_encode_low
#print axioms Submission.Helpers.upperGridDecode_encode_high
#print axioms Submission.Helpers.upperGridSemantics_pi_decode_low
#print axioms Submission.Helpers.upperGridSemantics_pi_decode_high
#print axioms Submission.Helpers.upperGridSemantics_decode
#print axioms Submission.Helpers.firstGridApply_congr
#print axioms Submission.Helpers.firstGridLambda_congr
#print axioms Submission.Helpers.firstGridProduct_types_conv
#print axioms Submission.Helpers.upperGridSemantics_lam
#print axioms Submission.Helpers.upperGridSemantics_app
#print axioms Submission.Helpers.upperGridSemantics_pi_compare
#print axioms Submission.Helpers.upperGridSemantics_ren
#print axioms Submission.Helpers.upperGridSemantics_substitute_related
#print axioms Submission.Helpers.upperGridSemantics_subst_value
#print axioms Submission.Helpers.upperGridSemantics_subst_carrier
#print axioms Submission.Helpers.upperGridSemantics_context_conversion
#print axioms Submission.Helpers.upperGridSemantics_beta_value
#print axioms Submission.Helpers.upperGridSemantics_step
#print axioms Submission.Helpers.upperGridSemantics_value_conv
#print axioms Submission.Helpers.upperGridSemantics_carrier_conv
#print axioms Submission.Helpers.inferredSecondGrid_eq
#print axioms Submission.Helpers.inferredSecondGrid_ren
#print axioms Submission.Helpers.inferredSecondGrid_substitute_related
#print axioms Submission.Helpers.inferredSecondGrid_step
#print axioms Submission.Helpers.secondGridShape_subst
#print axioms Submission.Helpers.secondGridShape_conv
#print axioms Submission.Helpers.SecondGridContext.up
#print axioms Submission.Helpers.SecondGridContext.var_code
#print axioms Submission.Helpers.secondGrid_environments
#print axioms Submission.Helpers.CarrierQuantifiers.twoBeta
#print axioms Submission.Helpers.CarrierQuantifiers.twoValueBeta
#print axioms Submission.Helpers.secondGridLambda_code
#print axioms Submission.Helpers.secondGridApply_code
#print axioms Submission.Helpers.secondGridLambda_typed
#print axioms Submission.Helpers.secondGridApply_typed
#print axioms Submission.Helpers.secondGridBeta
#print axioms Submission.Helpers.bound_three_normalization

/- Next source obligation: evaluate coordinate two using `secondGridApply`
and `secondGridLambda`, pairing those values with coordinate-three carrier
families. Prove their universe factorization and decoding as done here for
coordinate one. The uniform carrier algebra, horizontal/vertical retractions,
and universe-step objects are available for this extension. The full model
must iterate through all coordinates and finally supply candidate realization.
No `BoundedModel 4` or normalization theorem above bound three is claimed. -/
