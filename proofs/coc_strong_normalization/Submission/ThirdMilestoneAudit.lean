import Submission

/-!
Source bound-three checkpoint. Run `lake env lean Submission/ThirdMilestoneAudit.lean`.
The full original normalization and consistency declarations still depend on
`sorryAx`; all new bound-three claims must have only the permitted axioms.
-/
open Submission.Helpers

#check middleShape_pi
#check middleSemantics_form
#check middleSemantics_decode
#check middleSemantics_subst_carrier
#check middleSemantics_carrier_conv
#check thirdShape_pi
#check thirdSemantics_decode
#check thirdSemantics_subst_candidate
#check thirdSemantics_candidate_conv
#check thirdBoundedModel
#check bound_three_fundamental
#check bound_three_normalization
#check normalization_of_models_above_three

#print axioms MiddleCode.piBeta
#print axioms middleShape_pi
#print axioms middleShape_substitute
#print axioms middleShape_conv
#print axioms middleSemantics_form
#print axioms middleSemantics_decode
#print axioms middleSemantics_ren
#print axioms middleSemantics_substitute_related
#print axioms middleSemantics_carrier_conv
#print axioms ThirdCode.all_small
#print axioms ThirdCode.allBeta
#print axioms thirdBeta
#print axioms thirdShape_pi
#print axioms inferredThird_substitute_related
#print axioms ThirdContext.up
#print axioms thirdCandidatePi_apply
#print axioms thirdCandidatePi_lambda
#print axioms thirdDecode_encode_type_one
#print axioms thirdSemantics_decode
#print axioms thirdSemantics_lam
#print axioms thirdSemantics_app
#print axioms thirdSemantics_ren
#print axioms thirdSemantics_substitute_related
#print axioms thirdSemantics_subst_candidate
#print axioms thirdSemantics_beta_value
#print axioms thirdSemantics_step
#print axioms thirdSemantics_candidate_conv
#print axioms thirdDefaultUpper_admissible
#print axioms thirdDefaultMiddle_admissible
#print axioms thirdDefaultLower_admissible
#print axioms thirdModel_abstraction
#print axioms thirdBoundedModel
#print axioms bound_three_fundamental
#print axioms bound_three_normalization
#print axioms normalization_of_models_above_three
#print axioms bound_two_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency

#check carrierGrid_succ
#check carrierGrid_intermediate
#check carrierGrid_bottom
#check third_grid_roundtrip
#print axioms CarrierRetraction.pi
#print axioms middle_tower_roundtrip
#print axioms third_tower_roundtrip
#print axioms thirdTowerType_realizes
#print axioms thirdTowerCode_subst
#print axioms carrierGrid_succ
#print axioms carrierGrid_bottom
#print axioms carrierGrid_intermediate
#print axioms carrierGrid_inhabited
#print axioms fiberGrid_code_roundtrip
#print axioms middle_grid_roundtrip
#print axioms third_grid_roundtrip
