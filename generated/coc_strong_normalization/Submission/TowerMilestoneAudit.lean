import Submission

/-!
Reproducible signature and transitive-axiom audit for the semantic tower and
uniform source-model interface. Run:

  lake env lean Submission/TowerMilestoneAudit.lean

The final two original benchmark declarations intentionally still report
`sorryAx`: the full uniform source-model family is still missing. Bound three is audited
separately in `ThirdMilestoneAudit.lean`.
-/

open Submission.Helpers

#check tower_universe_roundtrip
#check tower_universe_injective
#check fiber_universe_roundtrip
#check tower_dependent_application
#check tower_dependent_abstraction
#check tower_dependent_beta
#check tower_candidate_family_roundtrip
#check tower_candidate_family_injective
#check tower_refinement_abstraction
#check bounded_model_fundamental
#check bounded_model_normalization
#check fiberBoundedModel
#check normalization_of_successor_models

#print axioms tower_universe_roundtrip
#print axioms tower_universe_injective
#print axioms fiber_universe_roundtrip
#print axioms TowerType.depPi_apply
#print axioms TowerType.depPi_lambda
#print axioms TowerType.shapePi_apply
#print axioms TowerType.shapePi_lambda
#print axioms TowerType.depPi_value_apply
#print axioms TowerType.universePi_value_apply
#print axioms tower_dependent_application
#print axioms tower_dependent_abstraction
#print axioms tower_dependent_beta
#print axioms TowerType.refinementPi_apply
#print axioms TowerType.refinementPi_lambda
#print axioms TowerValue.refinementBeta
#print axioms CandidateAtom.encode_decode_family
#print axioms tower_candidate_family_roundtrip
#print axioms tower_candidate_family_injective
#print axioms tower_refinement_abstraction
#print axioms BoundedModel.RealizesContext.up
#print axioms bounded_model_fundamental
#print axioms bounded_model_normalization
#print axioms normalization_of_bounded_models
#print axioms normalization_of_successor_models
#print axioms fiberBoundedModel
#print axioms fiber_model_normalization
#print axioms bound_two_fundamental
#print axioms bound_two_normalization

#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId_app
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.step_polyId_app
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.subject_reduction
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
