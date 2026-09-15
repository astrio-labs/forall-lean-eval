import Submission

/-! Reproducible signature and axiom audit for the bound-two milestone.
Run with `lake env lean Submission/FiberMilestoneAudit.lean`.
The two full benchmark declarations at the end intentionally still report `sorryAx`.
-/

open Submission.Helpers

#check fiberSemantics_substitute_related
#check fiberSemantics_subst_value
#check fiberSemantics_subst_candidate
#check fiberCandidatePi_apply_subst
#check fiberSemantics_app_candidate
#check fiberSemantics_context_conversion
#check fiberSemantics_step
#check fiberSemantics_candidate_conv
#check FiberRealizesContext.up
#check FiberRealizesContext.identity
#check fiberEnvironment_exists
#check bound_two_fundamental
#check bound_two_normalization

#print axioms fiberSemantics_decode
#print axioms fiberSemantics_pi_compare
#print axioms fiberSemantics_ren
#print axioms fiberSemantics_substitute_related
#print axioms fiberSemantics_subst_value
#print axioms fiberSemantics_subst_candidate
#print axioms fiberCandidatePi_apply_subst
#print axioms fiberSemantics_app_candidate
#print axioms shapeEval_lam_apply
#print axioms fiberSemantics_below_compare
#print axioms fiberSemantics_context
#print axioms fiberSemantics_context_conversion
#print axioms fiberSemantics_beta_value
#print axioms fiberSemantics_step
#print axioms fiberSemantics_steps_value
#print axioms fiberSemantics_steps_candidate
#print axioms fiberSemantics_value_conv
#print axioms fiberSemantics_candidate_conv
#print axioms type_fiberSemantics_conv
#print axioms FiberRealizesContext.up
#print axioms FiberRealizesContext.identity
#print axioms defaultShapeEnv_admissible
#print axioms defaultFiberEnv_admissible
#print axioms fiberEnvironment_exists
#print axioms bound_two_fundamental
#print axioms bound_two_normalization

#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.typing_polyId_app
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.step_polyId_app
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.subject_reduction
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.strong_normalization
#print axioms Submission.LeanEval.ProgramVerification.CoCStrongNormalization.consistency
