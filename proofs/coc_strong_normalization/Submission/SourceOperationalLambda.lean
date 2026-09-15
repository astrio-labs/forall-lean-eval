import Submission.SourceOperationalCore

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def sourceGridNativeLambda (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A b : Tm) : FiniteGridValue (r + 1) :=
  let B := chosenType (r + 2) (A :: Γ) b
  finiteTypeLambda r (sourceGridInterpretation r Γ ρ A)
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) ((sourceGridMeaning r b).bodyMap Γ ρ A)

theorem sourceGridEval_lam_coordinate (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A b : Tm) (i : Fin (r + 2)) :
    sourceGridEval r Γ ρ (.lam A b) i =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.lam A b))).forceCoordinate
        (sourceGridEval r Γ ρ (.lam A b)) i (sourceGridNativeLambda r Γ ρ A b i) := by
  obtain ⟨j, hj⟩ := i
  let old := sourceGridStages r j (by omega)
  let stage := sourceGridStages r (j + 1) (by omega)
  let ε := GridEnvironment.truncate (j + 1) ρ
  let B := chosenType (r + 2) (A :: Γ) b
  have hε : GridEnvironment.Agree (j + 1) ε ρ := GridEnvironment.truncate_below ρ (j + 1)
  have hOp : FiniteGridValue.Agree (j + 1)
      (finiteTypeLambda r ((old A).interp Γ ε) ((old B).bodyFamily Γ ε A)
        ((stage b).bodyMap Γ ε A)) (sourceGridNativeLambda r Γ ρ A b) := by
    apply finiteTypeLambda_prefix_congr r (j + 1) (by omega)
    · exact (sourceGridStages_interp_agree r j (by omega) A Γ ε ρ (hε.mono (by omega))).codeEqBelow
    · intro x hx
      exact (sourceGridStages_interp_agree r j (by omega) B (A :: Γ) (push x ε) (push x ρ)
        ((hε.mono (by omega)).push (fun _ _ => rfl))).codeEqBelow
    · intro x hx
      exact sourceGridStages_eval_agree r (j + 1) (by omega) b (A :: Γ) (push x ε) (push x ρ)
        (hε.push (fun _ _ => rfl))
  rw [sourceGridEval_current r Γ ρ (.lam A b) j (by omega)]
  change sourceGridForcedValue r j (by omega) old Γ ε (.lam A b)
    (finiteTypeLambda r ((old A).interp Γ ε) ((old B).bodyFamily Γ ε A)
      ((stage b).bodyMap Γ ε A) ⟨j, hj⟩) ⟨j, hj⟩ = _
  unfold sourceGridForcedValue
  rw [FiniteGridValue.set_same, hOp ⟨j, hj⟩ (Nat.lt_succ_self _)]
  rw [sourceGridInferred_complete r j (by omega) Γ ε ρ (hε.mono (by omega))]
  rfl

theorem sourceGridEval_lam_normalize (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A b : Tm) : sourceGridEval r Γ ρ (.lam A b) =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.lam A b))).normalizeValue
        (sourceGridNativeLambda r Γ ρ A b) :=
  ((sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.lam A b))).normalizeValue_of_coordinates
    _ _ (sourceGridEval_lam_coordinate r Γ ρ A b)).symm

/-- The native lambda satisfies beta at its inferred body family. This is
an equation of semantic values, with no source normalization premise. -/
theorem sourceGridNativeLambda_beta (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A b : Tm) (x : FiniteGridValue (r + 1))
    (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
    sourceGridApply r Γ ρ A (chosenType (r + 2) (A :: Γ) b)
      (sourceGridNativeLambda r Γ ρ A b) x = sourceGridEval r (A :: Γ) (push x ρ) b := by
  apply finiteTypeLambda_beta
  · intro a ha
    exact sourceGridEval_inferred r (A :: Γ) (push a ρ) b
  · exact hx

end Submission.Helpers
