import Submission.SourcePrefixTools

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem sourceGridStages_eval_agree (r d : Nat) (hd : d ≤ r + 2) (t : Tm)
    (Γ : List Tm) (ρ δ : GridEnvironment (r + 1)) (h : GridEnvironment.Agree d ρ δ) :
    FiniteGridValue.Agree d ((sourceGridStages r d hd t).eval Γ ρ) (sourceGridEval r Γ δ t) := by
  intro i hi
  exact ((sourceGridStages r d hd t).eval_causal Γ ρ δ i (h.mono (by omega))).trans
    (sourceGridStages_eval_before r (r + 2) (Nat.le_refl _) d hd t Γ δ i hi).symm

theorem sourceGridEval_current (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (t : Tm) (j : Nat) (hj : j ≤ r + 1) :
    sourceGridEval r Γ ρ t ⟨j, Nat.lt_succ_of_le hj⟩ =
      (sourceGridStep r j hj (sourceGridStages r j (by omega)) t).rawValue
        Γ (GridEnvironment.truncate (j + 1) ρ) ⟨j, Nat.lt_succ_of_le hj⟩ :=
  sourceGridStages_eval_before r (r + 2) (Nat.le_refl _) (j + 1) (by omega) t Γ ρ
    ⟨j, Nat.lt_succ_of_le hj⟩ (Nat.lt_succ_self _)

theorem sourceGridInferred_complete (r j : Nat) (hj : j ≤ r + 1) (Γ : List Tm)
    (ρ δ : GridEnvironment (r + 1)) (h : GridEnvironment.Agree j ρ δ) (t : Tm) :
    sourceGridInferred r j hj (sourceGridStages r j (by omega)) Γ ρ t =
      (sourceGridInterpretation r Γ δ (chosenType (r + 2) Γ t)).carrier.code j hj
        (FiniteGridValue.toTower _ (sourceGridEval r Γ δ t)) := by
  unfold sourceGridInferred
  rw [sourceGridStages_interp_agree r j (by omega) (chosenType (r + 2) Γ t) Γ ρ δ h j hj (Nat.lt_succ_self _)]
  exact (sourceGridInterpretation r Γ δ (chosenType (r + 2) Γ t)).carrier.causal j hj _ _
    (sourceGridStages_eval_agree r j (by omega) t Γ ρ δ h).toTower

theorem sourceGridEval_var_coordinate (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (x : Nat) (i : Fin (r + 2)) :
    sourceGridEval r Γ ρ (.var x) i =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).forceCoordinate
        (sourceGridEval r Γ ρ (.var x)) i (ρ x i) := by
  obtain ⟨j, hj⟩ := i
  rw [sourceGridEval_current r Γ ρ (.var x) j (by omega)]
  change sourceGridForcedValue r j (by omega) (sourceGridStages r j (by omega)) Γ
    (GridEnvironment.truncate (j + 1) ρ) (.var x) _ ⟨j, hj⟩ = _
  unfold sourceGridForcedValue
  rw [FiniteGridValue.set_same,
    sourceGridInferred_complete r j (by omega) Γ _ ρ
      ((GridEnvironment.truncate_below ρ (j + 1)).mono (by omega))]
  rw [GridEnvironment.truncate_below ρ (j + 1) x ⟨j, hj⟩ (Nat.lt_succ_self _)]
  rfl

/-- This equation describes the cast performed on a source variable even
outside an admissible environment. It does not assert the cast is inert. -/
theorem sourceGridEval_var_normalize (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (x : Nat) : sourceGridEval r Γ ρ (.var x) =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).normalizeValue (ρ x) :=
  ((sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).normalizeValue_of_coordinates
    (ρ x) _ (sourceGridEval_var_coordinate r Γ ρ x)).symm

noncomputable def sourceGridNativeApp (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (f a : Tm) : FiniteGridValue (r + 1) :=
  let p := chosenProduct (r + 2) Γ f
  finiteTypeApplication r (sourceGridInterpretation r Γ ρ p.1)
    ((sourceGridMeaning r p.2).bodyFamily Γ ρ p.1)
    (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a)

theorem sourceGridEval_app_coordinate (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (f a : Tm) (i : Fin (r + 2)) :
    sourceGridEval r Γ ρ (.app f a) i =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.app f a))).forceCoordinate
        (sourceGridEval r Γ ρ (.app f a)) i (sourceGridNativeApp r Γ ρ f a i) := by
  obtain ⟨j, hj⟩ := i
  let old := sourceGridStages r j (by omega)
  let stage := sourceGridStages r (j + 1) (by omega)
  let ε := GridEnvironment.truncate (j + 1) ρ
  let p := chosenProduct (r + 2) Γ f
  have hε : GridEnvironment.Agree (j + 1) ε ρ := GridEnvironment.truncate_below ρ (j + 1)
  have hOp : FiniteGridValue.Agree (j + 1)
      (finiteTypeApplication r ((old p.1).interp Γ ε) ((old p.2).bodyFamily Γ ε p.1)
        ((stage f).eval Γ ε) ((stage a).eval Γ ε)) (sourceGridNativeApp r Γ ρ f a) := by
    apply finiteTypeApplication_prefix_congr r (j + 1) (by omega)
    · exact (sourceGridStages_interp_agree r j (by omega) p.1 Γ ε ρ (hε.mono (by omega))).codeEqBelow
    · intro x hx
      exact (sourceGridStages_interp_agree r j (by omega) p.2 (p.1 :: Γ) (push x ε) (push x ρ)
        ((hε.mono (by omega)).push (fun _ _ => rfl))).codeEqBelow
    · exact sourceGridStages_eval_agree r (j + 1) (by omega) f Γ ε ρ hε
    · exact sourceGridStages_eval_agree r (j + 1) (by omega) a Γ ε ρ hε
  rw [sourceGridEval_current r Γ ρ (.app f a) j (by omega)]
  change sourceGridForcedValue r j (by omega) old Γ ε (.app f a)
    (finiteTypeApplication r ((old p.1).interp Γ ε) ((old p.2).bodyFamily Γ ε p.1)
      ((stage f).eval Γ ε) ((stage a).eval Γ ε) ⟨j, hj⟩) ⟨j, hj⟩ = _
  unfold sourceGridForcedValue
  rw [FiniteGridValue.set_same, hOp ⟨j, hj⟩ (Nat.lt_succ_self _)]
  rw [sourceGridInferred_complete r j (by omega) Γ ε ρ (hε.mono (by omega))]
  rfl

/-- The actual source application is the native finite application followed
by the inferred-type cast. Removing this cast still needs typed conversion. -/
theorem sourceGridEval_app_normalize (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (f a : Tm) : sourceGridEval r Γ ρ (.app f a) =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.app f a))).normalizeValue
        (sourceGridNativeApp r Γ ρ f a) :=
  ((sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.app f a))).normalizeValue_of_coordinates
    _ _ (sourceGridEval_app_coordinate r Γ ρ f a)).symm

end Submission.Helpers
