import Submission.SourceGridStage

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- The new source value has its inferred carrier at the current coordinate.
Both environment and value-prefix projections are accounted for explicitly. -/
theorem sourceGridStep_code (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    ((sourceGridStep r j hj old t).eval Γ ρ ⟨j, Nat.lt_succ_of_le hj⟩).code =
      ((old (chosenType (r + 2) Γ t)).interp Γ ρ).carrier.code j hj
        (FiniteGridValue.toTower _ ((sourceGridStep r j hj old t).eval Γ ρ)) := by
  let ε := GridEnvironment.truncate (j + 1) ρ
  have hε : GridEnvironment.Agree (j + 1) ε ρ := GridEnvironment.truncate_below ρ (j + 1)
  change ((sourceGridStep r j hj old t).rawValue Γ ε ⟨j, Nat.lt_succ_of_le hj⟩).code = _
  obtain ⟨v, hv⟩ := sourceGridStep_rawValue r j hj old t Γ ε
  rw [hv, sourceGridForcedValue_code]
  unfold sourceGridInferred
  rw [(old (chosenType (r + 2) Γ t)).interp_causal Γ ε ρ j hj (hε.mono (by omega))]
  apply ((old (chosenType (r + 2) Γ t)).interp Γ ρ).carrier.causal
  apply FiniteGridValue.Agree.toTower
  intro i hi
  exact ((old t).eval_causal Γ ε ρ i (hε.mono (by omega))).trans
    ((sourceGridStep_eval_before r j hj old t Γ ρ i hi).symm)

theorem sourceGridStages_eval_before (r : Nat) (e : Nat) (he : e ≤ r + 2)
    (d : Nat) (hd : d ≤ e) (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    FiniteGridValue.Agree d ((sourceGridStages r e he t).eval Γ ρ)
      ((sourceGridStages r d (by omega) t).eval Γ ρ) := by
  induction e with
  | zero => intro i hi; omega
  | succ e ih =>
    by_cases hde : d = e + 1
    · subst d; intro i hi; rfl
    · intro i hi
      exact (sourceGridStep_eval_before r e (by omega) (sourceGridStages r e (by omega)) t Γ ρ i (by omega)).trans
        (ih (by omega) (by omega) i hi)

theorem sourceGridStages_interp_before (r : Nat) (e : Nat) (he : e ≤ r + 2)
    (d : Nat) (hd : d ≤ e) (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (i : Nat) (hi : i ≤ r + 1) (hid : i ≤ d) (v : TowerFamily (carrierGrid (r + 1))) :
    ((sourceGridStages r e he t).interp Γ ρ).carrier.code i hi v =
      ((sourceGridStages r d (by omega) t).interp Γ ρ).carrier.code i hi v := by
  induction e with
  | zero =>
    have hdz : d = 0 := by omega
    subst d
    rfl
  | succ e ih =>
    by_cases hde : d = e + 1
    · subst d; rfl
    · exact (sourceGridStep_interp_before r e (by omega) (sourceGridStages r e (by omega))
        t Γ ρ i hi (by omega) v).trans (ih (by omega) (by omega))

/-- Every computed prefix satisfies the carrier equations of the type chosen
for the source term. This is an inference invariant, not normalization or
invariance under conversion to another source type. -/
theorem sourceGridStages_coherent (r : Nat) (d : Nat) (hd : d ≤ r + 2)
    (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    ((sourceGridStages r d hd (chosenType (r + 2) Γ t)).interp Γ ρ).carrier.Coherent d hd
      (FiniteGridValue.toTower _ ((sourceGridStages r d hd t).eval Γ ρ)) := by
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    let old := sourceGridStages r d (by omega)
    intro i hi
    by_cases hid : i < d
    · have hp := sourceGridStep_eval_before r d (by omega) old t Γ ρ
      calc
        _ = (FiniteGridValue.toTower _ ((old t).eval Γ ρ) i).code :=
          congrArg TowerValue.code (hp.toTower i hid)
        _ = ((old (chosenType (r + 2) Γ t)).interp Γ ρ).carrier.code i (by omega)
            (FiniteGridValue.toTower _ ((old t).eval Γ ρ)) := ih (by omega) i hid
        _ = ((old (chosenType (r + 2) Γ t)).interp Γ ρ).carrier.code i (by omega)
            (FiniteGridValue.toTower _ ((sourceGridStep r d (by omega) old t).eval Γ ρ)) :=
          ((old (chosenType (r + 2) Γ t)).interp Γ ρ).carrier.causal i (by omega) _ _
            (fun k hk => (hp.toTower k (by omega)).symm)
        _ = _ := (sourceGridStep_interp_before r d (by omega) old (chosenType (r + 2) Γ t)
          Γ ρ i (by omega) (by omega) _).symm
    · have hie : i = d := by omega
      subst i
      rw [FiniteGridValue.toTower_at _ _ ⟨d, by omega⟩]
      change ((sourceGridStep r d (by omega) old t).eval Γ ρ ⟨d, by omega⟩).code = _
      exact (sourceGridStep_code r d (by omega) old t Γ ρ).trans
        (sourceGridStep_interp_before r d (by omega) old (chosenType (r + 2) Γ t)
          Γ ρ d (by omega) (Nat.le_refl _) _).symm

theorem sourceGridEval_inferred (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (t : Tm) :
    (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)).Valid (sourceGridEval r Γ ρ t) :=
  sourceGridStages_coherent r (r + 2) (Nat.le_refl _) t Γ ρ

end Submission.Helpers
