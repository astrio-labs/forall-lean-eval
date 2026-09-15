import Submission.SourceGridEnvironments

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem sourceGridStages_variable (r d : Nat) (hd : d ≤ r + 2) (Γ : List Tm)
    (ρ : GridEnvironment (r + 1)) (x : Nat)
    (hx : (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).Valid (ρ x)) :
    FiniteGridValue.Agree d ((sourceGridStages r d hd (.var x)).eval Γ ρ) (ρ x) := by
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    let old := sourceGridStages r d (by omega)
    intro i hi
    by_cases hid : i.val < d
    · exact (sourceGridStep_eval_before r d (by omega) old (.var x) Γ ρ i hid).trans (ih (by omega) i hid)
    · have hie : i.val = d := by omega
      obtain ⟨i, hi'⟩ := i
      dsimp only at hie
      subst i
      let ε := GridEnvironment.truncate (d + 1) ρ
      have hε : GridEnvironment.Agree (d + 1) ε ρ := GridEnvironment.truncate_below ρ (d + 1)
      have hp : FiniteGridValue.Agree d ((old (.var x)).eval Γ ε) (ρ x) := by
        intro k hk
        exact ((old (.var x)).eval_causal Γ ε ρ k (hε.mono (by omega))).trans (ih (by omega) k hk)
      have hc : sourceGridInferred r d (by omega) old Γ ε (.var x) =
          (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).carrier.code d (by omega)
            (FiniteGridValue.toTower _ (ρ x)) := by
        unfold sourceGridInferred
        calc
          _ = ((old (chosenType (r + 2) Γ (.var x))).interp Γ ρ).carrier.code d (by omega)
              (FiniteGridValue.toTower _ ((old (.var x)).eval Γ ε)) :=
            (old (chosenType (r + 2) Γ (.var x))).interp_causal Γ ε ρ d (by omega) (hε.mono (by omega)) _
          _ = (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).carrier.code d (by omega)
              (FiniteGridValue.toTower _ ((old (.var x)).eval Γ ε)) :=
            (sourceGridStages_interp_before r (r + 2) (Nat.le_refl _) d (by omega)
              (chosenType (r + 2) Γ (.var x)) Γ ρ d (by omega) (Nat.le_refl _) _).symm
          _ = _ := (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).carrier.causal d (by omega) _ _ hp.toTower
      have hxc : (ρ x ⟨d, hi'⟩).code = sourceGridInferred r d (by omega) old Γ ε (.var x) := by
        have hh := hx d hi'
        rw [FiniteGridValue.toTower_at _ _ ⟨d, hi'⟩] at hh
        exact hh.trans hc.symm
      change sourceGridForcedValue r d (by omega) old Γ ε (.var x) (ε x ⟨d, hi'⟩) ⟨d, hi'⟩ = _
      unfold sourceGridForcedValue
      rw [FiniteGridValue.set_same, hε x ⟨d, hi'⟩ (Nat.lt_succ_self d)]
      exact (ρ x ⟨d, hi'⟩).mk_cast hxc

/-- Variables evaluate to their environment entries under code-compatible
admissibility. No variable typing or normalization theorem is assumed. -/
theorem sourceGridEval_variable (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (hρ : SourceGridAdmissible r Γ ρ) (x : Nat) : sourceGridEval r Γ ρ (.var x) = ρ x := by
  funext i
  exact sourceGridStages_variable r (r + 2) (Nat.le_refl _) Γ ρ x (hρ x) i i.isLt

end Submission.Helpers
