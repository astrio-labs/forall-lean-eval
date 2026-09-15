import Submission.SourceUniverseBoundaryBase

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem sourceGridCode_first_of_arity (r : Nat) (Γ Δ : List Tm)
    (ρ δ : GridEnvironment (r + 1)) (A B : Tm)
    (h : arityAt (.type r) A = arityAt (.type r) B) :
    FiniteGridCodeEqBelow 1 (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Δ δ B) := by
  intro j hj hjd v hv
  have he : j = 0 := by omega
  subst j
  rw [sourceGridInterpretation_zero, sourceGridInterpretation_zero, h]

theorem sourceGridInferred_sub_first (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false) (ρ δ : GridEnvironment (r + 1)) :
    FiniteGridCodeEqBelow 1
      (sourceGridInterpretation r Δ ρ (chosenType (r + 2) Δ (sub σ t)))
      (sourceGridInterpretation r Γ δ (chosenType (r + 2) Γ t)) :=
  sourceGridCode_first_of_arity r Δ Γ ρ δ _ _ (inferredArityAt_substitute h hw hσ hk rfl)

theorem upSub_not_kindAt (hk : ∀ j, kindAt q (σ j) = false) :
    ∀ j, kindAt q (upSub σ j) = false := by
  intro j
  cases j with
  | zero => rfl
  | succ j => exact (kindAt_ren _ _ _).trans (hk j)

theorem sourceGridEval_variable_zero (hw : BoundedWf (r + 2) Γ) (hj : Γ[j]? = some A)
    (ρ : GridEnvironment (r + 1))
    (hx : (ρ j ⟨0, by omega⟩).code = arityAt (.type r) A) :
    sourceGridEval r Γ ρ (.var j) ⟨0, by omega⟩ = ρ j ⟨0, by omega⟩ := by
  rw [sourceGridEval_var_coordinate]
  unfold FiniteGridType.forceCoordinate
  rw [sourceGridInterpretation_zero]
  have hc : arityAt (.type r) (chosenType (r + 2) Γ (.var j)) = arityAt (.type r) A :=
    inferredArityAt_var hw hj rfl
  rw [hc]
  exact (ρ j ⟨0, by omega⟩).mk_cast hx

def GridEnvironment.SubstitutedFirst (r : Nat) (Γ Δ : List Tm) (σ : Nat → Tm)
    (ρ δ : GridEnvironment (r + 1)) : Prop :=
  ∀ j A, Γ[j]? = some A → FiniteGridValue.Agree 1 (sourceGridEval r Δ ρ (σ j)) (δ j)

theorem GridEnvironment.SubstitutedFirst.variable (he : SubstitutedFirst r Γ Δ σ ρ δ)
    (hw : BoundedWf (r + 2) Γ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false) (hj : Γ[j]? = some A) :
    FiniteGridValue.Agree 1 (sourceGridEval r Δ ρ (σ j)) (sourceGridEval r Γ δ (.var j)) := by
  have hh := he j A hj ⟨0, by omega⟩ (Nat.zero_lt_succ 0)
  have hc : (δ j ⟨0, by omega⟩).code = arityAt (.type r) A := by
    rw [← hh, sourceGridEval_arity (hσ j A hj) ρ, arityAt_sub hk, ← ren_shift, arityAt_ren]
  apply FiniteGridValue.agree_one
  exact hh.trans (sourceGridEval_variable_zero hw hj δ hc).symm

theorem GridEnvironment.SubstitutedFirst.up (he : SubstitutedFirst r Γ Δ σ ρ δ)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (x : FiniteGridValue (r + 1))
    (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).Valid x) :
    SubstitutedFirst r (A :: Γ) (sub σ A :: Δ) (upSub σ) (push x ρ) (push x δ) := by
  have hA' := hA.substitute hw hσ
  intro j C hj
  apply FiniteGridValue.agree_one
  cases j with
  | zero =>
    have hc := hx 0 (Nat.zero_lt_succ _)
    rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hc
    exact sourceGridEval_variable_zero (.cons hw hA') (j := 0) rfl (push x ρ) hc
  | succ j =>
    have hh := sourceGridEval_rename_zero (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A))
      (ρ := ρ) (δ := push x ρ) (by intro i D hi; exact FiniteGridValue.agree_one rfl)
    exact hh.trans (he j C hj ⟨0, by omega⟩ (Nat.zero_lt_succ 0))

end Submission.Helpers
