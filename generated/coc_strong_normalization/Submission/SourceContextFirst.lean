import Submission.SourceSubstitutionBase

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

def SourceGridContextFirst (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) : Prop :=
  ∀ j A, Γ[j]? = some A → (ρ j ⟨0, by omega⟩).code = arityAt (.type r) A

theorem SourceGridContextFirst.up (hρ : SourceGridContextFirst r Γ ρ)
    (hx : (x ⟨0, by omega⟩).code = arityAt (.type r) A) :
    SourceGridContextFirst r (A :: Γ) (push x ρ) := by
  intro j C hj
  cases j with
  | zero =>
    have he : A = C := Option.some.inj hj
    subst C
    exact hx
  | succ j => exact hρ j C hj

theorem SourceGridContextFirst.variable (hρ : SourceGridContextFirst r Γ ρ)
    (hw : BoundedWf (r + 2) Γ) (hj : Γ[j]? = some A) :
    sourceGridEval r Γ ρ (.var j) ⟨0, by omega⟩ = ρ j ⟨0, by omega⟩ :=
  sourceGridEval_variable_zero hw hj ρ (hρ j A hj)

theorem sourceGridContextFirst_exists (r : Nat) (Γ : List Tm) : ∃ ρ, SourceGridContextFirst r Γ ρ := by
  let τ j := lift (j + 1) 0 (Γ[j]?.getD (.srt .prop))
  obtain ⟨ρ, hρ⟩ := sourceGridEnvironment_exists r Γ τ
  refine ⟨ρ, ?_⟩
  intro j A hj
  have hh := hρ j 0 (Nat.zero_lt_succ _)
  rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hh
  simpa only [τ, hj, Option.getD_some, ← ren_shift, arityAt_ren] using hh

/-- Typed single substitution has no residual kind or semantic transport
premise. The environment is required to match its declared first carriers. -/
theorem sourceGrid_subst_first (hb : BoundedTyping (r + 2) (A :: Γ) b B)
    (hA : BoundedTyping (r + 2) Γ A (.srt sA)) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridContextFirst r Γ ρ) :
    FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ (subst 0 a b))
      (sourceGridEval r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b) ∧
    (∀ s, BoundedTyping (r + 2) (A :: Γ) b (.srt s) →
      SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ (subst 0 a b))
        (sourceGridInterpretation r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b)) := by
  rw [subst_eq_sub]
  apply sourceGrid_substitute_first hb ha.wf (BoundedSubCtx.single ha)
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj
    apply FiniteGridValue.agree_one
    cases j with
    | zero => rfl
    | succ j => exact hρ.variable ha.wf hj

theorem sourceGridEval_subst_zero (hb : BoundedTyping (r + 2) (A :: Γ) b B)
    (hA : BoundedTyping (r + 2) Γ A (.srt sA)) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridContextFirst r Γ ρ) :
    sourceGridEval r Γ ρ (subst 0 a b) ⟨0, by omega⟩ =
      sourceGridEval r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b ⟨0, by omega⟩ :=
  (sourceGrid_subst_first hb hA ha hρ).1 ⟨0, by omega⟩ (Nat.zero_lt_succ 0)

theorem sourceGridInterpretation_subst_first (hB : BoundedTyping (r + 2) (A :: Γ) B (.srt sB))
    (hA : BoundedTyping (r + 2) Γ A (.srt sA)) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridContextFirst r Γ ρ) :
    FiniteGridCodeEqBelow 2 (sourceGridInterpretation r Γ ρ (subst 0 a B))
      (sourceGridInterpretation r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) B) :=
  ((sourceGrid_subst_first hB hA ha hρ).2 sB hB).code

end Submission.Helpers
