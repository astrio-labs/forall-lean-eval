import Submission.FiberShapeSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Reduction of a formed type leaves its lower carrier unchanged. -/
theorem fiberShape_step (h : BoundedTyping n Γ A (.srt s))
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hs : Step A A') : fiberShape n i Γ ρ A v = fiberShape n i Γ ρ A' v := by
  induction A generalizing Γ s ρ v A'
  all_goals
    have h' := h.preservation hs
    apply fiberShape_compare h h' hq
      (congrArg ShapeValue.asArity (shapeEval_step h hq hρ hs))
    intro ht
    rw [fiberShape_top h ht hq, fiberShape_top h' ht hq]
  case var => cases hs
  case srt => cases hs
  case app =>
    have hh := h.app_below_top
    omega
  case lam =>
    obtain ⟨B, r, hPi, hb, hbnd, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  case pi A B ihA ihB =>
    obtain ⟨sA, sB, sC, hA, hB, hrule, hsA, hsB, hsC, hc⟩ := h.generation
    cases hs with
    | piDom B hs =>
      have hA' := hA.preservation hs
      have hconv : Conv A _ := .fwd (.refl _) hs
      apply fiberProduct_congr ((hA.goodAt hq).arity_step hs).symm
      · intro x hx
        exact ihA hA hρ hs
      · intro x hx y
        exact (fiberShape_context_conversion hB hA hA' hsA hconv hq).symm
    | piCod A hs =>
      apply fiberProduct_congr rfl
      · intro x hx
        rfl
      · intro x hx y
        exact ihB hB (hρ.up hx) hs

theorem fiberShape_steps (h : BoundedTyping n Γ A (.srt s))
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hs : Steps A A') : fiberShape n i Γ ρ A v = fiberShape n i Γ ρ A' v := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact (fiberShape_step h hq hρ hs).trans (ih (h.preservation hs))

/-- Sorts without a type at the finite bound are also allowed as type expressions. -/
def FiberTypeExpression (n : Nat) (Γ : List Tm) (A : Tm) : Prop :=
  (∃ s, BoundedTyping n Γ A (.srt s)) ∨ ∃ s, A = .srt s

theorem BoundedTyping.type_expression (h : BoundedTyping n Γ t A) :
    FiberTypeExpression n Γ A := by
  rcases h.regularity with hs | ht
  · exact .inr hs
  · exact .inl ht

theorem FiberTypeExpression.fiberShape_red (h : FiberTypeExpression n Γ A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hr : Red A B) : fiberShape n i Γ ρ A v = fiberShape n i Γ ρ B v := by
  rcases h with ⟨s, hA⟩ | ⟨s, he⟩
  · exact fiberShape_steps hA hq hρ hr.steps
  · have he' := red_srt hr s he
    rw [he, he']

theorem fiberShape_conv (hA : FiberTypeExpression n Γ A)
    (hB : FiberTypeExpression n Γ B) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) (hc : Conv A B) :
    fiberShape n i Γ ρ A v = fiberShape n i Γ ρ B v := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (hA.fiberShape_red hq hρ hC).trans (hB.fiberShape_red hq hρ hC').symm

theorem type_fiberShape_conv (h : BoundedTyping n Γ t A)
    (hB : BoundedTyping n Γ B (.srt s)) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) (hc : Conv A B) :
    fiberShape n i Γ ρ A v = fiberShape n i Γ ρ B v :=
  fiberShape_conv h.type_expression (.inl ⟨s, hB⟩) hq hρ hc

/-- Carrier inference uses typing uniqueness, so the arbitrary choice of type is immaterial. -/
noncomputable def inferredFiber (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (t : Tm) : FiberCode :=
  fiberShape n i Γ ρ (chosenType n Γ t) (shapeEval n i Γ ρ t)

theorem inferredFiber_eq (h : BoundedTyping n Γ t A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    inferredFiber n i Γ ρ t = fiberShape n i Γ ρ A (shapeEval n i Γ ρ t) := by
  have ht := chosenType_typing h
  exact fiberShape_conv ht.type_expression h.type_expression hq hρ
    (typing_unique ht.forget h.forget)

end Submission.Helpers
