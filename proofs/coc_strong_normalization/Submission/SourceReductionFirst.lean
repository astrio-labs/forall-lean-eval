import Submission.SourceComparisonFirst

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- The first source stage is invariant under the trusted full reduction
relation, including both annotation reductions and reductions under binders. -/
theorem sourceGrid_step_first (h : BoundedTyping (r + 2) Γ t T)
    (hρ : SourceGridContextFirst r Γ ρ) (hs : Step t u) :
    FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ t) (sourceGridEval r Γ ρ u) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ t) (sourceGridInterpretation r Γ ρ u)) := by
  induction hs generalizing Γ T ρ with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, hc⟩ := h.generation
    obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping (r + 2) Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hconv).1) hsA
    have hv := FiniteGridValue.agree_one (sourceGridEval_beta_zero hPi hb ha' hρ)
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval_first hsort (hsort.preservation (.beta A b a))
      (by have hh := hsort.app_below_top; omega) ρ hv
  | appFun a hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv := sourceGridEval_application_compare_first hf ha (hf.preservation hs) ha ρ ρ rfl rfl
      (ih hf hρ).1 (fun _ _ => rfl)
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval_first hsort (hsort.preservation (.appFun a hs))
      (by have hh := hsort.app_below_top; omega) ρ hv
  | appArg f hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv := sourceGridEval_application_compare_first hf ha hf (ha.preservation hs) ρ ρ rfl rfl
      (fun _ _ => rfl) (ih ha hρ).1
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval_first hsort (hsort.preservation (.appArg f hs))
      (by have hh := hsort.app_below_top; omega) ρ hv
  | @lamTy A A' b hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have hA' := hA.preservation hs
    have hconv : Conv A A' := .fwd (.refl _) hs
    have hb' := hb.context_conv hA hA' hsA hconv
    have hD := ((hA.goodAt (q := .type r) rfl).arity_step hs).symm
    refine ⟨?_, ?_⟩
    · apply sourceGridEval_lambda_compare_first hPi hb (hPi.preservation (.piDom B hs)) hb' ρ ρ hD rfl
      intro x hx
      have hctx := hρ.up ((sourceGridValid_arity hx).trans hD)
      have he := (sourceGrid_context_conversion_first hb hA hA' hconv hctx).1
      exact fun i hi => (he i hi).symm
    · intro q hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    refine ⟨?_, ?_⟩
    · apply sourceGridEval_lambda_compare_first hPi hb hPi (hb.preservation hs) ρ ρ rfl rfl
      intro x hx
      exact (ih hb (hρ.up (sourceGridValid_arity hx))).1
    · intro q hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | @piDom A A' B hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hsortBound, hc⟩ := h.generation
    have hA' := hA.preservation hs
    have hconv : Conv A A' := .fwd (.refl _) hs
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hsortBound
    have ht' := ht.preservation (.piDom B hs)
    have hD := ((hA.goodAt (q := .type r) rfl).arity_step hs).symm
    have hDA := (ih hA hρ).2 sA hA
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
        SourceTypeEqPrefix 1 (sourceGridInterpretation r (A :: Γ) (push x ρ) B)
          (sourceGridInterpretation r (A' :: Γ) (push x ρ) B) :=
      ((sourceGrid_context_conversion_first hB hA hA' hconv
        (hρ.up ((sourceGridValid_arity hx).trans hD))).2 sB hB).symm
    have hTy : SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ (.pi A B))
        (sourceGridInterpretation r Γ ρ (.pi A' B)) := by
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r 1 _ _ _ _ hDA hDB
    exact ⟨sourceGridEval_encoded_compare_first ht ht' (Or.inr ⟨A, B, rfl⟩)
      (Or.inr ⟨A', B, rfl⟩) ρ ρ hTy, fun _ _ => hTy⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hsortBound, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hsortBound
    have ht' := ht.preservation (.piCod A hs)
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
        SourceTypeEqPrefix 1 (sourceGridInterpretation r (A :: Γ) (push x ρ) B)
          (sourceGridInterpretation r (A :: Γ) (push x ρ) B') :=
      (ih hB (hρ.up (sourceGridValid_arity hx))).2 sB hB
    have hTy : SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ (.pi A B))
        (sourceGridInterpretation r Γ ρ (.pi A B')) := by
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r 1 _ _ _ _ (SourceTypeEqPrefix.of_eq 1 rfl) hDB
    exact ⟨sourceGridEval_encoded_compare_first ht ht' (Or.inr ⟨A, B, rfl⟩)
      (Or.inr ⟨A, B', rfl⟩) ρ ρ hTy, fun _ _ => hTy⟩

theorem sourceGrid_steps_first (h : BoundedTyping (r + 2) Γ t T)
    (hρ : SourceGridContextFirst r Γ ρ) (hs : Steps t u) :
    FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ t) (sourceGridEval r Γ ρ u) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ t) (sourceGridInterpretation r Γ ρ u)) := by
  induction hs with
  | refl => exact ⟨fun _ _ => rfl, fun _ _ => SourceTypeEqPrefix.of_eq 1 rfl⟩
  | head hs hr ih =>
    have h₁ := sourceGrid_step_first h hρ hs
    have h₂ := ih (h.preservation hs)
    exact ⟨fun i hi => (h₁.1 i hi).trans (h₂.1 i hi),
      fun s ht => (h₁.2 s ht).trans (h₂.2 s (ht.preservation hs))⟩

theorem sourceGrid_type_red_first (hA : FiberTypeExpression (r + 2) Γ A)
    (hρ : SourceGridContextFirst r Γ ρ) (hr : Red A B) :
    SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) := by
  rcases hA with ⟨s, hA⟩ | ⟨s, he⟩
  · exact (sourceGrid_steps_first hA hρ hr.steps).2 s hA
  · exact SourceTypeEqPrefix.of_eq 1 (congrArg (sourceGridInterpretation r Γ ρ) (he.trans (red_srt hr s he).symm))

/-- Coherent carrier conversion through the first two coordinates, uniformly
in the source bound, follows from typed reduction and confluence. -/
theorem sourceGrid_type_conv_first (hA : FiberTypeExpression (r + 2) Γ A)
    (hB : FiberTypeExpression (r + 2) Γ B) (hρ : SourceGridContextFirst r Γ ρ) (hc : Conv A B) :
    SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (sourceGrid_type_red_first hA hρ hC).trans (sourceGrid_type_red_first hB hρ hC').symm

end Submission.Helpers
