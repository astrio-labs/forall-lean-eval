import Submission.SourceComparisonSecond

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- The second source stage is invariant under the trusted full reduction
relation, including both annotation reductions and reductions under binders. -/
theorem sourceGrid_step_second (h : BoundedTyping (r + 2) Γ t T)
    (hρ : SourceGridCompatible r 2 Γ ρ) (hs : Step t u) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ t) (sourceGridEval r Γ ρ u) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ t) (sourceGridInterpretation r Γ ρ u)) := by
  induction hs generalizing Γ T ρ with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, hc⟩ := h.generation
    obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping (r + 2) Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hconv).1) hsA
    have hv := sourceGridEval_beta_second hPi hb ha' hρ
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval (sourceCarrierConversionFirst r) hsort (hsort.preservation (.beta A b a))
      (by have hh := hsort.app_below_top; omega) hρ.first hv
  | appFun a hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv := sourceGridEval_app_compare_second hf (hf.preservation hs) ha ha hρ.first
      (ih hf hρ).1 (fun _ _ => rfl)
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval (sourceCarrierConversionFirst r) hsort (hsort.preservation (.appFun a hs))
      (by have hh := hsort.app_below_top; omega) hρ.first hv
  | appArg f hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv := sourceGridEval_app_compare_second hf hf ha (ha.preservation hs) hρ.first
      (fun _ _ => rfl) (ih ha hρ).1
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval (sourceCarrierConversionFirst r) hsort (hsort.preservation (.appArg f hs))
      (by have hh := hsort.app_below_top; omega) hρ.first hv
  | @lamTy A A' b hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have hA' := hA.preservation hs
    have hconv : Conv A A' := .fwd (.refl _) hs
    have hb' := hb.context_conv hA hA' hsA hconv
    refine ⟨?_, ?_⟩
    · exact sourceGridEval_lam_type_second hPi (hPi.preservation (.piDom B hs)) hb hb' hconv hρ
    · intro q hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    refine ⟨?_, ?_⟩
    · apply sourceGridEval_lam_body_second hPi hb (hb.preservation hs) hρ.first
      intro x hx
      obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
      exact (ih hb (hρ.up_second hA (hx.mono (hd := Nat.le_refl (r + 2)) (by omega)))).1
    · intro q hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | @piDom A A' B hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hsortBound, hc⟩ := h.generation
    have hA' := hA.preservation hs
    have hconv : Conv A A' := .fwd (.refl _) hs
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hsortBound
    have ht' := ht.preservation (.piDom B hs)
    have hDA := (ih hA hρ).2 sA hA
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
        SourceTypeEqPrefix 2 (sourceGridInterpretation r (A :: Γ) (push x ρ) B)
          (sourceGridInterpretation r (A' :: Γ) (push x ρ) B) :=
      ((sourceGrid_context_conversion_second hB hA hA' hconv
        (hρ.up_second hA' (hDA.code.coherent_forward 2 (by omega) (by omega) _
          (hx.mono (hd := Nat.le_refl (r + 2)) (by omega))))).2 sB hB).symm
    have hTy : SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ (.pi A B))
        (sourceGridInterpretation r Γ ρ (.pi A' B)) := by
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r 2 _ _ _ _ hDA hDB
    exact ⟨sourceGridEval_encoded_compare_second ht ht' (Or.inr ⟨A, B, rfl⟩)
      (Or.inr ⟨A', B, rfl⟩) hρ.first hρ.first hTy, fun _ _ => hTy⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hsortBound, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hsortBound
    have ht' := ht.preservation (.piCod A hs)
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
        SourceTypeEqPrefix 2 (sourceGridInterpretation r (A :: Γ) (push x ρ) B)
          (sourceGridInterpretation r (A :: Γ) (push x ρ) B') :=
      (ih hB (hρ.up_second hA (hx.mono (hd := Nat.le_refl (r + 2)) (by omega)))).2 sB hB
    have hTy : SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ (.pi A B))
        (sourceGridInterpretation r Γ ρ (.pi A B')) := by
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r 2 _ _ _ _ (SourceTypeEqPrefix.of_eq 2 rfl) hDB
    exact ⟨sourceGridEval_encoded_compare_second ht ht' (Or.inr ⟨A, B, rfl⟩)
      (Or.inr ⟨A, B', rfl⟩) hρ.first hρ.first hTy, fun _ _ => hTy⟩

theorem sourceGrid_steps_second (h : BoundedTyping (r + 2) Γ t T)
    (hρ : SourceGridCompatible r 2 Γ ρ) (hs : Steps t u) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ t) (sourceGridEval r Γ ρ u) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ t) (sourceGridInterpretation r Γ ρ u)) := by
  induction hs with
  | refl => exact ⟨fun _ _ => rfl, fun _ _ => SourceTypeEqPrefix.of_eq 2 rfl⟩
  | head hs hr ih =>
    have h₁ := sourceGrid_step_second h hρ hs
    have h₂ := ih (h.preservation hs)
    exact ⟨fun i hi => (h₁.1 i hi).trans (h₂.1 i hi),
      fun s ht => (h₁.2 s ht).trans (h₂.2 s (ht.preservation hs))⟩

theorem sourceGrid_type_red_second (hA : FiberTypeExpression (r + 2) Γ A)
    (hρ : SourceGridCompatible r 2 Γ ρ) (hr : Red A B) :
    SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) := by
  rcases hA with ⟨s, hA⟩ | ⟨s, he⟩
  · exact (sourceGrid_steps_second hA hρ hr.steps).2 s hA
  · exact SourceTypeEqPrefix.of_eq 2 (congrArg (sourceGridInterpretation r Γ ρ) (he.trans (red_srt hr s he).symm))

/-- Coherent carrier conversion through the first three coordinates, uniformly
in the source bound, follows from typed reduction and confluence. -/
theorem sourceGrid_type_conv_second (hA : FiberTypeExpression (r + 2) Γ A)
    (hB : FiberTypeExpression (r + 2) Γ B) (hρ : SourceGridCompatible r 2 Γ ρ) (hc : Conv A B) :
    SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (sourceGrid_type_red_second hA hρ hC).trans (sourceGrid_type_red_second hB hρ hC').symm

end Submission.Helpers
