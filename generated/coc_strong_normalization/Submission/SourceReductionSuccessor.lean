import Submission.SourceComparisonSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- The successor source stage is invariant under the trusted full reduction
relation, including both annotation reductions and reductions under binders. -/
theorem SourceTransportStage.step_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (h : BoundedTyping (r + 2) Γ t T)
    (hρ : SourceGridCompatible r (d + 1) Γ ρ) (hs : Step t u) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ t) (sourceGridEval r Γ ρ u) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ t) (sourceGridInterpretation r Γ ρ u)) := by
  induction hs generalizing Γ T ρ with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, hc⟩ := h.generation
    obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping (r + 2) Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hconv).1) hsA
    have hv := S.beta_next hd hPi hb ha' hρ
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval (S.conversion_input hd) hsort (hsort.preservation (.beta A b a))
      (by have hh := hsort.app_below_top; omega) (hρ.mono (Nat.le_succ d)) hv
  | appFun a hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv := S.app_compare_next hd hf (hf.preservation hs) ha ha (hρ.mono (Nat.le_succ d))
      (ih hf hρ).1 (fun _ _ => rfl)
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval (S.conversion_input hd) hsort (hsort.preservation (.appFun a hs))
      (by have hh := hsort.app_below_top; omega) (hρ.mono (Nat.le_succ d)) hv
  | appArg f hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv := S.app_compare_next hd hf hf ha (ha.preservation hs) (hρ.mono (Nat.le_succ d))
      (fun _ _ => rfl) (ih ha hρ).1
    refine ⟨hv, ?_⟩
    intro q hsort
    exact sourceTypeEqPrefix_of_eval (S.conversion_input hd) hsort (hsort.preservation (.appArg f hs))
      (by have hh := hsort.app_below_top; omega) (hρ.mono (Nat.le_succ d)) hv
  | @lamTy A A' b hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have hA' := hA.preservation hs
    have hconv : Conv A A' := .fwd (.refl _) hs
    have hb' := hb.context_conv hA hA' hsA hconv
    refine ⟨?_, ?_⟩
    · exact S.lam_type_next hd hPi (hPi.preservation (.piDom B hs)) hb hb' hconv hρ
    · intro q hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    refine ⟨?_, ?_⟩
    · apply S.lam_body_next hd hPi hb (hb.preservation hs) (hρ.mono (Nat.le_succ d))
      intro x hx
      obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
      exact (ih hb (S.extend_next hd hA hρ (hx.mono (hd := Nat.le_refl (r + 2)) hd))).1
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
        SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r (A :: Γ) (push x ρ) B)
          (sourceGridInterpretation r (A' :: Γ) (push x ρ) B) :=
      ((S.context_next hd hB hA hA' hconv
        (S.extend_next hd hA' hρ (hDA.code.coherent_forward (d + 1) hd (by omega) _
          (hx.mono (hd := Nat.le_refl (r + 2)) hd)))).2 sB hB).symm
    have hTy : SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ (.pi A B))
        (sourceGridInterpretation r Γ ρ (.pi A' B)) := by
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r (d + 1) _ _ _ _ hDA hDB
    exact ⟨S.encoded_compare_next hd ht ht' (Or.inr ⟨A, B, rfl⟩)
      (Or.inr ⟨A', B, rfl⟩) (hρ.mono (Nat.le_succ d)) (hρ.mono (Nat.le_succ d)) hTy, fun _ _ => hTy⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hsortBound, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hsortBound
    have ht' := ht.preservation (.piCod A hs)
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
        SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r (A :: Γ) (push x ρ) B)
          (sourceGridInterpretation r (A :: Γ) (push x ρ) B') :=
      (ih hB (S.extend_next hd hA hρ (hx.mono (hd := Nat.le_refl (r + 2)) hd))).2 sB hB
    have hTy : SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ (.pi A B))
        (sourceGridInterpretation r Γ ρ (.pi A B')) := by
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r (d + 1) _ _ _ _ (SourceTypeEqPrefix.of_eq (d + 1) rfl) hDB
    exact ⟨S.encoded_compare_next hd ht ht' (Or.inr ⟨A, B, rfl⟩)
      (Or.inr ⟨A, B', rfl⟩) (hρ.mono (Nat.le_succ d)) (hρ.mono (Nat.le_succ d)) hTy, fun _ _ => hTy⟩

theorem SourceTransportStage.steps_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (h : BoundedTyping (r + 2) Γ t T)
    (hρ : SourceGridCompatible r (d + 1) Γ ρ) (hs : Steps t u) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ t) (sourceGridEval r Γ ρ u) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ t) (sourceGridInterpretation r Γ ρ u)) := by
  induction hs with
  | refl => exact ⟨fun _ _ => rfl, fun _ _ => SourceTypeEqPrefix.of_eq (d + 1) rfl⟩
  | head hs hr ih =>
    have h₁ := S.step_next hd h hρ hs
    have h₂ := ih (h.preservation hs)
    exact ⟨fun i hi => (h₁.1 i hi).trans (h₂.1 i hi),
      fun s ht => (h₁.2 s ht).trans (h₂.2 s (ht.preservation hs))⟩

theorem SourceTransportStage.type_red_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hA : FiberTypeExpression (r + 2) Γ A)
    (hρ : SourceGridCompatible r (d + 1) Γ ρ) (hr : Red A B) :
    SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) := by
  rcases hA with ⟨s, hA⟩ | ⟨s, he⟩
  · exact (S.steps_next hd hA hρ hr.steps).2 s hA
  · exact SourceTypeEqPrefix.of_eq (d + 1) (congrArg (sourceGridInterpretation r Γ ρ) (he.trans (red_srt hr s he).symm))

/-- Coherent carrier conversion through the successor carrier prefix, uniformly
in the source bound, follows from typed reduction and confluence. -/
theorem SourceTransportStage.conversion_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hA : FiberTypeExpression (r + 2) Γ A)
    (hB : FiberTypeExpression (r + 2) Γ B) (hρ : SourceGridCompatible r (d + 1) Γ ρ) (hc : Conv A B) :
    SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (S.type_red_next hd hA hρ hC).trans (S.type_red_next hd hB hρ hC').symm

end Submission.Helpers
