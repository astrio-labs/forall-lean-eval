import Submission.SourceBetaSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Typed application can use its declared product through the successor
stage; all inferred product choices have been compared by source conversion. -/
theorem SourceTransportStage.app_typed_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (ha : BoundedTyping (r + 2) Γ a A) (hρ : SourceGridCompatible r d Γ ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.app f a))
      (sourceGridApply r Γ ρ A B (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a)) := by
  have hc := S.app_native_next hd hf ha hρ
  have hp := S.chosen_product hf hρ
  have he : FiniteGridValue.Agree (d + 1) (sourceGridNativeApp r Γ ρ f a)
      (sourceGridApply r Γ ρ A B (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a)) := by
    unfold sourceGridNativeApp sourceGridApply
    exact finiteTypeApplication_prefix_congr r (d + 1) hd _ _ _ _ hp.1.code
      (fun x hx => (hp.2 x hx).code) _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
  exact fun i hi => (hc i hi).trans (he i hi)

theorem SourceTransportStage.lam_typed_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hρ : SourceGridCompatible r d Γ ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.lam A b))
      (finiteTypeLambda r (sourceGridInterpretation r Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
        ((sourceGridMeaning r b).bodyMap Γ ρ A)) := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  have hc := S.lam_native_next hd hPi hb hρ
  have he : FiniteGridValue.Agree (d + 1) (sourceGridNativeLambda r Γ ρ A b)
      (finiteTypeLambda r (sourceGridInterpretation r Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
        ((sourceGridMeaning r b).bodyMap Γ ρ A)) := by
    unfold sourceGridNativeLambda
    apply finiteTypeLambda_prefix_congr r (d + 1) hd
    · exact (FiniteGridTypeEq.refl _).codeEqBelow (d + 1)
    · intro x hx
      exact (S.conversion_law (chosenType_typing hb).type_expression hb.type_expression
        (S.extend hA hρ (hx.mono (hd := Nat.le_refl (r + 2)) S.depth)) (typing_unique (chosenType_typing hb).forget hb.forget)).code
    · intro x hx i hi; rfl
  exact fun i hi => (hc i hi).trans (he i hi)

theorem SourceTransportStage.app_compare_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (hg : BoundedTyping (r + 2) Γ g (.pi A B)) (ha : BoundedTyping (r + 2) Γ a A)
    (hb : BoundedTyping (r + 2) Γ b A) (hρ : SourceGridCompatible r d Γ ρ)
    (hfg : FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ g))
    (hab : FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ a) (sourceGridEval r Γ ρ b)) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.app f a)) (sourceGridEval r Γ ρ (.app g b)) := by
  have h₁ := S.app_typed_next hd hf ha hρ
  have h₂ := S.app_typed_next hd hg hb hρ
  have he := finiteTypeApplication_prefix_congr r (d + 1) hd
    (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ A)
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
    ((FiniteGridTypeEq.refl _).codeEqBelow (d + 1)) (fun x _ => (FiniteGridTypeEq.refl _).codeEqBelow (d + 1))
    _ _ _ _ hfg hab
  exact fun i hi => (h₁ i hi).trans ((he i hi).trans (h₂ i hi).symm)

theorem SourceTransportStage.lam_body_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hc : BoundedTyping (r + 2) (A :: Γ) c B)
    (hρ : SourceGridCompatible r d Γ ρ)
    (he : ∀ x, (sourceGridInterpretation r Γ ρ A).Valid x →
      FiniteGridValue.Agree (d + 1) (sourceGridEval r (A :: Γ) (push x ρ) b) (sourceGridEval r (A :: Γ) (push x ρ) c)) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.lam A b)) (sourceGridEval r Γ ρ (.lam A c)) := by
  have h₁ := S.lam_typed_next hd hPi hb hρ
  have h₂ := S.lam_typed_next hd hPi hc hρ
  have hL := finiteTypeLambda_prefix_congr r (d + 1) hd
    (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ A)
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
    ((FiniteGridTypeEq.refl _).codeEqBelow (d + 1)) (fun x _ => (FiniteGridTypeEq.refl _).codeEqBelow (d + 1))
    ((sourceGridMeaning r b).bodyMap Γ ρ A) ((sourceGridMeaning r c).bodyMap Γ ρ A) he
  exact fun i hi => (h₁ i hi).trans ((hL i hi).trans (h₂ i hi).symm)

end Submission.Helpers
