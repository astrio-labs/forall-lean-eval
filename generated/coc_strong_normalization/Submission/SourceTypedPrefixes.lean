import Submission.SourceBetaSecond

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Typed application can use its declared product through the second
stage; all inferred product choices have been compared by source conversion. -/
theorem sourceGridEval_app_typed_second (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (ha : BoundedTyping (r + 2) Γ a A) (hρ : SourceGridContextFirst r Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.app f a))
      (sourceGridApply r Γ ρ A B (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a)) := by
  have hc := sourceGridEval_app_native_second hf ha hρ
  have hp := sourceGridChosenProduct_first hf hρ
  have he : FiniteGridValue.Agree 2 (sourceGridNativeApp r Γ ρ f a)
      (sourceGridApply r Γ ρ A B (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a)) := by
    unfold sourceGridNativeApp sourceGridApply
    exact finiteTypeApplication_prefix_congr r 2 (by omega) _ _ _ _ hp.1.code
      (fun x hx => (hp.2 x hx).code) _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
  exact fun i hi => (hc i hi).trans (he i hi)

theorem sourceGridEval_lam_typed_second (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hρ : SourceGridContextFirst r Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.lam A b))
      (finiteTypeLambda r (sourceGridInterpretation r Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
        ((sourceGridMeaning r b).bodyMap Γ ρ A)) := by
  have hc := sourceGridEval_lam_native_second hPi hb hρ
  have he : FiniteGridValue.Agree 2 (sourceGridNativeLambda r Γ ρ A b)
      (finiteTypeLambda r (sourceGridInterpretation r Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
        ((sourceGridMeaning r b).bodyMap Γ ρ A)) := by
    unfold sourceGridNativeLambda
    apply finiteTypeLambda_prefix_congr r 2 (by omega)
    · exact (FiniteGridTypeEq.refl _).codeEqBelow 2
    · intro x hx
      exact (sourceGrid_type_conv_first (chosenType_typing hb).type_expression hb.type_expression
        (hρ.up (sourceGridValid_arity hx)) (typing_unique (chosenType_typing hb).forget hb.forget)).code
    · intro x hx i hi; rfl
  exact fun i hi => (hc i hi).trans (he i hi)

theorem sourceGridEval_app_compare_second (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (hg : BoundedTyping (r + 2) Γ g (.pi A B)) (ha : BoundedTyping (r + 2) Γ a A)
    (hb : BoundedTyping (r + 2) Γ b A) (hρ : SourceGridContextFirst r Γ ρ)
    (hfg : FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ g))
    (hab : FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ a) (sourceGridEval r Γ ρ b)) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.app f a)) (sourceGridEval r Γ ρ (.app g b)) := by
  have h₁ := sourceGridEval_app_typed_second hf ha hρ
  have h₂ := sourceGridEval_app_typed_second hg hb hρ
  have he := finiteTypeApplication_prefix_congr r 2 (by omega)
    (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ A)
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
    ((FiniteGridTypeEq.refl _).codeEqBelow 2) (fun x _ => (FiniteGridTypeEq.refl _).codeEqBelow 2)
    _ _ _ _ hfg hab
  exact fun i hi => (h₁ i hi).trans ((he i hi).trans (h₂ i hi).symm)

theorem sourceGridEval_lam_body_second (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hc : BoundedTyping (r + 2) (A :: Γ) c B)
    (hρ : SourceGridContextFirst r Γ ρ)
    (he : ∀ x, (sourceGridInterpretation r Γ ρ A).Valid x →
      FiniteGridValue.Agree 2 (sourceGridEval r (A :: Γ) (push x ρ) b) (sourceGridEval r (A :: Γ) (push x ρ) c)) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.lam A b)) (sourceGridEval r Γ ρ (.lam A c)) := by
  have h₁ := sourceGridEval_lam_typed_second hPi hb hρ
  have h₂ := sourceGridEval_lam_typed_second hPi hc hρ
  have hL := finiteTypeLambda_prefix_congr r 2 (by omega)
    (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ A)
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
    ((FiniteGridTypeEq.refl _).codeEqBelow 2) (fun x _ => (FiniteGridTypeEq.refl _).codeEqBelow 2)
    ((sourceGridMeaning r b).bodyMap Γ ρ A) ((sourceGridMeaning r c).bodyMap Γ ρ A) he
  exact fun i hi => (h₁ i hi).trans ((hL i hi).trans (h₂ i hi).symm)

end Submission.Helpers
