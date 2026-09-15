import Submission.SourceContextSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem SourceTransportStage.lam_native_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2)
    (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hρ : SourceGridCompatible r d Γ ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.lam A b)) (sourceGridNativeLambda r Γ ρ A b) := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  exact sourceGridEval_lam_native_prefix (S.conversion_input hd) hPi hb hρ
    (fun x hx => S.extend hA hρ (hx.mono (hd := Nat.le_refl (r + 2)) S.depth))

theorem SourceTransportStage.app_native_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (ha : BoundedTyping (r + 2) Γ a A) (hρ : SourceGridCompatible r d Γ ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.app f a)) (sourceGridNativeApp r Γ ρ f a) := by
  have hF := chosenProduct_typing hf
  obtain ⟨sPi, hPi⟩ := hF.pi_type
  obtain ⟨sD, hD, hsD⟩ := hPi.pi_domain
  obtain ⟨sC, hC, hsC⟩ := hPi.pi_codomain
  have haD := BoundedTyping.conv ha hD (conv_symm (chosenProduct_conv hf).1) hsD
  have hApp := BoundedTyping.app hF haD
  have hChosen := chosenType_typing (BoundedTyping.app hf ha)
  have hOuter := S.conversion_law hChosen.type_expression hApp.type_expression hρ
    (typing_unique hChosen.forget hApp.forget)
  have hSub := ((S.single_substitution hC hD haD hρ).2 sC hC).code
  have hNative := finiteTypeApplication_prefix_coherent r (d + 1) hd
    (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1)
    ((sourceGridMeaning r (chosenProduct (r + 2) Γ f).2).bodyFamily Γ ρ (chosenProduct (r + 2) Γ f).1)
    (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a) (S.typed_coherent_next hd haD hρ)
  rw [sourceGridEval_app_normalize]
  exact FiniteGridType.normalizeValue_recover_prefix _ (d + 1) hd _
    ((hOuter.code.trans hSub).coherent_backward (d + 1) hd (Nat.le_refl _) _ hNative)

theorem SourceTransportStage.chosen_product (S : SourceTransportStage r d) (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (hρ : SourceGridCompatible r d Γ ρ) :
    SourceTypeEqPrefix d (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1)
      (sourceGridInterpretation r Γ ρ A) ∧
    (∀ x, (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1).Valid x →
      SourceTypeEqPrefix d
        (sourceGridInterpretation r ((chosenProduct (r + 2) Γ f).1 :: Γ) (push x ρ) (chosenProduct (r + 2) Γ f).2)
        (sourceGridInterpretation r (A :: Γ) (push x ρ) B)) := by
  have hF := chosenProduct_typing hf
  obtain ⟨sPi, hPi⟩ := hF.pi_type
  obtain ⟨sD, hD, hsD⟩ := hPi.pi_domain
  obtain ⟨sC, hC, hsC⟩ := hPi.pi_codomain
  obtain ⟨sPi', hPi'⟩ := hf.pi_type
  obtain ⟨sA, hA, hsA⟩ := hPi'.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi'.pi_codomain
  have hc := chosenProduct_conv hf
  refine ⟨S.conversion_law (.inl ⟨sD, hD⟩) (.inl ⟨sA, hA⟩) hρ hc.1, ?_⟩
  intro x hx
  have hctx := S.extend hD hρ (hx.mono (hd := Nat.le_refl (r + 2)) S.depth)
  have hB' := hB.context_conv hA hD hsA (conv_symm hc.1)
  have hCod := S.conversion_law (.inl ⟨sC, hC⟩) (.inl ⟨sB, hB'⟩) hctx hc.2
  exact hCod.trans ((S.context_law hB hA hD (conv_symm hc.1) hctx).2 sB hB)

end Submission.Helpers
