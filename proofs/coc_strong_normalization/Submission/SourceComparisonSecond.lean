import Submission.SourceSubstitutionExtension

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem sourceGridEval_encoded_compare_second (hA : BoundedTyping (r + 2) Γ A (.srt s))
    (hB : BoundedTyping (r + 2) Δ B (.srt s)) (hencA : SourceGridEncodedTerm A)
    (hencB : SourceGridEncodedTerm B) (hρ : SourceGridContextFirst r Γ ρ)
    (hδ : SourceGridContextFirst r Δ δ)
    (hTy : SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Δ δ B)) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ A) (sourceGridEval r Δ δ B) := by
  have h₁ := sourceGridEval_encode_second hA hencA hρ
  have h₂ := sourceGridEval_encode_second hB hencB hδ
  have he := uniformUniverseEncode_prefix_conversion (r + 1) 2 (by omega) s _ _ hTy
    (sourceGridInterpretation_formed hA ρ)
  exact fun i hi => (h₁ i hi).trans ((he i hi).trans (h₂ i hi).symm)

/-- Annotation conversion in a lambda transports both its codomain carrier
and its body evaluation under the converted declaration. -/
theorem sourceGridEval_lam_type_second (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hPi' : BoundedTyping (r + 2) Γ (.pi A' B) (.srt s'))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hb' : BoundedTyping (r + 2) (A' :: Γ) b B)
    (hc : Conv A A') (hρ : SourceGridCompatible r 2 Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.lam A b)) (sourceGridEval r Γ ρ (.lam A' b)) := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  obtain ⟨sA', hA', hsA'⟩ := hPi'.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi.pi_codomain
  have hDA := sourceGrid_type_conv_first (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hρ.first hc
  have hup (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
      SourceGridCompatible r 2 (A' :: Γ) (push x ρ) :=
    hρ.up_second hA' (hDA.code.coherent_forward 2 (by omega) (Nat.le_refl _) _
      (hx.mono (hd := Nat.le_refl (r + 2)) (by omega)))
  have h₁ := sourceGridEval_lam_typed_second hPi hb hρ.first
  have h₂ := sourceGridEval_lam_typed_second hPi' hb' hρ.first
  have he := finiteTypeLambda_prefix_congr r 2 (by omega)
    (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ A')
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A') hDA.code
    (fun x hx => ((sourceGrid_context_conversion_first hB hA hA' hc (hup x hx).first).2 sB hB).symm.code)
    ((sourceGridMeaning r b).bodyMap Γ ρ A) ((sourceGridMeaning r b).bodyMap Γ ρ A')
    (fun x hx i hi => ((sourceGrid_context_conversion_second hb hA hA' hc (hup x hx)).1 i hi).symm)
  exact fun i hi => (h₁ i hi).trans ((he i hi).trans (h₂ i hi).symm)

end Submission.Helpers
