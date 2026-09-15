import Submission.SourceTypedSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem SourceTransportStage.encoded_compare_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hA : BoundedTyping (r + 2) Γ A (.srt s))
    (hB : BoundedTyping (r + 2) Δ B (.srt s)) (hencA : SourceGridEncodedTerm A)
    (hencB : SourceGridEncodedTerm B) (hρ : SourceGridCompatible r d Γ ρ)
    (hδ : SourceGridCompatible r d Δ δ)
    (hTy : SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Δ δ B)) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ A) (sourceGridEval r Δ δ B) := by
  have h₁ := sourceGridEval_encode_prefix (S.conversion_input hd) hA hencA hρ
  have h₂ := sourceGridEval_encode_prefix (S.conversion_input hd) hB hencB hδ
  have he := uniformUniverseEncode_prefix_conversion (r + 1) (d + 1) hd s _ _ hTy
    (sourceGridInterpretation_formed hA ρ)
  exact fun i hi => (h₁ i hi).trans ((he i hi).trans (h₂ i hi).symm)

/-- Annotation conversion in a lambda transports both its codomain carrier
and its body evaluation under the converted declaration. -/
theorem SourceTransportStage.lam_type_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hPi' : BoundedTyping (r + 2) Γ (.pi A' B) (.srt s'))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hb' : BoundedTyping (r + 2) (A' :: Γ) b B)
    (hc : Conv A A') (hρ : SourceGridCompatible r (d + 1) Γ ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.lam A b)) (sourceGridEval r Γ ρ (.lam A' b)) := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  obtain ⟨sA', hA', hsA'⟩ := hPi'.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi.pi_codomain
  have hDA := S.conversion_law (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) (hρ.mono (Nat.le_succ d)) hc
  have hup (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
      SourceGridCompatible r (d + 1) (A' :: Γ) (push x ρ) :=
    S.extend_next hd hA' hρ (hDA.code.coherent_forward (d + 1) hd (Nat.le_refl _) _
      (hx.mono (hd := Nat.le_refl (r + 2)) hd))
  have h₁ := S.lam_typed_next hd hPi hb (hρ.mono (Nat.le_succ d))
  have h₂ := S.lam_typed_next hd hPi' hb' (hρ.mono (Nat.le_succ d))
  have he := finiteTypeLambda_prefix_congr r (d + 1) hd
    (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ A')
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A') hDA.code
    (fun x hx => ((S.context_law hB hA hA' hc ((hup x hx).mono (Nat.le_succ d))).2 sB hB).symm.code)
    ((sourceGridMeaning r b).bodyMap Γ ρ A) ((sourceGridMeaning r b).bodyMap Γ ρ A')
    (fun x hx i hi => ((S.context_next hd hb hA hA' hc (hup x hx)).1 i hi).symm)
  exact fun i hi => (h₁ i hi).trans ((he i hi).trans (h₂ i hi).symm)

end Submission.Helpers
