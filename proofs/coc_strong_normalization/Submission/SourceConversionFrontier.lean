import Submission.SourceRenamingSecond

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- The conversion information consumed at value depth d consists only of
carrier comparisons below d. It contains no value or candidate equation. -/
structure SourceCarrierConversion (r d : Nat)
    (P : List Tm → GridEnvironment (r + 1) → Prop) : Prop where
  depth : d ≤ r + 2
  convert : ∀ {Γ ρ A B}, FiberTypeExpression (r + 2) Γ A →
    FiberTypeExpression (r + 2) Γ B → P Γ ρ → Conv A B →
    FiniteGridCodeEqBelow d (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B)

theorem SourceTypeEqPrefix.of_full {A B : FiniteGridType R} (h : FiniteGridTypeEq A B) :
    SourceTypeEqPrefix d A B := ⟨h.codeEqBelow (d + 1), fun _ => h.candidate⟩

theorem sourceGridEval_coherent_of_conversion (F : SourceCarrierConversion r d P)
    (h : BoundedTyping (r + 2) Γ t A) (hρ : P Γ ρ) :
    (sourceGridInterpretation r Γ ρ A).carrier.Coherent d F.depth
      (FiniteGridValue.toTower _ (sourceGridEval r Γ ρ t)) := by
  have ht := chosenType_typing h
  have he := F.convert ht.type_expression h.type_expression hρ (typing_unique ht.forget h.forget)
  exact he.coherent_forward d F.depth (Nat.le_refl _) _
    ((sourceGridEval_inferred r Γ ρ t).mono (hd := Nat.le_refl (r + 2)) F.depth)

/-- Inferred casts on universe introductions are inert through d as soon
as source conversion has been established through carrier d-1. -/
theorem sourceGridEval_encode_prefix (F : SourceCarrierConversion r d P)
    (h : BoundedTyping (r + 2) Γ t (.srt s)) (ht : SourceGridEncodedTerm t) (hρ : P Γ ρ) :
    FiniteGridValue.Agree d (sourceGridEval r Γ ρ t)
      (uniformUniverseEncode (r + 1) (some s) (sourceGridInterpretation r Γ ρ t)) := by
  have hChosen := chosenType_typing h
  have he := F.convert hChosen.type_expression (.inr ⟨s, rfl⟩) hρ
    (typing_unique hChosen.forget h.forget)
  rw [sourceGridInterpretation_sort] at he
  have hv := (uniformUniverseEncode_valid (r + 1) s (sourceGridInterpretation r Γ ρ t)).mono
    (hd := Nat.le_refl (r + 2)) F.depth
  have hc := he.coherent_backward d F.depth (Nat.le_refl _) _ hv
  rw [sourceGridEval_encode_normalize r Γ ρ t ht, typeSort_eq h]
  exact FiniteGridType.normalizeValue_recover_prefix _ d F.depth _ hc

/-- Universe elimination at an arbitrary stage, including its candidate
boundary. The only source premise is the preceding carrier conversion. -/
theorem sourceGridInterpretation_decode_prefix (F : SourceCarrierConversion r d P)
    (h : BoundedTyping (r + 2) Γ A (.srt s)) (hs : sortRank s ≤ r + 1) (hρ : P Γ ρ) :
    SourceTypeEqPrefix d (sourceGridInterpretation r Γ ρ A)
      (uniformUniverseDecode (r + 1) (some s) (sourceGridEval r Γ ρ A)) := by
  by_cases henc : SourceGridEncodedTerm A
  · have hEq := uniformUniverseDecode_encode (r + 1) s hs (sourceGridInterpretation r Γ ρ A)
      (sourceGridInterpretation_formed h ρ)
    have hVal := sourceGridEval_encode_prefix F h henc hρ
    exact (SourceTypeEqPrefix.of_full hEq).trans
      (sourceTypeEqPrefix_decode (r + 1) d (some s) _ _ (fun i hi => (hVal i hi).symm))
  · have hdec : SourceGridDecodedTerm A := by
      cases A with
      | var x => exact Or.inl ⟨x, rfl⟩
      | app f a => exact Or.inr ⟨f, a, rfl⟩
      | srt q => exact (henc (Or.inl ⟨q, rfl⟩)).elim
      | pi D B => exact (henc (Or.inr ⟨D, B, rfl⟩)).elim
      | lam D b =>
        obtain ⟨_, _, _, _, _, hc⟩ := h.generation
        exact (not_conv_pi_srt hc).elim
    apply SourceTypeEqPrefix.of_eq
    rw [sourceGridInterpretation_decode r Γ ρ A hdec, typeSort_eq h]

theorem sourceTypeEqPrefix_of_eval (F : SourceCarrierConversion r d P)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hB : BoundedTyping (r + 2) Γ B (.srt s))
    (hs : sortRank s ≤ r + 1) (hρ : P Γ ρ)
    (he : FiniteGridValue.Agree d (sourceGridEval r Γ ρ A) (sourceGridEval r Γ ρ B)) :
    SourceTypeEqPrefix d (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) :=
  ((sourceGridInterpretation_decode_prefix F hA hs hρ).trans
    (sourceTypeEqPrefix_decode (r + 1) d (some s) _ _ he)).trans
      (sourceGridInterpretation_decode_prefix F hB hs hρ).symm

/-- The first conversion theorem supplies the two-carrier input for the
next stage at every finite source bound. -/
theorem sourceCarrierConversionFirst (r : Nat) :
    SourceCarrierConversion r 2 (SourceGridContextFirst r) where
  depth := by omega
  convert := fun hA hB hρ hc => (sourceGrid_type_conv_first hA hB hρ hc).code

theorem sourceGridEval_coherent_second (h : BoundedTyping (r + 2) Γ t A)
    (hρ : SourceGridContextFirst r Γ ρ) :
    (sourceGridInterpretation r Γ ρ A).carrier.Coherent 2 (by omega)
      (FiniteGridValue.toTower _ (sourceGridEval r Γ ρ t)) :=
  sourceGridEval_coherent_of_conversion (sourceCarrierConversionFirst r) h hρ

theorem sourceGridEval_encode_second (h : BoundedTyping (r + 2) Γ t (.srt s))
    (ht : SourceGridEncodedTerm t) (hρ : SourceGridContextFirst r Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ t)
      (uniformUniverseEncode (r + 1) (some s) (sourceGridInterpretation r Γ ρ t)) :=
  sourceGridEval_encode_prefix (sourceCarrierConversionFirst r) h ht hρ

theorem sourceGridInterpretation_decode_second (h : BoundedTyping (r + 2) Γ A (.srt s))
    (hs : sortRank s ≤ r + 1) (hρ : SourceGridContextFirst r Γ ρ) :
    SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ A)
      (uniformUniverseDecode (r + 1) (some s) (sourceGridEval r Γ ρ A)) :=
  sourceGridInterpretation_decode_prefix (sourceCarrierConversionFirst r) h hs hρ

end Submission.Helpers
