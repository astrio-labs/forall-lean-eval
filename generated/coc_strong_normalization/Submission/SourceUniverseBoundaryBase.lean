import Submission.SourceRenamingBase

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem FiniteGridCodeEqBelow.trans {A B C : FiniteGridType R}
    (h : FiniteGridCodeEqBelow d A B) (h' : FiniteGridCodeEqBelow d B C) : FiniteGridCodeEqBelow d A C :=
  fun j hj hjd v hv => (h j hj hjd v hv).trans
    (h' j hj hjd v (h.coherent_forward j (by omega) (by omega) v hv))

theorem SourceTypeEqPrefix.symm {A B : FiniteGridType R} (h : SourceTypeEqPrefix d A B) :
    SourceTypeEqPrefix d B A := ⟨h.code.symm, fun hd => (h.full hd).symm.candidate⟩

theorem SourceTypeEqPrefix.trans {A B C : FiniteGridType R}
    (h : SourceTypeEqPrefix d A B) (h' : SourceTypeEqPrefix d B C) : SourceTypeEqPrefix d A C :=
  ⟨h.code.trans h'.code, fun hd => ((h.full hd).trans (h'.full hd)).candidate⟩

theorem FiniteGridValue.agree_one {v w : FiniteGridValue R}
    (h : v ⟨0, Nat.zero_lt_succ _⟩ = w ⟨0, Nat.zero_lt_succ _⟩) : Agree 1 v w := by
  intro i hi
  have he : i = ⟨0, Nat.zero_lt_succ _⟩ := by
    apply Fin.ext
    change i.val = 0
    omega
  subst i
  exact h

theorem uniformUniverseEncode_valid (R : Nat) (s : Srt) (A : FiniteGridType R) :
    (FiniteGridType.sort R s).Valid (uniformUniverseEncode R (some s) A) := by
  cases s with
  | prop => exact A.reifyProp_valid
  | type i =>
    by_cases hi : i + 1 ≤ R
    · obtain ⟨k, he⟩ : ∃ k, R = i + 1 + k := ⟨R - (i + 1), by omega⟩
      subst R
      rw [uniformUniverseEncode_at]
      exact A.reify_valid i k
    · unfold uniformUniverseEncode
      dsimp only
      rw [dif_neg hi]
      intro j hj
      rw [FiniteGridValue.toTower_at R _ ⟨j, hj⟩]
      change (TowerFamily.point (carrierGrid R) j).code = uniformSortCode R j (by omega) (.type i) _
      unfold uniformSortCode
      dsimp only
      rw [dif_neg hi]
      rfl

theorem uniformUniverseDecode_encode (R : Nat) (s : Srt) (hs : sortRank s ≤ R)
    (A : FiniteGridType R) (hA : A.Formed s) :
    FiniteGridTypeEq A (uniformUniverseDecode R (some s) (uniformUniverseEncode R (some s) A)) := by
  cases s with
  | prop => exact decodePropType_reify A hA
  | type i =>
    obtain ⟨k, he⟩ : ∃ k, R = i + 1 + k := ⟨R - (i + 1), by simp only [sortRank] at hs; omega⟩
    subst R
    rw [uniformUniverseEncode_at, uniformUniverseDecode_at]
    exact decodeUniverseType_reify i k A hA

/-- At the first value coordinate the inferred cast on a sort or Pi
introduction is inert. This uses its actual source typing derivation. -/
theorem sourceGridEval_encode_zero (h : BoundedTyping (r + 2) Γ t (.srt s))
    (ht : SourceGridEncodedTerm t) (ρ : GridEnvironment (r + 1)) :
    sourceGridEval r Γ ρ t ⟨0, by omega⟩ =
      uniformUniverseEncode (r + 1) (some s) (sourceGridInterpretation r Γ ρ t) ⟨0, by omega⟩ := by
  rw [sourceGridEval_encode_coordinate r Γ ρ t ht, typeSort_eq h]
  unfold FiniteGridType.forceCoordinate
  rw [sourceGridInterpretation_zero]
  have hc : arityAt (.type r) (chosenType (r + 2) Γ t) = arityAt (.type r) (.srt s) :=
    inferredArityAt_eq h rfl
  rw [hc]
  apply TowerValue.mk_cast
  have hv := uniformUniverseEncode_valid (r + 1) s (sourceGridInterpretation r Γ ρ t)
  have hv0 := hv 0 (Nat.zero_lt_succ _)
  rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩] at hv0
  exact hv0.trans (uniformSortCode_zero r s _)

/-- Proper source types satisfy the universe elimination equation through
the first two carrier coordinates. This includes sort and Pi arguments. -/
theorem sourceGridInterpretation_decode_first (h : BoundedTyping (r + 2) Γ A (.srt s))
    (hs : sortRank s ≤ r + 1) (ρ : GridEnvironment (r + 1)) :
    SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ A)
      (uniformUniverseDecode (r + 1) (some s) (sourceGridEval r Γ ρ A)) := by
  by_cases henc : SourceGridEncodedTerm A
  · have hEq := uniformUniverseDecode_encode (r + 1) s hs (sourceGridInterpretation r Γ ρ A)
      (sourceGridInterpretation_formed h ρ)
    have hVal := FiniteGridValue.agree_one (sourceGridEval_encode_zero h henc ρ)
    constructor
    · intro j hj hjd v hv
      exact (hEq.code j hj v hv).trans
        (uniformUniverseDecode_causal (r + 1) (some s) _ _ j hj
          (fun i hi => (hVal i (by omega)).symm) v)
    · intro hd
      omega
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

end Submission.Helpers
