import Submission.FiniteGridConversion

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def rawFiniteUniverseCode (r k d : Nat) (hd : d ≤ r)
    (u : FiniteGridValue (r + 1 + k)) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    (carrierGrid (r + 1 + k) (d + 1 + k)).Code :=
  (finiteUniversePrefix r k d (by omega) u).readCodeFamily hd k
    (FiniteGridValue.toTower _ u (d + k)) (universeArgumentSlice r k v)

theorem rawFiniteUniverseCode_congr (r k d : Nat) (hd : d ≤ r)
    (u : FiniteGridValue (r + 1 + k)) (v w : TowerFamily (carrierGrid (r + 1 + k)))
    (h : TowerFamily.AgreeBelow (d + 1 + k) v w) :
    rawFiniteUniverseCode r k d hd u v = rawFiniteUniverseCode r k d hd u w := by
  let P := finiteUniversePrefix r k d (by omega) u
  have he : (P.arguments k).decode (universeArgumentSlice r k v) =
      (P.arguments k).decode (universeArgumentSlice r k w) :=
    P.telescope.project_congr (universeArgumentRepresentation r k) P.ordered.all _ _
      (fun i hi => h (i + 1 + k) (by omega))
  unfold rawFiniteUniverseCode UniversePrefix.readCodeFamily
  dsimp only [familyDecode]
  rw [he]

theorem rawFiniteUniverseCode_formed (r k d : Nat) (hd : d ≤ r)
    (u : FiniteGridValue (r + 1 + k)) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    GridFormation (r + 1 + k) (d + 1 + k) (.type r) (rawFiniteUniverseCode r k d hd u v) := by
  refine ⟨fun h => by simp only [sortRank] at h; omega, ?_⟩
  have he : min (d + 1 + k) ((r + 1 + k) + 1 - sortRank (.type r)) = k + 1 := by
    simp only [sortRank]
    omega
  rw [he]
  exact universeOutputCodes_image r d k _

noncomputable def decodedUniverseCarrier (r k : Nat) (u : FiniteGridValue (r + 1 + k))
    (j : Nat) (hj : j ≤ r + 1 + k) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    (carrierGrid (r + 1 + k) j).Code :=
  if hl : j ≤ k then (carrierGrid (r + 1 + k) j).defaultCode else
    gridCodeCast rfl (by omega) (rawFiniteUniverseCode r k (j - (k + 1)) (by omega) u v)

theorem decodedUniverseCarrier_low (r k : Nat) (u : FiniteGridValue (r + 1 + k))
    (j : Nat) (hj : j ≤ r + 1 + k) (hl : j ≤ k) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    decodedUniverseCarrier r k u j hj v = (carrierGrid (r + 1 + k) j).defaultCode := by
  unfold decodedUniverseCarrier
  rw [dif_pos hl]

theorem universeCode_cast (he : i' = i) (hj : i' + 1 + k = i + 1 + k)
    (C : (d : Nat) → d ≤ r → (carrierGrid (r + 1 + k) (d + 1 + k)).Code)
    (hi' : i' ≤ r) (hi : i ≤ r) : gridCodeCast rfl hj (C i' hi') = C i hi := by
  cases he
  rfl

theorem decodedUniverseCarrier_at (r k : Nat) (u : FiniteGridValue (r + 1 + k))
    (d : Nat) (hd : d ≤ r) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    decodedUniverseCarrier r k u (d + 1 + k) (by omega) v = rawFiniteUniverseCode r k d hd u v := by
  unfold decodedUniverseCarrier
  rw [dif_neg (show ¬d + 1 + k ≤ k by omega)]
  exact universeCode_cast (by omega) _ (fun i hi => rawFiniteUniverseCode r k i hi u v) _ hd

theorem decodedUniverseCarrier_causal (r k : Nat) (u : FiniteGridValue (r + 1 + k))
    (j : Nat) (hj : j ≤ r + 1 + k) : TowerFamily.DependsBelow j (decodedUniverseCarrier r k u j hj) := by
  intro v w h
  by_cases hl : j ≤ k
  · rw [decodedUniverseCarrier_low r k u j hj hl, decodedUniverseCarrier_low r k u j hj hl]
  · obtain ⟨d, he⟩ : ∃ d, j = d + 1 + k := ⟨j - (k + 1), by omega⟩
    subst j
    rw [decodedUniverseCarrier_at r k u d (by omega), decodedUniverseCarrier_at r k u d (by omega)]
    exact rawFiniteUniverseCode_congr r k d (by omega) u v w h

theorem decodedUniverseCarrier_formed (r k : Nat) (u : FiniteGridValue (r + 1 + k))
    (j : Nat) (hj : j ≤ r + 1 + k) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    GridFormation (r + 1 + k) j (.type r) (decodedUniverseCarrier r k u j hj v) := by
  by_cases hl : j ≤ k
  · rw [decodedUniverseCarrier_low r k u j hj hl]
    exact gridFormation_default hj _
  · obtain ⟨d, he⟩ : ∃ d, j = d + 1 + k := ⟨j - (k + 1), by omega⟩
    subst j
    rw [decodedUniverseCarrier_at r k u d (by omega)]
    exact rawFiniteUniverseCode_formed r k d (by omega) u v

/-- Universe elimination constructs a complete semantic type from a finite
value, including its candidate. The result is formed by construction. -/
noncomputable def decodeUniverseType (r k : Nat) (u : FiniteGridValue (r + 1 + k)) :
    FiniteGridType (r + 1 + k) where
  carrier := ⟨decodedUniverseCarrier r k u, decodedUniverseCarrier_causal r k u⟩
  candidate := finiteUniverseCandidate r k u

theorem decodeUniverseType_formed (r k : Nat) (u : FiniteGridValue (r + 1 + k)) :
    (decodeUniverseType r k u).Formed (.type r) := decodedUniverseCarrier_formed r k u

theorem decodedUniverseCarrier_reify (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (hA : A.Formed (.type r)) (d : Nat) (hd : d ≤ r)
    (v : TowerFamily (carrierGrid (r + 1 + k))) (hv : A.carrier.Coherent (d + 1 + k) (by omega) v) :
    decodedUniverseCarrier r k (A.reify r k) (d + 1 + k) (by omega) v = A.carrier.code (d + 1 + k) (by omega) v := by
  rw [decodedUniverseCarrier_at]
  unfold rawFiniteUniverseCode
  rw [finiteUniversePrefix_reify, A.reify_at r k d (by omega)]
  exact universeReify_decode r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) hA d hd v hv

/-- Reification followed by universe elimination preserves a formed type on
all coherent prefixes and values. There is no source-normalization premise. -/
theorem decodeUniverseType_reify (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (hA : A.Formed (.type r)) : FiniteGridTypeEq A (decodeUniverseType r k (A.reify r k)) := by
  constructor
  · intro j hj v hv
    change A.carrier.code j hj v = decodedUniverseCarrier r k (A.reify r k) j hj v
    by_cases hl : j ≤ k
    · rw [decodedUniverseCarrier_low r k _ j hj hl]
      exact (hA j hj v).lower (by simp only [sortRank]; omega)
    · obtain ⟨d, he⟩ : ∃ d, j = d + 1 + k := ⟨j - (k + 1), by omega⟩
      subst j
      exact (decodedUniverseCarrier_reify r k A hA d (by omega) v hv).symm
  · intro v hv
    exact (finiteUniverseCandidate_reify r k A hA v hv).symm

theorem decodeUniverseType_reify_conversion (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (hA : A.Formed (.type r)) :
    A.canonicalCandidate = (decodeUniverseType r k (A.reify r k)).canonicalCandidate :=
  (decodeUniverseType_reify r k A hA).canonicalCandidate_eq

noncomputable def decodePropType (R : Nat) (u : FiniteGridValue R) : FiniteGridType R where
  carrier := ⟨fun j _ _ => (carrierGrid R j).defaultCode, fun _ _ _ _ _ => rfl⟩
  candidate _ := finitePropCandidate R u

theorem decodePropType_formed (R : Nat) (u : FiniteGridValue R) : (decodePropType R u).Formed .prop :=
  fun _ hj _ => gridFormation_default hj _

theorem decodePropType_reify (A : FiniteGridType R) (hA : A.Formed .prop) :
    FiniteGridTypeEq A (decodePropType R A.reifyProp) := by
  constructor
  · intro j hj v _
    exact (hA j hj v).lower (by simp only [sortRank]; omega)
  · intro v hv
    exact (finitePropCandidate_reify A hA v hv).symm

theorem decodePropType_reify_conversion (A : FiniteGridType R) (hA : A.Formed .prop) :
    A.canonicalCandidate = (decodePropType R A.reifyProp).canonicalCandidate :=
  (decodePropType_reify A hA).canonicalCandidate_eq

end Submission.Helpers
