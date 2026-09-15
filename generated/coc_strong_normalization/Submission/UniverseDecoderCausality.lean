import Submission.CanonicalPiCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem finiteUniversePrefix_congr (r k d : Nat) (hd : d ≤ r + 1)
    (u w : FiniteGridValue (r + 1 + k))
    (h : TowerFamily.AgreeBelow (d + k) (FiniteGridValue.toTower _ u) (FiniteGridValue.toTower _ w)) :
    finiteUniversePrefix r k d hd u = finiteUniversePrefix r k d hd w :=
  UniversePrefix.fromValues_congr r k d hd _ _ (fun i hi => h (i + k) (by omega))

theorem rawFiniteUniverseCode_stored_congr (r k d : Nat) (hd : d ≤ r)
    (u w : FiniteGridValue (r + 1 + k))
    (h : TowerFamily.AgreeBelow (d + 1 + k) (FiniteGridValue.toTower _ u) (FiniteGridValue.toTower _ w))
    (v : TowerFamily (carrierGrid (r + 1 + k))) :
    rawFiniteUniverseCode r k d hd u v = rawFiniteUniverseCode r k d hd w v := by
  unfold rawFiniteUniverseCode
  rw [finiteUniversePrefix_congr r k d (by omega) u w (h.mono (by omega)), h (d + k) (by omega)]

/-- The carrier decoded at coordinate `j` reads strictly earlier stored
universe-value coordinates. This is the dependency required for a family. -/
theorem decodedUniverseCarrier_stored_congr (r k : Nat) (u w : FiniteGridValue (r + 1 + k))
    (j : Nat) (hj : j ≤ r + 1 + k)
    (h : TowerFamily.AgreeBelow j (FiniteGridValue.toTower _ u) (FiniteGridValue.toTower _ w))
    (v : TowerFamily (carrierGrid (r + 1 + k))) :
    decodedUniverseCarrier r k u j hj v = decodedUniverseCarrier r k w j hj v := by
  by_cases hl : j ≤ k
  · rw [decodedUniverseCarrier_low r k u j hj hl, decodedUniverseCarrier_low r k w j hj hl]
  · obtain ⟨d, he⟩ : ∃ d, j = d + 1 + k := ⟨j - (k + 1), by omega⟩
    subst j
    rw [decodedUniverseCarrier_at r k u d (by omega), decodedUniverseCarrier_at r k w d (by omega)]
    exact rawFiniteUniverseCode_stored_congr r k d (by omega) u w h v

noncomputable def decodeUniverseFamily (r k : Nat) : FiniteGridFamily (r + 1 + k) where
  fiber := decodeUniverseType r k
  causal j hj u w h v := decodedUniverseCarrier_stored_congr r k u w j hj h v

noncomputable def decodePropFamily (R : Nat) : FiniteGridFamily R where
  fiber := decodePropType R
  causal _ _ _ _ _ _ := rfl

theorem FiniteGridValue.eq_of_agree (R : Nat) (u w : FiniteGridValue R)
    (h : TowerFamily.AgreeBelow (R + 1) (toTower R u) (toTower R w)) : u = w :=
  (ofTower_toTower R u).symm.trans ((ofTower_congr R _ _ h).trans (ofTower_toTower R w))

end Submission.Helpers
