import Submission.UniverseCoherentSections

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem FiniteGridTypeEq.universePrefix (r k : Nat) {A B : FiniteGridType (r + 1 + k)}
    (h : FiniteGridTypeEq A B) (hA : A.Formed (.type r)) (d : Nat) (hd : d ≤ r + 1) :
    universeTypePrefix r k A.carrier d hd = universeTypePrefix r k B.carrier d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [universeTypePrefix, universeTypePrefix, ← ih (by omega)]
    congr 1
    funext x
    apply congrArg (universeOutputCodes r d k).decode
    exact h.code (d + 1 + k) (by omega) _
      (universeTypePrefix_section_coherent r k A.carrier hA d (by omega) x)

theorem FiniteGridTypeEq.universeReify (r k : Nat) {A B : FiniteGridType (r + 1 + k)}
    (h : FiniteGridTypeEq A B) (hA : A.Formed (.type r)) (d : Nat) :
    universeReify r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) d =
      universeReify r k B.carrier (CausalGridPredicate.ofFinite _ B.candidate) d := by
  by_cases hd : d ≤ r
  · rw [universeReify_proper r k _ _ d hd, universeReify_proper r k _ _ d hd]
    unfold universeTypeField
    rw [← h.universePrefix r k hA d (by omega)]
    congr 1
    funext x
    apply congrArg (universeOutputCodes r d k).decode
    exact h.code (d + 1 + k) (by omega) _
      (universeTypePrefix_section_coherent r k A.carrier hA d (by omega) x)
  · by_cases he : d = r + 1
    · subst d
      rw [universeReify_final, universeReify_final, ← h.universePrefix r k hA (r + 1) (Nat.le_refl _)]
      congr 1
      funext x
      apply h.candidate
      apply A.carrier.valid_ofTower
      exact (universeTypePrefix_section_coherent r k A.carrier hA (r + 1) (Nat.le_refl _) x).mono (by omega)
    · unfold Submission.Helpers.universeReify
      rw [dif_neg hd, dif_neg hd, dif_neg he, dif_neg he]

/-- Reification respects semantic type equality on coherent data. The proof
uses the validity of the encoder's own telescope sections. -/
theorem FiniteGridTypeEq.reify_eq (r k : Nat) {A B : FiniteGridType (r + 1 + k)}
    (h : FiniteGridTypeEq A B) (hA : A.Formed (.type r)) : A.reify r k = B.reify r k := by
  apply congrArg (FiniteGridValue.ofTower _)
  funext j
  unfold universeReifyValues
  split
  · rw [h.universeReify r k hA]
  · rfl

theorem FiniteGridTypeEq.reifyProp_eq {A B : FiniteGridType R}
    (h : FiniteGridTypeEq A B) (hA : A.Formed .prop) : A.reifyProp = B.reifyProp := by
  have hp : A.Valid (FiniteGridValue.ofTower R (TowerFamily.point (carrierGrid R))) := by
    apply A.carrier.valid_ofTower
    intro j hj
    exact ((hA j (by omega) _).lower (by simp only [sortRank]; omega)).symm
  unfold FiniteGridType.reifyProp propReifyValues CausalGridPredicate.ofFinite
  dsimp only
  rw [h.candidate _ hp]

end Submission.Helpers
