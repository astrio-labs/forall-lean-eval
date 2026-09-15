import Submission.LiteralSorts

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- A causal sequence of code fields determines a dependent input prefix. -/
noncomputable def carrierFieldPrefix (r : Nat)
    (C : (d : Nat) → d ≤ r → TowerFamily (carrierGrid r) → (carrierGrid r d).Code) :
    (d : Nat) → d ≤ r + 1 → UniversePrefix r d
  | 0, _ => UniversePrefix.empty r
  | d + 1, hd =>
    let P := carrierFieldPrefix r C d (by omega)
    P.next (fun x => C d (by omega)
      (P.telescope.sectionValues (fun i => CarrierRepresentation.identity (carrierGrid r i)) x))

/-- Reify the carrier fields of any literal sort, including `Prop`. -/
noncomputable def sortLiteralPrefix (s : Srt) (d : Nat) (hd : d ≤ sortRank s + 1) :
    UniversePrefix (sortRank s) d :=
  carrierFieldPrefix (sortRank s) (fun d hd v => uniformSortCode (sortRank s) d hd s v) d hd

noncomputable def sortLiteralField (s : Srt) (d : Nat) (hd : d ≤ sortRank s) :
    (sortLiteralPrefix s d (by omega)).El → (carrierGrid (sortRank s) d).Code :=
  fun x => uniformSortCode (sortRank s) d hd s
    ((sortLiteralPrefix s d (by omega)).telescope.sectionValues
      (fun i => CarrierRepresentation.identity (carrierGrid (sortRank s) i)) x)

noncomputable def sortLiteralValue (s : Srt) (k d : Nat) :
    TowerValue (carrierGrid (sortRank s + 1 + k) (d + k)) := by
  classical
  exact if hd : d ≤ sortRank s then
    (sortLiteralPrefix s d (by omega)).encodeCode hd k (sortLiteralField s d hd)
  else if he : d = sortRank s + 1 then
    gridValueCast rfl (congrArg (fun d => d + k) he.symm)
      ((sortLiteralPrefix s (sortRank s + 1) (Nat.le_refl _)).encodeCandidate k (fun _ => Candidate.sn))
  else (TowerFamily.point (carrierGrid (sortRank s + 1 + k))) (d + k)

theorem sortLiteralValue_proper (s : Srt) (k d : Nat) (hd : d ≤ sortRank s) :
    sortLiteralValue s k d =
      (sortLiteralPrefix s d (by omega)).encodeCode hd k (sortLiteralField s d hd) := by
  unfold sortLiteralValue
  rw [dif_pos hd]

theorem sortLiteralValue_final (s : Srt) (k : Nat) :
    sortLiteralValue s k (sortRank s + 1) =
      (sortLiteralPrefix s (sortRank s + 1) (Nat.le_refl _)).encodeCandidate k (fun _ => Candidate.sn) := by
  unfold sortLiteralValue
  rw [dif_neg (Nat.not_succ_le_self _), dif_pos rfl]
  rfl

theorem sortLiteralValue_prefix (s : Srt) (k d : Nat) (hd : d ≤ sortRank s + 1) :
    UniversePrefix.fromValues (sortRank s) k d hd (sortLiteralValue s k) = sortLiteralPrefix s d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [UniversePrefix.fromValues, ih (by omega), sortLiteralValue_proper s k d (by omega),
      UniversePrefix.decodeCode_encodeCode]
    rfl

theorem sortLiteralValue_code (s : Srt) (k d : Nat) (hd : d ≤ sortRank s + 1) :
    (sortLiteralValue s k d).code = ((sortLiteralPrefix s d hd).shiftObject hd k).code := by
  by_cases hl : d ≤ sortRank s
  · rw [sortLiteralValue_proper s k d hl]
    exact (sortLiteralPrefix s d hd).shiftCodeObject_code hl k
  · have he : d = sortRank s + 1 := by omega
    subst d
    rw [sortLiteralValue_final]
    exact (sortLiteralPrefix s (sortRank s + 1) hd).shiftCandidateObject_code k

noncomputable def sortLiteralValues (s : Srt) (k : Nat) :
    TowerFamily (carrierGrid (sortRank s + 1 + k)) :=
  fun j => if hj : k ≤ j then gridValueCast rfl (Nat.sub_add_cancel hj) (sortLiteralValue s k (j - k))
    else (TowerFamily.point (carrierGrid (sortRank s + 1 + k))) j

theorem sortLiteralValues_at (s : Srt) (k d : Nat) :
    sortLiteralValues s k (d + k) = sortLiteralValue s k d := by
  unfold sortLiteralValues
  rw [dif_pos (show k ≤ d + k by omega)]
  exact gridValueCast_family (by omega) _ (sortLiteralValue s k)

theorem sortLiteralValues_active_code (s : Srt) (k d : Nat) (hd : d ≤ sortRank s + 1) :
    (sortLiteralValues s k (d + k)).code =
      uniformSortCode (sortRank s + 1 + k) (d + k) (by omega) (.type (sortRank s)) (sortLiteralValues s k) := by
  rw [sortLiteralValues_at, uniformSortCode_at (sortRank s) k d hd]
  unfold universeSortAt
  have hv : (fun i => sortLiteralValues s k (i + k)) = sortLiteralValue s k :=
    funext (sortLiteralValues_at s k)
  rw [hv, sortLiteralValue_prefix]
  exact sortLiteralValue_code s k d hd

/-- All literal sorts satisfy the carrier equation of their original sort
axiom, at every coordinate and every larger finite row. -/
theorem sortLiteralValues_typed_code (s : Srt) (k j : Nat) (hj : j ≤ sortRank s + 1 + k)
    (hAx : Ax s s') :
    (sortLiteralValues s k j).code =
      uniformSortCode (sortRank s + 1 + k) j hj s' (sortLiteralValues s k) := by
  have hs : s' = .type (sortRank s) := by cases hAx <;> rfl
  subst s'
  by_cases hk : k ≤ j
  · obtain ⟨d, he⟩ : ∃ d, j = d + k := ⟨j - k, (Nat.sub_add_cancel hk).symm⟩
    subst j
    exact sortLiteralValues_active_code s k d (by omega)
  · rw [uniformSortCode_lower _ _ hj (Ax.type (sortRank s)) _ (by simp only [sortRank]; omega)]
    unfold sortLiteralValues
    rw [dif_neg hk]
    rfl

/-- At the last coordinate the represented reducibility family of every
literal sort is exactly the strong-normalization candidate. -/
theorem sortLiteralValues_candidate (s : Srt) (k : Nat) :
    (sortLiteralPrefix s (sortRank s + 1) (Nat.le_refl _)).decodeCandidate k
      (sortLiteralValues s k (sortRank s + 1 + k)) = fun _ => Candidate.sn := by
  rw [sortLiteralValues_at, sortLiteralValue_final, UniversePrefix.decodeCandidate_encodeCandidate]

/-- Transport the entire literal interpretation to a prescribed finite row. -/
theorem sortLiteralValues_typed_code_cast (s : Srt) (k R j : Nat)
    (hR : sortRank s + 1 + k = R) (hj : j ≤ R) (hAx : Ax s s') :
    ((gridRowValuesCast hR (sortLiteralValues s k)) j).code =
      uniformSortCode R j hj s' (gridRowValuesCast hR (sortLiteralValues s k)) := by
  cases hR
  exact sortLiteralValues_typed_code s k j hj hAx

noncomputable def boundedLiteralValues (R : Nat) (s : Srt) : TowerFamily (carrierGrid R) :=
  if hR : sortRank s + 1 ≤ R then
    gridRowValuesCast (Nat.add_sub_of_le hR) (sortLiteralValues s (R - (sortRank s + 1)))
  else TowerFamily.point (carrierGrid R)

/-- The highest available sort has a terminal value. Proper lower sorts
use the same literal interpretation, with their calculated universe offset. -/
theorem boundedLiteralValues_typed_code (R j : Nat) (hj : j ≤ R) (hAx : Ax s s') :
    (boundedLiteralValues R s j).code =
      uniformSortCode R j hj s' (boundedLiteralValues R s) := by
  classical
  unfold boundedLiteralValues
  by_cases hR : sortRank s + 1 ≤ R
  · rw [dif_pos hR]
    exact sortLiteralValues_typed_code_cast s _ R j (Nat.add_sub_of_le hR) hj hAx
  · rw [dif_neg hR]
    have hs : s' = .type (sortRank s) := by cases hAx <;> rfl
    subst s'
    unfold uniformSortCode
    dsimp only
    rw [dif_neg hR]
    rfl

end Submission.Helpers
