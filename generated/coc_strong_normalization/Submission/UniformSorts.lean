import Submission.UniverseValues

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

def gridCodeCast (hr : r = r') (hd : d = d') (A : (carrierGrid r d).Code) :
    (carrierGrid r' d').Code := by cases hr; cases hd; exact A

def gridValueCast (hr : r = r') (hd : d = d') (v : TowerValue (carrierGrid r d)) :
    TowerValue (carrierGrid r' d') := by cases hr; cases hd; exact v

def gridRowValuesCast (hr : r = r') (v : TowerFamily (carrierGrid r)) : TowerFamily (carrierGrid r') :=
  fun i => gridValueCast hr rfl (v i)

theorem GridFormation.cast (hr : r = r') (hd : d = d') (h : GridFormation r d s A) :
    GridFormation r' d' s (gridCodeCast hr hd A) := by cases hr; cases hd; exact h

theorem carrierGridCandidateCode_image (r : Nat) :
    GridCodeImage r r r (carrierGridCandidateCode r) := by
  induction r with
  | zero => exact .base _
  | succ r ih => exact .small ih

theorem carrierGridCandidateCode_formation (r : Nat) :
    GridFormation r r (.type 0) (carrierGridCandidateCode r) := by
  refine ⟨fun h => by simp only [sortRank] at h; omega, ?_⟩
  have he : min r (r + 1 - sortRank (.type 0)) = r := by simp only [sortRank]; omega
  rw [he]
  exact carrierGridCandidateCode_image r

/-- The active portion of a predicative source sort. It reads only already
available universe coordinates and covers its candidate-valued boundary. -/
noncomputable def universeSortAt (r k d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1 + k))) : (carrierGrid (r + 1 + k) (d + k)).Code :=
  ((UniversePrefix.fromValues r k d hd (fun i => v (i + k))).shiftObject hd k).code

theorem universeSortAt_formation (r k d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1 + k))) :
    GridFormation (r + 1 + k) (d + k) (.type (r + 1)) (universeSortAt r k d hd v) :=
  (UniversePrefix.fromValues r k d hd _).shiftObject_formation hd k

theorem universeSortAt_congr (r k d : Nat) (hd : d ≤ r + 1)
    (v w : TowerFamily (carrierGrid (r + 1 + k))) (h : ∀ i, i < d + k → v i = w i) :
    universeSortAt r k d hd v = universeSortAt r k d hd w := by
  unfold universeSortAt
  rw [UniversePrefix.fromValues_congr r k d hd _ _ (fun i hi => h (i + k) (by omega))]

/-- The universe carrier at any source row and coordinate. Lower coordinates
are terminal; active ones use the same indexed universe representation.
`Prop` reaches candidates on the small diagonal. -/
noncomputable def uniformSortCode (R j : Nat) (hj : j ≤ R) (s : Srt)
    (v : TowerFamily (carrierGrid R)) : (carrierGrid R j).Code := by
  classical
  cases s with
  | prop => exact if he : j = R then gridCodeCast rfl he.symm (carrierGridCandidateCode R)
      else (carrierGrid R j).defaultCode
  | type i =>
    exact if hi : i + 1 ≤ R then
      if hk : R - (i + 1) ≤ j then
        let k := R - (i + 1)
        let d := j - k
        let hR : i + 1 + k = R := Nat.add_sub_of_le hi
        let hd : d + k = j := Nat.sub_add_cancel hk
        gridCodeCast hR hd (universeSortAt i k d (by omega) (gridRowValuesCast hR.symm v))
      else (carrierGrid R j).defaultCode
    else (carrierGrid R j).defaultCode

/-- The original trusted sort axiom is respected at every coordinate and
finite source row. No finite-bound normalization premise occurs. -/
theorem uniformSortCode_formation (R j : Nat) (hj : j ≤ R) (hAx : Ax s s')
    (v : TowerFamily (carrierGrid R)) : GridFormation R j s' (uniformSortCode R j hj s v) := by
  classical
  cases hAx with
  | prop =>
    unfold uniformSortCode
    dsimp only
    by_cases he : j = R
    · rw [dif_pos he]
      exact (carrierGridCandidateCode_formation R).cast rfl he.symm
    · rw [dif_neg he]
      exact gridFormation_default hj _
  | type i =>
    unfold uniformSortCode
    dsimp only
    by_cases hi : i + 1 ≤ R
    · rw [dif_pos hi]
      by_cases hk : R - (i + 1) ≤ j
      · rw [dif_pos hk]
        exact (universeSortAt_formation i (R - (i + 1)) (j - (R - (i + 1))) (by omega) _).cast
          (Nat.add_sub_of_le hi) (Nat.sub_add_cancel hk)
      · rw [dif_neg hk]
        exact gridFormation_default hj _
    · rw [dif_neg hi]
      exact gridFormation_default hj _

theorem uniformSortCode_lower (R j : Nat) (hj : j ≤ R) (hAx : Ax s s')
    (v : TowerFamily (carrierGrid R)) (hs : sortRank s + j < R) :
    uniformSortCode R j hj s v = (carrierGrid R j).defaultCode := by
  have he : sortRank s' = sortRank s + 1 := by cases hAx <;> rfl
  exact (uniformSortCode_formation R j hj hAx v).lower (by omega)

/-- The sort code at coordinate `j` depends strictly on earlier values.
This is the noncircularity property needed by a source stage construction. -/
theorem uniformSortCode_congr (R j : Nat) (hj : j ≤ R) (s : Srt)
    (v w : TowerFamily (carrierGrid R)) (h : ∀ i, i < j → v i = w i) :
    uniformSortCode R j hj s v = uniformSortCode R j hj s w := by
  classical
  cases s with
  | prop => rfl
  | type i =>
    unfold uniformSortCode
    dsimp only
    by_cases hi : i + 1 ≤ R
    · rw [dif_pos hi, dif_pos hi]
      by_cases hk : R - (i + 1) ≤ j
      · rw [dif_pos hk, dif_pos hk]
        apply congrArg (gridCodeCast (Nat.add_sub_of_le hi) (Nat.sub_add_cancel hk))
        apply universeSortAt_congr
        intro m hm
        exact congrArg (gridValueCast (Nat.add_sub_of_le hi).symm rfl) (h m (by omega))
      · rw [dif_neg hk, dif_neg hk]
    · rw [dif_neg hi, dif_neg hi]

theorem universeSortAt_cast (hk : k' = k) (he : d' = d)
    (hR : r + 1 + k' = r + 1 + k) (hj : d' + k' = d + k)
    (hd' : d' ≤ r + 1) (hd : d ≤ r + 1) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    gridCodeCast hR hj (universeSortAt r k' d' hd' (gridRowValuesCast hR.symm v)) =
      universeSortAt r k d hd v := by
  cases hk
  cases he
  rfl

theorem uniformSortCode_at (r k d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1 + k))) :
    uniformSortCode (r + 1 + k) (d + k) (by omega) (.type r) v = universeSortAt r k d hd v := by
  classical
  unfold uniformSortCode
  dsimp only
  rw [dif_pos (show r + 1 ≤ r + 1 + k by omega)]
  have he : r + 1 + k - (r + 1) = k := by omega
  simp only [he]
  rw [dif_pos (show k ≤ d + k by omega)]
  exact universeSortAt_cast he (by omega) _ _ _ hd v

end Submission.Helpers
