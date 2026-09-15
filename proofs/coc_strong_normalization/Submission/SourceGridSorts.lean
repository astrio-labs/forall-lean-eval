import Submission.SourceGridProductCarriers

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem universeSortAt_zero (r : Nat) (v : TowerFamily (carrierGrid (r + 1))) :
    universeSortAt r 0 0 (by omega) v = (.prop : Arity) := by
  cases r <;> rfl

theorem uniformSortCode_zero (r : Nat) (s : Srt) (v : TowerFamily (carrierGrid (r + 1))) :
    uniformSortCode (r + 1) 0 (by omega) s v = arityAt (.type r) (.srt s) := by
  cases s with
  | prop =>
    unfold uniformSortCode
    dsimp only
    rw [dif_neg (show ¬0 = r + 1 by omega)]
    rfl
  | type i =>
    by_cases he : i = r
    · subst i
      rw [uniformSortCode_at r 0 0 (by omega), universeSortAt_zero]
      simp only [arityAt, ↓reduceIte]
      rfl
    · have hs : Srt.type i ≠ .type r := fun h => he (Srt.type.inj h)
      simp only [arityAt, if_neg hs]
      unfold uniformSortCode
      dsimp only
      by_cases hi : i + 1 ≤ r + 1
      · rw [dif_pos hi, dif_neg (show ¬r + 1 - (i + 1) ≤ 0 by omega)]
        rfl
      · rw [dif_neg hi]
        rfl

theorem sourceGridInterpretation_sort_carrier (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (s : Srt) (i : Nat) (hi : i ≤ r + 1) (v : TowerFamily (carrierGrid (r + 1))) :
    (sourceGridInterpretation r Γ ρ (.srt s)).carrier.code i hi v = uniformSortCode (r + 1) i hi s v := by
  cases i with
  | zero => exact (sourceGridInterpretation_zero r Γ ρ (.srt s) v).trans (uniformSortCode_zero r s v).symm
  | succ i =>
    have he := sourceGridStages_interp_before r (r + 2) (Nat.le_refl _) (i + 1) (by omega)
      (.srt s) Γ ρ (i + 1) hi (Nat.le_refl _) v
    refine he.trans ?_
    change (sourceGridUpgrade (r + 1) i
      ((sourceGridStages r i (by omega) (.srt s)).interp Γ (GridEnvironment.truncate (i + 1) ρ))
      (FiniteGridType.sort (r + 1) s)).carrier.code (i + 1) hi v = _
    change (if i + 1 = i + 1 then _ else _) = _
    rw [if_pos rfl]
    rfl

theorem sourceGridInterpretation_sort (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (s : Srt) :
    sourceGridInterpretation r Γ ρ (.srt s) = FiniteGridType.sort (r + 1) s := by
  apply FiniteGridType.ext_fields
  · exact sourceGridInterpretation_sort_carrier r Γ ρ s
  · exact sourceGridInterpretation_sort_candidate r Γ ρ s

theorem sourceGridEval_arity (h : BoundedTyping (r + 2) Γ t A) (ρ : GridEnvironment (r + 1)) :
    (sourceGridEval r Γ ρ t ⟨0, by omega⟩).code = arityAt (.type r) A := by
  have hc := sourceGridEval_inferred r Γ ρ t
  have hh := hc 0 (by omega)
  rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hh
  exact hh.trans (inferredArityAt_eq h rfl)

end Submission.Helpers
