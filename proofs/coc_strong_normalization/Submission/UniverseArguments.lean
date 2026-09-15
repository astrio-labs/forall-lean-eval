import Submission.GridCompletion

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def universeArgumentLift (r k : Nat)
    (v : TowerFamily (universeArgumentSystems r k)) : TowerFamily (carrierGrid (r + 1 + k)) :=
  fun j => if hj : k + 1 ≤ j then gridValueCast rfl (by omega) (v (j - (k + 1)))
    else TowerFamily.point (carrierGrid (r + 1 + k)) j

def universeArgumentSlice (r k : Nat) (v : TowerFamily (carrierGrid (r + 1 + k))) :
    TowerFamily (universeArgumentSystems r k) := fun i => v (i + 1 + k)

theorem universeArgumentValue_cast (he : i' = i) (hj : i' + 1 + k = i + 1 + k)
    (v : TowerFamily (universeArgumentSystems r k)) : gridValueCast rfl hj (v i') = v i := by
  cases he
  rfl

theorem universeArgumentLift_at (r k i : Nat) (v : TowerFamily (universeArgumentSystems r k)) :
    universeArgumentLift r k v (i + 1 + k) = v i := by
  unfold universeArgumentLift
  rw [dif_pos (show k + 1 ≤ i + 1 + k by omega)]
  exact universeArgumentValue_cast (by omega) _ v

theorem universeArgumentLift_low (r k i : Nat) (hi : i ≤ k)
    (v : TowerFamily (universeArgumentSystems r k)) :
    universeArgumentLift r k v i = TowerFamily.point (carrierGrid (r + 1 + k)) i := by
  unfold universeArgumentLift
  rw [dif_neg (show ¬k + 1 ≤ i by omega)]

theorem universeArgumentLift_congr (r k d : Nat) (v w : TowerFamily (universeArgumentSystems r k))
    (h : TowerFamily.AgreeBelow d v w) :
    TowerFamily.AgreeBelow (d + 1 + k) (universeArgumentLift r k v) (universeArgumentLift r k w) := by
  intro i hi
  by_cases hik : i ≤ k
  · rw [universeArgumentLift_low r k i hik, universeArgumentLift_low r k i hik]
  · obtain ⟨j, he⟩ : ∃ j, i = j + 1 + k := ⟨i - (k + 1), by omega⟩
    subst i
    rw [universeArgumentLift_at, universeArgumentLift_at]
    exact h j (by omega)

theorem gridValue_eq_point (R j : Nat) (v : TowerValue (carrierGrid R j))
    (h : v.code = (carrierGrid R j).defaultCode) : v = TowerFamily.point (carrierGrid R) j := by
  cases v with
  | mk A x =>
    cases h
    exact congrArg (TowerValue.mk _) ((carrierGridArrows R j).terminal.subsingleton.elim x _)

/-- Recovering the active arguments and the terminal leading coordinates
recovers the whole prefix used by the next source carrier. -/
theorem UniversePrefix.lift_arguments_recover (P : UniversePrefix r d) (hP : P.Full) (k : Nat)
    (v : TowerFamily (carrierGrid (r + 1 + k)))
    (hv : P.telescope.Compatible (universeArgumentRepresentation r k) (universeArgumentSlice r k v))
    (hlow : ∀ i, i ≤ k → (v i).code = (carrierGrid (r + 1 + k) i).defaultCode) :
    TowerFamily.AgreeBelow (d + 1 + k)
      (universeArgumentLift r k ((P.arguments k).encode ((P.arguments k).decode (universeArgumentSlice r k v)))) v := by
  intro i hi
  by_cases hik : i ≤ k
  · rw [universeArgumentLift_low r k i hik]
    exact (gridValue_eq_point _ i (v i) (hlow i hik)).symm
  · obtain ⟨j, he⟩ : ∃ j, i = j + 1 + k := ⟨i - (k + 1), by omega⟩
    subst i
    rw [universeArgumentLift_at]
    exact P.arguments_recover hP k _ hv j (by omega)

end Submission.Helpers
