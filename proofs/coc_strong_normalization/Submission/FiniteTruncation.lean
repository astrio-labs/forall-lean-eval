import Submission.UniverseValueConversion

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def FiniteGridValue.Agree (d : Nat) (v w : FiniteGridValue R) : Prop :=
  ∀ i : Fin (R + 1), i.val < d → v i = w i

def FiniteGridValue.truncate (d : Nat) (v : FiniteGridValue R) : FiniteGridValue R :=
  fun i => if i.val < d then v i else TowerFamily.point (carrierGrid R) i.val

variable {R d e : Nat} {v w : FiniteGridValue R}

theorem FiniteGridValue.truncate_congr (h : Agree d v w) : truncate d v = truncate d w := by
  funext i
  unfold truncate
  split
  · exact h i ‹_›
  · rfl

theorem FiniteGridValue.truncate_below (v : FiniteGridValue R) (d : Nat) :
    Agree d (truncate d v) v := by
  intro i hi
  exact if_pos hi

theorem FiniteGridValue.truncate_full (v : FiniteGridValue R) (d : Nat) (hd : R + 1 ≤ d) :
    truncate d v = v := by
  funext i
  exact if_pos (by omega)

theorem FiniteGridValue.truncate_nested (v : FiniteGridValue R) (d e : Nat) (hd : d ≤ e) :
    truncate d (truncate e v) = truncate d v := by
  apply truncate_congr
  intro i hi
  exact if_pos (by omega)

theorem FiniteGridValue.Agree.mono (h : Agree d v w) (he : e ≤ d) : Agree e v w :=
  fun i hi => h i (by omega)

theorem FiniteGridValue.Agree.toTower (h : Agree d v w) :
    TowerFamily.AgreeBelow d (toTower R v) (toTower R w) := by
  intro i hi
  by_cases hb : i < R + 1
  · rw [toTower_at R v ⟨i, hb⟩, toTower_at R w ⟨i, hb⟩]
    exact h ⟨i, hb⟩ hi
  · unfold Submission.Helpers.FiniteGridValue.toTower
    rw [dif_neg hb, dif_neg hb]

theorem FiniteGridValue.agree_ofTower (v w : TowerFamily (carrierGrid R))
    (h : TowerFamily.AgreeBelow d v w) : Agree d (ofTower R v) (ofTower R w) :=
  fun i hi => h i.val hi

abbrev GridEnvironment (R : Nat) := Nat → FiniteGridValue R

def GridEnvironment.Agree (d : Nat) (ρ δ : GridEnvironment R) : Prop :=
  ∀ x, FiniteGridValue.Agree d (ρ x) (δ x)

def GridEnvironment.truncate (d : Nat) (ρ : GridEnvironment R) : GridEnvironment R :=
  fun x => FiniteGridValue.truncate d (ρ x)

variable {ρ δ : GridEnvironment R} {x y : FiniteGridValue R}

theorem GridEnvironment.truncate_congr (h : Agree d ρ δ) : truncate d ρ = truncate d δ :=
  funext (fun x => FiniteGridValue.truncate_congr (h x))

theorem GridEnvironment.truncate_below (ρ : GridEnvironment R) (d : Nat) :
    Agree d (truncate d ρ) ρ := fun x => FiniteGridValue.truncate_below (ρ x) d

theorem GridEnvironment.truncate_nested (ρ : GridEnvironment R) (d e : Nat) (hd : d ≤ e) :
    truncate d (truncate e ρ) = truncate d ρ :=
  funext (fun x => FiniteGridValue.truncate_nested (ρ x) d e hd)

theorem GridEnvironment.Agree.mono (h : Agree d ρ δ) (he : e ≤ d) : Agree e ρ δ :=
  fun x => (h x).mono he

theorem GridEnvironment.Agree.push (h : Agree d ρ δ) (hx : FiniteGridValue.Agree d x y) :
    Agree d (push x ρ) (push y δ) := by
  intro i
  cases i with
  | zero => exact hx
  | succ i => exact h i

theorem GridEnvironment.truncate_push (ρ : GridEnvironment R) (x : FiniteGridValue R) (d : Nat) :
    truncate d (push x ρ) = push (FiniteGridValue.truncate d x) (truncate d ρ) := by
  funext i
  cases i <;> rfl

noncomputable def FiniteGridValue.set (v : FiniteGridValue R) (j : Nat) (x : TowerValue (carrierGrid R j)) :
    FiniteGridValue R := ofTower R ((toTower R v).set j x)

theorem FiniteGridValue.set_same (v : FiniteGridValue R) (j : Nat) (hj : j < R + 1)
    (x : TowerValue (carrierGrid R j)) : v.set j x ⟨j, hj⟩ = x := TowerFamily.set_same _ j x

theorem FiniteGridValue.set_other (v : FiniteGridValue R) (j : Nat)
    (i : Fin (R + 1)) (hij : i.val ≠ j) (x : TowerValue (carrierGrid R j)) : v.set j x i = v i :=
  (TowerFamily.set_other _ j i.val x hij).trans (toTower_at R v i)

theorem FiniteGridValue.set_below (v : FiniteGridValue R) (j : Nat)
    (x : TowerValue (carrierGrid R j)) : Agree j (v.set j x) v :=
  fun i hi => set_other v j i (by omega) x

end Submission.Helpers
