import Submission.GridPiCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- A term value at coordinate `j` may read the argument at that coordinate
and all earlier coordinates, but no later ones. -/
structure CausalGridMap (R : Nat) where
  eval : TowerFamily (carrierGrid R) → TowerFamily (carrierGrid R)
  causal : ∀ j, j ≤ R → ∀ a b, TowerFamily.AgreeBelow (j + 1) a b → eval a j = eval b j

noncomputable def gridLambdaAt (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) (j : Nat) (hj : j ≤ r + 1)
    (f : TowerFamily (carrierGrid (r + 1))) : TowerValue (carrierGrid (r + 1) j) :=
  let D := gridPiDomain A j hj
  let E := gridPiCodomain A B j hj (gridApplicationPrefix r A B j (by omega)).eval f
  let O := gridBindingObject r A j hj D E
  ⟨O.code, O.values.encode (fun x y =>
    (F.eval (((A.arguments j (by omega)).encode x).set j ⟨D x, y⟩) j).cast (E x))⟩

noncomputable def gridLambdaPrefix (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) : (d : Nat) → d ≤ r + 2 → TowerFamily (carrierGrid (r + 1))
  | 0, _ => TowerFamily.point (carrierGrid (r + 1))
  | d + 1, hd =>
    let f := gridLambdaPrefix r A B F d (by omega)
    f.set d (gridLambdaAt r A B F d (by omega) f)

noncomputable def gridLambda (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) : TowerFamily (carrierGrid (r + 1)) :=
  gridLambdaPrefix r A B F (r + 2) (Nat.le_refl _)

theorem gridLambdaPrefix_agree (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) (e : Nat) (he : e ≤ r + 2) (d : Nat) (hd : d ≤ e) :
    TowerFamily.AgreeBelow d (gridLambdaPrefix r A B F e he) (gridLambdaPrefix r A B F d (by omega)) := by
  induction e with
  | zero => intro i hi; omega
  | succ e ih =>
    by_cases hde : d = e + 1
    · subst d; exact .refl _ _
    · intro i hi
      change (gridLambdaPrefix r A B F e (by omega)).set e _ i = _
      rw [TowerFamily.set_other _ e i _ (by omega)]
      exact ih (by omega) (by omega) i hi

theorem gridLambda_at (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) (j : Nat) (hj : j ≤ r + 1) :
    gridLambda r A B F j = gridLambdaAt r A B F j hj (gridLambdaPrefix r A B F j (by omega)) := by
  have h := gridLambdaPrefix_agree r A B F (r + 2) (Nat.le_refl _) (j + 1) (by omega) j
    (Nat.lt_succ_self j)
  exact h.trans (TowerFamily.set_same _ j _)

theorem gridLambda_coherent (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) :
    (gridPiType r A B).Coherent (r + 2) (Nat.le_refl _) (gridLambda r A B F) := by
  intro j hj
  rw [gridLambda_at r A B F j (by omega)]
  exact ((gridPiType r A B).causal j (by omega) _ _
    (gridLambdaPrefix_agree r A B F (r + 2) (Nat.le_refl _) j (by omega))).symm

/-- Supplying a coherent argument to a telescope and its current binder
recovers all coordinates that the current body value can observe. -/
theorem grid_argument_recover (A : CausalGridType R) (j : Nat) (hj : j ≤ R)
    (a : TowerFamily (carrierGrid R)) (ha : A.Coherent (j + 1) (by omega) a) :
    TowerFamily.AgreeBelow (j + 1)
      (((A.arguments j (by omega)).encode ((A.arguments j (by omega)).decode a)).set j
        ⟨gridPiDomain A j hj ((A.arguments j (by omega)).decode a),
          (a j).cast (gridPiDomain A j hj ((A.arguments j (by omega)).decode a))⟩) a := by
  have hp := A.recover j (by omega) a (ha.mono (Nat.le_succ j))
  have hc := A.causal j hj _ a hp
  intro i hi
  by_cases hij : i = j
  · subst i
    rw [TowerFamily.set_same]
    unfold gridPiDomain
    rw [hc]
    exact (a j).mk_cast (ha j (Nat.lt_succ_self _))
  · rw [TowerFamily.set_other _ j i _ hij]
    exact hp i (by omega)

/-- A coordinate-level beta law with an explicit body carrier equation.
The global beta proof derives this equation from earlier coordinates. -/
theorem gridPiApplyAt_lambda (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) (j : Nat) (hj : j ≤ r + 1)
    (v f a : TowerFamily (carrierGrid (r + 1)))
    (hv : v j = gridLambdaAt r A B F j hj f) (hprev : TowerFamily.AgreeBelow j v f)
    (ha : A.Coherent (j + 1) (by omega) a)
    (hbody : (F.eval a j).code =
      gridPiCodomain A B j hj (gridApplicationPrefix r A B j (by omega)).eval f
        ((A.arguments j (by omega)).decode a)) :
    gridPiApplyAt r A B j hj (gridApplicationPrefix r A B j (by omega)).eval v a = F.eval a j := by
  let O := gridApplicationPrefix r A B j (by omega)
  have he : O.eval v = O.eval f := funext (fun x => O.congr v f x x hprev (.refl x j))
  have hE : gridPiCodomain A B j hj O.eval v = gridPiCodomain A B j hj O.eval f := by
    unfold gridPiCodomain
    rw [he]
  unfold gridPiApplyAt
  rw [hE, hv]
  unfold gridLambdaAt
  dsimp only
  rw [TowerValue.cast_mk]
  rw [(gridBindingObject r A j hj (gridPiDomain A j hj) (gridPiCodomain A B j hj O.eval f)).roundtrip]
  rw [F.causal j hj _ a (grid_argument_recover A j hj a ha)]
  exact (F.eval a j).mk_cast hbody

end Submission.Helpers
