import Submission.GridLambda

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- The body carrier equation required at each beta step follows from the
previous beta equations. This induction is uniform in the finite row. -/
theorem gridLambda_beta_coordinate (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1))
    (hF : ∀ a, A.Coherent (r + 2) (Nat.le_refl _) a →
      (B.fiber a).Coherent (r + 2) (Nat.le_refl _) (F.eval a))
    (a : TowerFamily (carrierGrid (r + 1))) (ha : A.Coherent (r + 2) (Nat.le_refl _) a)
    (j : Nat) (hj : j ≤ r + 1) :
    gridApplication r A B (gridLambda r A B F) a j = F.eval a j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [gridApplication_at r A B j hj]
    apply gridPiApplyAt_lambda r A B F j hj _ _ a
      (gridLambda_at r A B F j hj)
      (gridLambdaPrefix_agree r A B F (r + 2) (Nat.le_refl _) j (by omega))
      (ha.mono (by omega))
    let O := gridApplicationPrefix r A B j (by omega)
    let f := gridLambdaPrefix r A B F j (by omega)
    let v := gridLambda r A B F
    let a' := (A.arguments j (by omega)).encode ((A.arguments j (by omega)).decode a)
    have har := A.recover j (by omega) a (ha.mono (by omega))
    have hlf := gridLambdaPrefix_agree r A B F (r + 2) (Nat.le_refl _) j (by omega)
    have hold : TowerFamily.AgreeBelow j (O.eval f a') (F.eval a) := by
      intro i hi
      have he : O.eval f a' = O.eval v a :=
        O.congr f v a' a (fun m hm => (hlf m hm).symm) har
      calc
        O.eval f a' i = O.eval v a i := congrFun he i
        _ = gridApplication r A B v a i :=
          (gridApplicationPrefix_agree r A B (r + 2) (Nat.le_refl _) j (by omega) v a i hi).symm
        _ = F.eval a i := ih i hi (by omega)
    have he : (B.fiber a').code j hj (O.eval f a') = (B.fiber a).code j hj (F.eval a) :=
      (B.causal j hj a' a har _).trans ((B.fiber a).causal j hj _ _ hold)
    exact (hF a ha j (Nat.lt_succ_of_le hj)).trans he.symm

theorem gridLambda_beta (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1))
    (hF : ∀ a, A.Coherent (r + 2) (Nat.le_refl _) a →
      (B.fiber a).Coherent (r + 2) (Nat.le_refl _) (F.eval a))
    (a : TowerFamily (carrierGrid (r + 1))) (ha : A.Coherent (r + 2) (Nat.le_refl _) a) :
    TowerFamily.AgreeBelow (r + 2) (gridApplication r A B (gridLambda r A B F) a) (F.eval a) :=
  fun j hj => gridLambda_beta_coordinate r A B F hF a ha j (Nat.le_of_lt_succ hj)

/-- Finite source models store only the coordinates of their finite row. -/
abbrev FiniteGridValue (R : Nat) := (i : Fin (R + 1)) → TowerValue (carrierGrid R i.val)

def FiniteGridValue.ofTower (R : Nat) (v : TowerFamily (carrierGrid R)) : FiniteGridValue R := fun i => v i.val

theorem FiniteGridValue.ofTower_congr (R : Nat) (v w : TowerFamily (carrierGrid R))
    (h : TowerFamily.AgreeBelow (R + 1) v w) : ofTower R v = ofTower R w :=
  funext (fun i => h i.val i.isLt)

/-- The coordinate beta equations give equality of complete finite semantic
values, not just equality at a selected fixed-bound coordinate. -/
theorem gridLambda_beta_finite (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1))
    (hF : ∀ a, A.Coherent (r + 2) (Nat.le_refl _) a →
      (B.fiber a).Coherent (r + 2) (Nat.le_refl _) (F.eval a))
    (a : TowerFamily (carrierGrid (r + 1))) (ha : A.Coherent (r + 2) (Nat.le_refl _) a) :
    FiniteGridValue.ofTower (r + 1) (gridApplication r A B (gridLambda r A B F) a) =
      FiniteGridValue.ofTower (r + 1) (F.eval a) :=
  FiniteGridValue.ofTower_congr _ _ _ (gridLambda_beta r A B F hF a ha)

/-- Reducibility of abstraction uses the derived semantic beta law. Its
normalization premise is exactly the annotation premise of candidate lambda;
the body premise is pointwise reducibility, as in the fundamental lemma. -/
theorem gridPiPredicate_lambda (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1))
    (hF : ∀ a, A.Coherent (r + 2) (Nat.le_refl _) a →
      (B.fiber a).Coherent (r + 2) (Nat.le_refl _) (F.eval a))
    (p : TowerFamily (carrierGrid (r + 1)) → Candidate)
    (q : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → Candidate)
    (hq : ∀ x, TowerFamily.DependsBelow (r + 2) (q x))
    (hD : SN D)
    (hb : ∀ x, A.Coherent (r + 2) (Nat.le_refl _) x → ∀ a, (p x).contains a →
      (q x (F.eval x)).contains (subst 0 a b)) :
    ((gridPiPredicate r A B p q).candidate (gridLambda r A B F)).contains (.lam D b) := by
  have hh (x : {a // A.Coherent (r + 2) (Nat.le_refl _) a}) :
      ((p x.1).arrow (q x.1 (gridApplication r A B (gridLambda r A B F) x.1))).contains (.lam D b) := by
    rw [hq x.1 _ _ (gridLambda_beta r A B F hF x.1 x.2)]
    exact Candidate.lambda _ _ hD (hb x.1 x.2)
  let x := A.normalize (r + 2) (Nat.le_refl _) (TowerFamily.point (carrierGrid (r + 1)))
  have hx : A.Coherent (r + 2) (Nat.le_refl _) x := A.normalize_coherent _ _ _
  exact ⟨(hh ⟨x, hx⟩).1, hh⟩

end Submission.Helpers
