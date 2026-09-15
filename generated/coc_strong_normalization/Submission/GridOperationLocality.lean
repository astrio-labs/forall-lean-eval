import Submission.GridPrefixAgreement

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem gridPiCode_types_congr (r : Nat) (A A' : CausalGridType (r + 1))
    (B B' : CausalGridFamily (r + 1)) (j : Nat) (hj : j ≤ r + 1)
    (hA : CausalGridType.Agree (j + 1) A A')
    (hB : ∀ x, CausalGridType.Agree (j + 1) (B.fiber x) (B'.fiber x))
    (old old' : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (he : old = old') (f : TowerFamily (carrierGrid (r + 1))) :
    gridPiCode r A B j hj old f = gridPiCode r A' B' j hj old' f := by
  have hp := A.telescopeAt_congr j (by omega) (hA.mono (Nat.le_succ j))
  have hb : (fun x => (B.fiber x).code j hj) = (fun x => (B'.fiber x).code j hj) :=
    funext (fun x => hB x j hj (Nat.lt_succ_self _))
  rw [gridPiCode_prefix, gridPiCode_prefix, hp, hA j hj (Nat.lt_succ_self _), hb, he]

theorem gridPiApplyAt_types_congr (r : Nat) (A A' : CausalGridType (r + 1))
    (B B' : CausalGridFamily (r + 1)) (j : Nat) (hj : j ≤ r + 1)
    (hA : CausalGridType.Agree (j + 1) A A')
    (hB : ∀ x, CausalGridType.Agree (j + 1) (B.fiber x) (B'.fiber x))
    (old old' : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (he : old = old') (f a : TowerFamily (carrierGrid (r + 1))) :
    gridPiApplyAt r A B j hj old f a = gridPiApplyAt r A' B' j hj old' f a := by
  have hp := A.telescopeAt_congr j (by omega) (hA.mono (Nat.le_succ j))
  have hb : (fun x => (B.fiber x).code j hj) = (fun x => (B'.fiber x).code j hj) :=
    funext (fun x => hB x j hj (Nat.lt_succ_self _))
  rw [gridPiApplyAt_prefix, gridPiApplyAt_prefix, hp, hA j hj (Nat.lt_succ_self _), hb, he]

/-- All application values below d depend only on carrier fields below d.
The telescope and every earlier application are compared by induction. -/
theorem gridApplicationPrefix_types_congr (r : Nat) (A A' : CausalGridType (r + 1))
    (B B' : CausalGridFamily (r + 1)) (d : Nat) (hd : d ≤ r + 2)
    (hA : CausalGridType.Agree d A A')
    (hB : ∀ x, CausalGridType.Agree d (B.fiber x) (B'.fiber x)) :
    (gridApplicationPrefix r A B d hd).eval = (gridApplicationPrefix r A' B' d hd).eval := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hp := ih (by omega) (hA.mono (Nat.le_succ d)) (fun x => (hB x).mono (Nat.le_succ d))
    funext f a
    change ((gridApplicationPrefix r A B d (by omega)).eval f a).set d _ =
      ((gridApplicationPrefix r A' B' d (by omega)).eval f a).set d _
    rw [congrFun (congrFun hp f) a,
      gridPiApplyAt_types_congr r A A' B B' d (by omega) hA hB _ _ hp f a]

theorem gridPiType_types_congr (r : Nat) (A A' : CausalGridType (r + 1))
    (B B' : CausalGridFamily (r + 1)) (d : Nat)
    (hA : CausalGridType.Agree d A A')
    (hB : ∀ x, CausalGridType.Agree d (B.fiber x) (B'.fiber x)) :
    CausalGridType.Agree d (gridPiType r A B) (gridPiType r A' B') := by
  intro j hj hjd
  funext f
  exact gridPiCode_types_congr r A A' B B' j hj (hA.mono (by omega))
    (fun x => (hB x).mono (by omega)) _ _
    (gridApplicationPrefix_types_congr r A A' B B' j (by omega) (hA.mono (by omega))
      (fun x => (hB x).mono (by omega))) f

theorem finitePiType_carrier_congr (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (d : Nat)
    (hA : CausalGridType.Agree d A.carrier A'.carrier)
    (hB : ∀ x, CausalGridType.Agree d (B.fiber x).carrier (B'.fiber x).carrier) :
    CausalGridType.Agree d (finitePiType r A B).carrier (finitePiType r A' B').carrier :=
  gridPiType_types_congr r A.carrier A'.carrier B.toCausal B'.toCausal d hA
    (fun x => hB (FiniteGridValue.ofTower _ x))

theorem gridApplication_types_congr (r : Nat) (A A' : CausalGridType (r + 1))
    (B B' : CausalGridFamily (r + 1)) (d : Nat) (hd : d ≤ r + 2)
    (hA : CausalGridType.Agree d A A')
    (hB : ∀ x, CausalGridType.Agree d (B.fiber x) (B'.fiber x))
    (f a : TowerFamily (carrierGrid (r + 1))) :
    TowerFamily.AgreeBelow d (gridApplication r A B f a) (gridApplication r A' B' f a) := by
  intro i hi
  have he := gridApplicationPrefix_types_congr r A A' B B' d hd hA hB
  exact (gridApplicationPrefix_agree r A B (r + 2) (Nat.le_refl _) d hd f a i hi).trans
    ((congrArg (fun P => P f a i) he).trans
      (gridApplicationPrefix_agree r A' B' (r + 2) (Nat.le_refl _) d hd f a i hi).symm)

end Submission.Helpers
