import Submission.CoherentPiFields

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem prefixBindingCode_congr (r j : Nat) (hj : j ≤ r + 1)
    (P : UniversePrefix (r + 1) j)
    {D D' E E' : P.El → (carrierGrid (r + 1) j).Code}
    (hD : D = D') (hE : E = E') :
    (prefixBindingObject r j hj P D E).code =
      (prefixBindingObject r j hj P D' E').code := by
  cases hD
  cases hE
  rfl

noncomputable def prefixApplyFields (r j : Nat) (hj : j ≤ r + 1) (P : UniversePrefix (r + 1) j)
    (F G : P.El → (carrierGrid (r + 1) j).Code) (f a : TowerFamily (carrierGrid (r + 1))) :
    TowerValue (carrierGrid (r + 1) j) :=
  let x := P.rowArguments.decode a
  let O := prefixBindingObject r j hj P F G
  ⟨G x, O.values.decode ((f j).cast O.code) x ((a j).cast (F x))⟩

theorem prefixPiApply_fields (r j : Nat) (hj : j ≤ r + 1) (P : UniversePrefix (r + 1) j)
    (D : TowerFamily (carrierGrid (r + 1)) → (carrierGrid (r + 1) j).Code)
    (E : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → (carrierGrid (r + 1) j).Code)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f a : TowerFamily (carrierGrid (r + 1))) :
    prefixPiApply r j hj P D E old f a = prefixApplyFields r j hj P
      (fun x => D (P.rowArguments.encode x)) (fun x => E (P.rowArguments.encode x) (old f (P.rowArguments.encode x))) f a := rfl

theorem coherentPi_codomain_fields (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1))
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1)
    (he : (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval)
    (f : TowerFamily (carrierGrid (r + 1))) :
    (fun x : (A.carrier.telescopeAt j (by omega)).El =>
      let a := (A.carrier.arguments j (by omega)).encode x
      (B.toCausal.fiber a).code j hj ((gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval f a)) =
    (fun x : (A.carrier.telescopeAt j (by omega)).El =>
      let a := (A.carrier.arguments j (by omega)).encode x
      (B'.toCausal.fiber a).code j hj ((gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval f a)) := by
  funext x
  exact (coherentPi_codomain_field r A B B' hB j hj f x).trans
    (congrArg ((B'.toCausal.fiber ((A.carrier.arguments j (by omega)).encode x)).code j hj)
      (congrFun (congrFun he f) ((A.carrier.arguments j (by omega)).encode x)))

theorem finitePiCode_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1)
    (he : (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval)
    (f : TowerFamily (carrierGrid (r + 1))) :
    (finitePiType r A B).carrier.code j hj f = (finitePiType r A' B').carrier.code j hj f := by
  have hF := funext (coherentPi_domain_field r hA j hj)
  have hG := coherentPi_codomain_fields r A A' B B' hB j hj he f
  change gridPiCode r A.carrier B.toCausal j hj _ f = gridPiCode r A'.carrier B'.toCausal j hj _ f
  rw [gridPiCode_prefix, gridPiCode_prefix, ← hA.telescopeAt j (by omega)]
  unfold prefixPiCode
  change (prefixBindingObject r j hj (A.carrier.telescopeAt j (by omega)) _ _).code = _
  dsimp only [CausalGridType.arguments, UniversePrefix.rowArguments] at hF hG ⊢
  exact prefixBindingCode_congr r j hj _ hF hG

theorem finitePiApplyAt_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1)
    (he : (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval)
    (f a : TowerFamily (carrierGrid (r + 1))) :
    gridPiApplyAt r A.carrier B.toCausal j hj (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval f a =
      gridPiApplyAt r A'.carrier B'.toCausal j hj (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval f a := by
  have hF := funext (coherentPi_domain_field r hA j hj)
  have hG := coherentPi_codomain_fields r A A' B B' hB j hj he f
  rw [gridPiApplyAt_prefix, gridPiApplyAt_prefix, ← hA.telescopeAt j (by omega)]
  rw [prefixPiApply_fields, prefixPiApply_fields]
  dsimp only [CausalGridType.arguments, UniversePrefix.rowArguments] at hF hG ⊢
  rw [hF, hG]

theorem finiteApplicationPrefix_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (d : Nat) (hd : d ≤ r + 2) :
    (gridApplicationPrefix r A.carrier B.toCausal d hd).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal d hd).eval := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have he := ih (by omega)
    funext f a
    change ((gridApplicationPrefix r A.carrier B.toCausal d (by omega)).eval f a).set d _ =
      ((gridApplicationPrefix r A'.carrier B'.toCausal d (by omega)).eval f a).set d _
    rw [congrFun (congrFun he f) a, finitePiApplyAt_coherent_eq r A A' B B' hA hB d (by omega) he f a]

/-- Application is independent of semantic type representations that agree
on coherent data; the codomain premise is needed only on valid arguments. -/
theorem finiteTypeApplication_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (f a : FiniteGridValue (r + 1)) : finiteTypeApplication r A B f a = finiteTypeApplication r A' B' f a :=
  congrArg (FiniteGridValue.ofTower _) (congrFun (congrFun
    (finiteApplicationPrefix_coherent_eq r A A' B B' hA hB (r + 2) (Nat.le_refl _))
      (FiniteGridValue.toTower _ f)) (FiniteGridValue.toTower _ a))

theorem finitePiType_carrier_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1) (f : TowerFamily (carrierGrid (r + 1))) :
    (finitePiType r A B).carrier.code j hj f = (finitePiType r A' B').carrier.code j hj f :=
  finitePiCode_coherent_eq r A A' B B' hA hB j hj
    (finiteApplicationPrefix_coherent_eq r A A' B B' hA hB j (by omega)) f

end Submission.Helpers
