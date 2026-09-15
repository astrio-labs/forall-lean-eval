import Submission.SourceGridFormationUniform

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

def CausalGridType.Agree (d : Nat) (A B : CausalGridType R) : Prop :=
  ∀ i hi, i < d → A.code i hi = B.code i hi

theorem CausalGridType.Agree.mono {A B : CausalGridType R} (h : Agree d A B) (he : e ≤ d) : Agree e A B :=
  fun i hi hil => h i hi (by omega)

theorem CausalGridType.telescopeAt_congr {A B : CausalGridType R} (d : Nat) (hd : d ≤ R + 1)
    (h : Agree d A B) : A.telescopeAt d hd = B.telescopeAt d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    unfold telescopeAt
    rw [carrierFieldPrefix, carrierFieldPrefix]
    have hp := ih (by omega) (h.mono (Nat.le_succ d))
    change carrierFieldPrefix R A.code d (by omega) = carrierFieldPrefix R B.code d (by omega) at hp
    rw [hp, h d (by omega) (Nat.lt_succ_self d)]

noncomputable def UniversePrefix.rowArguments (P : UniversePrefix R d) :
    CarrierRetraction P.El (TowerFamily (carrierGrid R)) :=
  P.telescope.valuesRetraction (fun i => CarrierRepresentation.identity (carrierGrid R i)) P.ordered

/-- The binder object depends only on its explicit preceding telescope. -/
noncomputable def prefixBindingObject (r : Nat) : (j : Nat) → (hj : j ≤ r + 1) →
    (P : UniversePrefix (r + 1) j) →
    (D E : P.El → (carrierGrid (r + 1) j).Code) →
    CarrierObject (carrierGrid (r + 1) j)
      ((x : P.El) → (carrierGrid (r + 1) j).El (D x) → (carrierGrid (r + 1) j).El (E x))
  | 0, _, P, D, E => by
    obtain ⟨T, hT⟩ := P
    have he : T = .nil := hT.empty (Nat.le_refl _)
    subst T
    exact CarrierObject.pullback
      ((CarrierFunction.singletonDomain () (inferInstanceAs (Subsingleton Unit))
        (fun x => (carrierGrid (r + 1) 0).El (D x) → (carrierGrid (r + 1) 0).El (E x))).toRetraction)
      (CarrierObject.arrow (carrierGridArrows (r + 1) 0)
        (CarrierObject.direct _ (D ())) (CarrierObject.direct _ (E ())))
  | j + 1, hj, P, D, E =>
    let hw : P.telescope.Within j := (P.telescope.within_all j).mpr
      (P.telescope.all_mono P.ordered.all (fun _ hi => Nat.le_of_lt_succ hi))
    ⟨carrierGridBinderCode r j (by omega) P.telescope hw D E,
      ⟨carrierGridBinderLambda r j (by omega) P.telescope hw D E,
        carrierGridBinderApply r j (by omega) P.telescope hw D E,
        fun f => funext (fun x => funext (fun y => carrierGrid_binder_beta r j (by omega) P.telescope hw D E f x y))⟩⟩

theorem gridBindingObject_prefix (r : Nat) (A : CausalGridType (r + 1)) (j : Nat) (hj : j ≤ r + 1)
    (D E : (A.telescopeAt j (by omega)).El → (carrierGrid (r + 1) j).Code) :
    gridBindingObject r A j hj D E = prefixBindingObject r j hj (A.telescopeAt j (by omega)) D E := by
  cases j <;> rfl

noncomputable def prefixPiCode (r j : Nat) (hj : j ≤ r + 1) (P : UniversePrefix (r + 1) j)
    (D : TowerFamily (carrierGrid (r + 1)) → (carrierGrid (r + 1) j).Code)
    (E : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → (carrierGrid (r + 1) j).Code)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f : TowerFamily (carrierGrid (r + 1))) : (carrierGrid (r + 1) j).Code :=
  (prefixBindingObject r j hj P (fun x => D (P.rowArguments.encode x))
    (fun x => E (P.rowArguments.encode x) (old f (P.rowArguments.encode x)))).code

noncomputable def prefixPiApply (r j : Nat) (hj : j ≤ r + 1) (P : UniversePrefix (r + 1) j)
    (D : TowerFamily (carrierGrid (r + 1)) → (carrierGrid (r + 1) j).Code)
    (E : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → (carrierGrid (r + 1) j).Code)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f a : TowerFamily (carrierGrid (r + 1))) : TowerValue (carrierGrid (r + 1) j) :=
  let x := P.rowArguments.decode a
  let F := fun x => D (P.rowArguments.encode x)
  let G := fun x => E (P.rowArguments.encode x) (old f (P.rowArguments.encode x))
  let O := prefixBindingObject r j hj P F G
  ⟨G x, O.values.decode ((f j).cast O.code) x ((a j).cast (F x))⟩

theorem gridPiCode_prefix (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f : TowerFamily (carrierGrid (r + 1))) :
    gridPiCode r A B j hj old f = prefixPiCode r j hj (A.telescopeAt j (by omega))
      (A.code j hj) (fun x => (B.fiber x).code j hj) old f := by
  unfold gridPiCode
  rw [gridBindingObject_prefix]
  rfl

theorem gridPiApplyAt_prefix (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f a : TowerFamily (carrierGrid (r + 1))) :
    gridPiApplyAt r A B j hj old f a = prefixPiApply r j hj (A.telescopeAt j (by omega))
      (A.code j hj) (fun x => (B.fiber x).code j hj) old f a := by
  unfold gridPiApplyAt
  dsimp only
  rw [gridBindingObject_prefix]
  rfl

end Submission.Helpers
