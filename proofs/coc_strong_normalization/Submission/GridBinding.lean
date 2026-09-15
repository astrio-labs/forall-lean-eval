import Submission.CausalCarriers

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem CarrierTelescope.GridForm.snoc {T : CarrierTelescope (carrierGrid R)}
    (hT : T.GridForm R s) (i : Nat) (A : T.El → (carrierGrid R i).Code)
    (hA : ∀ x, GridFormation R i s (A x)) : (T.snoc i A).GridForm R s := by
  induction T with
  | nil => exact ⟨hA (), fun _ => True.intro⟩
  | cons j B C ih => exact ⟨hT.1, fun x => ih x (hT.2 x) _ (fun y => hA ⟨x, y⟩)⟩

theorem CausalGridType.telescope_formed (A : CausalGridType R) (hA : A.Formed s)
    (d : Nat) (hd : d ≤ R + 1) : (A.telescopeAt d hd).telescope.GridForm R s := by
  induction d with
  | zero => trivial
  | succ d ih => exact (ih (by omega)).snoc d _ (fun x => hA d (by omega) _)

theorem CausalGridType.telescope_within (A : CausalGridType R) (d : Nat) (hd : d + 1 ≤ R + 1) :
    (A.telescopeAt (d + 1) hd).telescope.Within d :=
  ((A.telescopeAt (d + 1) hd).telescope.within_all d).mpr
    ((A.telescopeAt (d + 1) hd).telescope.all_mono (A.telescopeAt (d + 1) hd).ordered.all
      (fun _ hi => Nat.le_of_lt_succ hi))

/-- A binder at coordinate zero is an ordinary arrow. At every later
coordinate it quantifies over the complete preceding domain telescope. -/
noncomputable def gridBindingObject (r : Nat) (A : CausalGridType (r + 1)) :
    (j : Nat) → (hj : j ≤ r + 1) →
    (D E : (A.telescopeAt j (by omega)).El → (carrierGrid (r + 1) j).Code) →
    CarrierObject (carrierGrid (r + 1) j)
      ((x : (A.telescopeAt j (by omega)).El) →
        (carrierGrid (r + 1) j).El (D x) → (carrierGrid (r + 1) j).El (E x))
  | 0, _, D, E =>
    CarrierObject.pullback
      ((CarrierFunction.singletonDomain () (inferInstanceAs (Subsingleton Unit))
        (fun x => (carrierGrid (r + 1) 0).El (D x) → (carrierGrid (r + 1) 0).El (E x))).toRetraction)
      (CarrierObject.arrow (carrierGridArrows (r + 1) 0)
        (CarrierObject.direct _ (D ())) (CarrierObject.direct _ (E ())))
  | j + 1, hj, D, E =>
    let T := (A.telescopeAt (j + 1) (by omega)).telescope
    let hw := A.telescope_within j (by omega)
    ⟨carrierGridBinderCode r j (by omega) T hw D E,
      ⟨carrierGridBinderLambda r j (by omega) T hw D E,
        carrierGridBinderApply r j (by omega) T hw D E,
        fun f => funext (fun x => funext (fun y => carrierGrid_binder_beta r j (by omega) T hw D E f x y))⟩⟩

theorem gridBindingObject_formed (r : Nat) (A : CausalGridType (r + 1))
    (j : Nat) (hj : j ≤ r + 1)
    (D E : (A.telescopeAt j (by omega)).El → (carrierGrid (r + 1) j).Code)
    (hr : Rl sA sB sC) (hA : A.Formed sA)
    (hD : ∀ x, GridFormation (r + 1) j sA (D x))
    (hE : ∀ x, GridFormation (r + 1) j sB (E x)) :
    GridFormation (r + 1) j sC (gridBindingObject r A j hj D E).code := by
  cases j with
  | zero => exact gridFormation_arrow (by omega) hr (hD ()) (hE ())
  | succ j =>
    exact carrierGridBinderCode_formation r j (by omega) _ _ D E hr
      (A.telescope_formed hA _ _) hD hE

/-- A dependent codomain reads only the preceding coordinates of its domain
argument. Each of its own carriers has the same dependency discipline. -/
structure CausalGridFamily (R : Nat) where
  fiber : TowerFamily (carrierGrid R) → CausalGridType R
  causal : ∀ j hj x y, TowerFamily.AgreeBelow j x y → ∀ v, (fiber x).code j hj v = (fiber y).code j hj v

noncomputable def gridPiDomain (A : CausalGridType R) (j : Nat) (hj : j ≤ R) :
    (A.telescopeAt j (by omega)).El → (carrierGrid R j).Code :=
  fun x => A.code j hj ((A.arguments j (by omega)).encode x)

noncomputable def gridPiCodomain (A : CausalGridType R) (B : CausalGridFamily R)
    (j : Nat) (hj : j ≤ R)
    (old : TowerFamily (carrierGrid R) → TowerFamily (carrierGrid R) → TowerFamily (carrierGrid R))
    (f : TowerFamily (carrierGrid R)) :
    (A.telescopeAt j (by omega)).El → (carrierGrid R j).Code :=
  fun x =>
    let a := (A.arguments j (by omega)).encode x
    (B.fiber a).code j hj (old f a)

noncomputable def gridPiCode (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f : TowerFamily (carrierGrid (r + 1))) : (carrierGrid (r + 1) j).Code :=
  (gridBindingObject r A j hj (gridPiDomain A j hj) (gridPiCodomain A B j hj old f)).code

noncomputable def gridPiApplyAt (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f a : TowerFamily (carrierGrid (r + 1))) : TowerValue (carrierGrid (r + 1) j) :=
  let x := (A.arguments j (by omega)).decode a
  let D := gridPiDomain A j hj
  let E := gridPiCodomain A B j hj old f
  let O := gridBindingObject r A j hj D E
  ⟨E x, O.values.decode ((f j).cast O.code) x ((a j).cast (D x))⟩

theorem gridPiCode_formed (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1)
    (old : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)))
    (f : TowerFamily (carrierGrid (r + 1)))
    (hr : Rl sA sB sC) (hA : A.Formed sA) (hB : ∀ a, (B.fiber a).Formed sB) :
    GridFormation (r + 1) j sC (gridPiCode r A B j hj old f) :=
  gridBindingObject_formed r A j hj _ _ hr hA (fun _ => hA j hj _) (fun _ => hB _ j hj _)

end Submission.Helpers
