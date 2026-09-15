import Submission.GridApplication

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem CausalGridType.Coherent.mono {A : CausalGridType R} {v : TowerFamily (carrierGrid R)}
    (h : A.Coherent d hd v) (he : e ≤ d) : A.Coherent e (by omega) v :=
  fun i hi => h i (by omega)

theorem CausalGridType.coherent_extend (A : CausalGridType R) (d : Nat) (hd : d ≤ R)
    (v : TowerFamily (carrierGrid R)) (hv : A.Coherent d (by omega) v)
    (x : TowerValue (carrierGrid R d)) (hx : x.code = A.code d hd v) :
    A.Coherent (d + 1) (by omega) (v.set d x) := by
  intro i hi
  have he : A.code i (by omega) v = A.code i (by omega) (v.set d x) :=
    A.causal i (by omega) _ _ (fun j hj => (TowerFamily.set_other v d j x (by omega)).symm)
  by_cases hid : i = d
  · subst i
    rw [TowerFamily.set_same]
    exact hx.trans he
  · rw [TowerFamily.set_other v d i x hid]
    exact (hv i (by omega)).trans he

/-- Complete any finite prefix with carrier points, forcing each coordinate
only after its preceding carrier arguments have been constructed. -/
noncomputable def CausalGridType.normalize (A : CausalGridType R) :
    (d : Nat) → d ≤ R + 1 → TowerFamily (carrierGrid R) → TowerFamily (carrierGrid R)
  | 0, _, _ => TowerFamily.point (carrierGrid R)
  | d + 1, hd, v =>
    let w := A.normalize d (by omega) v
    w.set d ⟨A.code d (by omega) w, (v d).cast (A.code d (by omega) w)⟩

theorem CausalGridType.normalize_coherent (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) : A.Coherent d hd (A.normalize d hd v) := by
  induction d with
  | zero => intro i hi; omega
  | succ d ih => exact A.coherent_extend d (by omega) _ (ih (by omega)) _ rfl

theorem CausalGridType.normalize_agree (A : CausalGridType R) (e : Nat) (he : e ≤ R + 1)
    (d : Nat) (hd : d ≤ e) (v : TowerFamily (carrierGrid R)) :
    TowerFamily.AgreeBelow d (A.normalize e he v) (A.normalize d (by omega) v) := by
  induction e with
  | zero => intro i hi; omega
  | succ e ih =>
    by_cases hde : d = e + 1
    · subst d; exact .refl _ _
    · intro i hi
      change (A.normalize e (by omega) v).set e _ i = _
      rw [TowerFamily.set_other _ e i _ (by omega)]
      exact ih (by omega) (by omega) i hi

theorem CausalGridType.normalize_recover (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) (hv : A.Coherent d hd v) :
    TowerFamily.AgreeBelow d (A.normalize d hd v) v := by
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    have hp := ih (by omega) (hv.mono (Nat.le_succ d))
    intro i hi
    change (A.normalize d (by omega) v).set d _ i = v i
    by_cases hid : i = d
    · subst i
      rw [TowerFamily.set_same]
      have hc := A.causal d (by omega) _ _ hp
      rw [hc]
      exact (v d).mk_cast (hv d (Nat.lt_succ_self _))
    · rw [TowerFamily.set_other _ d i _ hid]
      exact hp i (by omega)

theorem CausalGridType.complete_recover (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) (hv : A.Coherent d hd v) :
    TowerFamily.AgreeBelow d (A.normalize (R + 1) (Nat.le_refl _) v) v :=
  fun i hi => (A.normalize_agree (R + 1) (Nat.le_refl _) d hd v i hi).trans
    (A.normalize_recover d hd v hv i hi)

/-- Product formation only needs codomain formation on fully coherent
domain arguments. Every partial domain telescope has such a completion. -/
theorem gridPiType_formed_coherent (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) (hr : Rl sA sB sC) (hA : A.Formed sA)
    (hB : ∀ a, A.Coherent (r + 2) (Nat.le_refl _) a → (B.fiber a).Formed sB) :
    (gridPiType r A B).Formed sC := by
  intro j hj f
  apply gridBindingObject_formed r A j hj _ _ hr hA (fun _ => hA j hj _)
  intro x
  let a := (A.arguments j (by omega)).encode x
  have ha := A.section_coherent j (by omega) x
  have har := A.complete_recover j (by omega) a ha
  have hc := B.causal j hj _ a har
    ((gridApplicationPrefix r A B j (by omega)).eval f a)
  change GridFormation (r + 1) j sB ((B.fiber a).code j hj
    ((gridApplicationPrefix r A B j (by omega)).eval f a))
  rw [← hc]
  exact hB _ (A.normalize_coherent (r + 2) (Nat.le_refl _) a) j hj _

end Submission.Helpers
