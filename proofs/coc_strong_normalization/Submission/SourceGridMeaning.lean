import Submission.UniformUniverseIO
import Submission.UpperGridSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- Raw syntax operations are observed through coordinate projections. A
value at j reads environment coordinates through j; a carrier at j reads
strictly earlier coordinates. Candidates read the whole finite environment. -/
structure SourceGridMeaning (R : Nat) where
  rawValue : List Tm → GridEnvironment R → FiniteGridValue R
  rawType : List Tm → GridEnvironment R → FiniteGridType R

noncomputable def SourceGridMeaning.eval (M : SourceGridMeaning R) (Γ : List Tm)
    (ρ : GridEnvironment R) : FiniteGridValue R :=
  fun i => M.rawValue Γ (GridEnvironment.truncate (i.val + 1) ρ) i

noncomputable def SourceGridMeaning.interp (M : SourceGridMeaning R) (Γ : List Tm)
    (ρ : GridEnvironment R) : FiniteGridType R where
  carrier := {
    code := fun j hj v => (M.rawType Γ (GridEnvironment.truncate j ρ)).carrier.code j hj v
    causal := fun j hj => (M.rawType Γ (GridEnvironment.truncate j ρ)).carrier.causal j hj }
  candidate := (M.rawType Γ ρ).candidate

theorem SourceGridMeaning.eval_causal (M : SourceGridMeaning R) (Γ : List Tm)
    (ρ δ : GridEnvironment R) (i : Fin (R + 1)) (h : GridEnvironment.Agree (i.val + 1) ρ δ) :
    M.eval Γ ρ i = M.eval Γ δ i :=
  congrArg (fun ε => M.rawValue Γ ε i) (GridEnvironment.truncate_congr h)

theorem SourceGridMeaning.eval_agree (M : SourceGridMeaning R) (Γ : List Tm)
    (ρ δ : GridEnvironment R) (h : GridEnvironment.Agree d ρ δ) :
    FiniteGridValue.Agree d (M.eval Γ ρ) (M.eval Γ δ) :=
  fun i hi => M.eval_causal Γ ρ δ i (h.mono (by omega))

theorem SourceGridMeaning.interp_causal (M : SourceGridMeaning R) (Γ : List Tm)
    (ρ δ : GridEnvironment R) (j : Nat) (hj : j ≤ R) (h : GridEnvironment.Agree j ρ δ)
    (v : TowerFamily (carrierGrid R)) :
    (M.interp Γ ρ).carrier.code j hj v = (M.interp Γ δ).carrier.code j hj v :=
  congrArg (fun ε => (M.rawType Γ ε).carrier.code j hj v) (GridEnvironment.truncate_congr h)

noncomputable def SourceGridMeaning.bodyMap (M : SourceGridMeaning R) (Γ : List Tm)
    (ρ : GridEnvironment R) (A : Tm) : FiniteGridMap R where
  eval x := M.eval (A :: Γ) (push x ρ)
  causal j hj x y h := by
    apply M.eval_causal
    apply GridEnvironment.Agree.push (fun _ _ _ => rfl)
    intro i hi
    exact (FiniteGridValue.toTower_at R x i).symm.trans
      ((h i.val hi).trans (FiniteGridValue.toTower_at R y i))

noncomputable def SourceGridMeaning.bodyFamily (M : SourceGridMeaning R) (Γ : List Tm)
    (ρ : GridEnvironment R) (A : Tm) : FiniteGridFamily R where
  fiber x := M.interp (A :: Γ) (push x ρ)
  causal j hj x y h v := by
    apply M.interp_causal
    apply GridEnvironment.Agree.push (fun _ _ _ => rfl)
    intro i hi
    exact (FiniteGridValue.toTower_at R x i).symm.trans
      ((h i.val hi).trans (FiniteGridValue.toTower_at R y i))

/-- Advance just the next carrier, or the candidate at the last stage.
Every preceding carrier remains frozen. -/
noncomputable def sourceGridUpgrade (R j : Nat) (old next : FiniteGridType R) : FiniteGridType R where
  carrier := {
    code := fun i hi v => if i = j + 1 then next.carrier.code i hi v else old.carrier.code i hi v
    causal := by
      intro i hi v w h
      split
      · exact next.carrier.causal i hi v w h
      · exact old.carrier.causal i hi v w h }
  candidate := if j = R then next.candidate else old.candidate

theorem sourceGridUpgrade_before (R j : Nat) (old next : FiniteGridType R) (i : Nat) (hi : i ≤ R)
    (hij : i ≤ j) (v : TowerFamily (carrierGrid R)) :
    (sourceGridUpgrade R j old next).carrier.code i hi v = old.carrier.code i hi v := by
  change (if i = j + 1 then _ else _) = _
  rw [if_neg (by omega)]

noncomputable def sourceGridBaseType (r : Nat) (t : Tm) : FiniteGridType (r + 1) where
  carrier := {
    code := fun j _ _ => if he : j = 0 then
      gridCodeCast rfl he.symm (arityAt (.type r) t : (carrierGrid (r + 1) 0).Code)
      else (carrierGrid (r + 1) j).defaultCode
    causal := fun _ _ _ _ _ => rfl }
  candidate _ := Candidate.sn

noncomputable def sourceGridBase (r : Nat) (t : Tm) : SourceGridMeaning (r + 1) where
  rawValue _ _ := FiniteGridValue.ofTower _ (TowerFamily.point (carrierGrid (r + 1)))
  rawType _ _ := sourceGridBaseType r t

noncomputable def sourceGridInferred (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (t : Tm) :
    (carrierGrid (r + 1) j).Code :=
  ((old (chosenType (r + 2) Γ t)).interp Γ ρ).carrier.code j hj
    (FiniteGridValue.toTower _ ((old t).eval Γ ρ))

noncomputable def sourceGridForcedValue (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (t : Tm)
    (v : TowerValue (carrierGrid (r + 1) j)) : FiniteGridValue (r + 1) :=
  ((old t).eval Γ ρ).set j ⟨sourceGridInferred r j hj old Γ ρ t, v.cast (sourceGridInferred r j hj old Γ ρ t)⟩

theorem sourceGridForcedValue_code (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (t : Tm)
    (v : TowerValue (carrierGrid (r + 1) j)) :
    (sourceGridForcedValue r j hj old Γ ρ t v ⟨j, Nat.lt_succ_of_le hj⟩).code =
      sourceGridInferred r j hj old Γ ρ t := by
  unfold sourceGridForcedValue
  rw [FiniteGridValue.set_same]

end Submission.Helpers
