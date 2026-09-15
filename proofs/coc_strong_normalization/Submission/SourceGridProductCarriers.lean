import Submission.GridOperationLocality

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem sourceGridInterpretation_zero (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A : Tm) (v : TowerFamily (carrierGrid (r + 1))) :
    (sourceGridInterpretation r Γ ρ A).carrier.code 0 (by omega) v = arityAt (.type r) A := by
  have he := sourceGridStages_interp_before r (r + 2) (Nat.le_refl _) 0 (by omega) A Γ ρ 0 (by omega) (Nat.le_refl _) v
  refine he.trans ?_
  change (if he : 0 = 0 then gridCodeCast (rfl : r + 1 = r + 1) he.symm (arityAt (.type r) A : (carrierGrid (r + 1) 0).Code)
    else (carrierGrid (r + 1) 0).defaultCode) = _
  rw [dif_pos rfl]
  rfl

theorem sourceGridStages_interp_agree (r d : Nat) (hd : d ≤ r + 2) (A : Tm) (Γ : List Tm)
    (ρ δ : GridEnvironment (r + 1)) (h : GridEnvironment.Agree d ρ δ) :
    CausalGridType.Agree (d + 1) ((sourceGridStages r d hd A).interp Γ ρ).carrier
      (sourceGridInterpretation r Γ δ A).carrier := by
  intro i hi hid
  funext v
  exact ((sourceGridStages r d hd A).interp_causal Γ ρ δ i hi (h.mono (by omega)) v).trans
    (sourceGridStages_interp_before r (r + 2) (Nat.le_refl _) d hd A Γ δ i hi (by omega) v).symm

theorem gridPiType_zero (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (v : TowerFamily (carrierGrid (r + 1))) :
    (gridPiType r A B).code 0 (by omega) v =
      (A.code 0 (by omega) (TowerFamily.point (carrierGrid (r + 1)))).arrow
        ((B.fiber (TowerFamily.point (carrierGrid (r + 1)))).code 0 (by omega)
          (TowerFamily.point (carrierGrid (r + 1)))) := rfl

/-- The complete source product carrier agrees with the reusable dependent
Pi algebra at every coordinate, uniformly in the finite universe bound. -/
theorem sourceGridInterpretation_pi_carrier (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A B : Tm) (i : Nat) (hi : i ≤ r + 1) (v : TowerFamily (carrierGrid (r + 1))) :
    (sourceGridInterpretation r Γ ρ (.pi A B)).carrier.code i hi v =
      (finitePiType r (sourceGridInterpretation r Γ ρ A)
        ((sourceGridMeaning r B).bodyFamily Γ ρ A)).carrier.code i hi v := by
  cases i with
  | zero =>
    rw [sourceGridInterpretation_zero]
    change (arityAt (.type r) A).arrow (arityAt (.type r) B) =
      (gridPiType r (sourceGridInterpretation r Γ ρ A).carrier
        ((sourceGridMeaning r B).bodyFamily Γ ρ A).toCausal).code 0 hi v
    rw [gridPiType_zero]
    change (arityAt (.type r) A).arrow (arityAt (.type r) B) =
      ((sourceGridInterpretation r Γ ρ A).carrier.code 0 (by omega) _).arrow
        ((sourceGridInterpretation r (A :: Γ) (push _ ρ) B).carrier.code 0 (by omega) _)
    rw [sourceGridInterpretation_zero, sourceGridInterpretation_zero]
  | succ i =>
    let ε := GridEnvironment.truncate (i + 1) ρ
    let stage := sourceGridStages r (i + 1) (by omega)
    have hε : GridEnvironment.Agree (i + 1) ε ρ := GridEnvironment.truncate_below ρ (i + 1)
    have he := sourceGridStages_interp_before r (r + 2) (Nat.le_refl _) (i + 1) (by omega)
      (.pi A B) Γ ρ (i + 1) hi (Nat.le_refl _) v
    refine he.trans ?_
    change (sourceGridUpgrade (r + 1) i
      ((sourceGridStages r i (by omega) (.pi A B)).interp Γ ε)
      (finitePiType r ((stage A).interp Γ ε) ((stage B).bodyFamily Γ ε A))).carrier.code (i + 1) hi v = _
    change (if i + 1 = i + 1 then _ else _) = _
    rw [if_pos rfl]
    apply congrFun
    apply finitePiType_carrier_congr r _ _ _ _ (i + 2)
    · exact sourceGridStages_interp_agree r (i + 1) (by omega) A Γ ε ρ hε
    · intro a
      exact sourceGridStages_interp_agree r (i + 1) (by omega) B (A :: Γ) (push a ε) (push a ρ)
        (hε.push (fun _ _ => rfl))
    · exact Nat.lt_succ_self (i + 1)

theorem FiniteGridType.ext_fields (A B : FiniteGridType R)
    (hc : ∀ i hi v, A.carrier.code i hi v = B.carrier.code i hi v)
    (hp : ∀ v, A.candidate v = B.candidate v) : A = B := by
  cases A with
  | mk Ac Ap =>
    cases B with
    | mk Bc Bp =>
      have he : Ac = Bc := by
        cases Ac
        cases Bc
        congr 1
        funext i hi v
        exact hc i hi v
      cases he
      have he' : Ap = Bp := funext hp
      cases he'
      rfl

theorem sourceGridInterpretation_pi (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (A B : Tm) :
    sourceGridInterpretation r Γ ρ (.pi A B) =
      finitePiType r (sourceGridInterpretation r Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A) := by
  apply FiniteGridType.ext_fields
  · exact sourceGridInterpretation_pi_carrier r Γ ρ A B
  · intro f
    exact sourceGridInterpretation_pi_candidate r Γ ρ A B f

end Submission.Helpers
