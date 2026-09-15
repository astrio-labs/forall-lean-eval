import Submission.SourceGridMeaning

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- One source stage, structurally recursive on the trusted term syntax.
Chosen types and products are interpreted only by the preceding stage.
The recursive body interpretation supplies the current value coordinate. -/
noncomputable def sourceGridStep (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) : Tm → SourceGridMeaning (r + 1)
  | .var x =>
    let V Γ ρ := sourceGridForcedValue r j hj old Γ ρ (.var x) (ρ x ⟨j, Nat.lt_succ_of_le hj⟩)
    ⟨V, fun Γ ρ => sourceGridUpgrade (r + 1) j ((old (.var x)).interp Γ ρ)
      (uniformUniverseDecode (r + 1) (typeSort (r + 2) Γ (.var x)) (V Γ ρ))⟩
  | .srt s =>
    let T Γ ρ := sourceGridUpgrade (r + 1) j ((old (.srt s)).interp Γ ρ) (FiniteGridType.sort (r + 1) s)
    ⟨fun Γ ρ => sourceGridForcedValue r j hj old Γ ρ (.srt s)
      (uniformUniverseEncode (r + 1) (typeSort (r + 2) Γ (.srt s)) (T Γ ρ) ⟨j, Nat.lt_succ_of_le hj⟩), T⟩
  | .app f a =>
    let mf := sourceGridStep r j hj old f
    let ma := sourceGridStep r j hj old a
    let V Γ ρ :=
      let p := chosenProduct (r + 2) Γ f
      sourceGridForcedValue r j hj old Γ ρ (.app f a)
        (finiteTypeApplication r ((old p.1).interp Γ ρ) ((old p.2).bodyFamily Γ ρ p.1)
          (mf.eval Γ ρ) (ma.eval Γ ρ) ⟨j, Nat.lt_succ_of_le hj⟩)
    ⟨V, fun Γ ρ => sourceGridUpgrade (r + 1) j ((old (.app f a)).interp Γ ρ)
      (uniformUniverseDecode (r + 1) (typeSort (r + 2) Γ (.app f a)) (V Γ ρ))⟩
  | .lam A b =>
    let mb := sourceGridStep r j hj old b
    ⟨fun Γ ρ =>
      let B := chosenType (r + 2) (A :: Γ) b
      sourceGridForcedValue r j hj old Γ ρ (.lam A b)
        (finiteTypeLambda r ((old A).interp Γ ρ) ((old B).bodyFamily Γ ρ A)
          (mb.bodyMap Γ ρ A) ⟨j, Nat.lt_succ_of_le hj⟩),
      fun Γ ρ => sourceGridUpgrade (r + 1) j ((old (.lam A b)).interp Γ ρ) (FiniteGridType.trivial (r + 1))⟩
  | .pi A B =>
    let mA := sourceGridStep r j hj old A
    let mB := sourceGridStep r j hj old B
    let T Γ ρ := sourceGridUpgrade (r + 1) j ((old (.pi A B)).interp Γ ρ)
      (finitePiType r (mA.interp Γ ρ) (mB.bodyFamily Γ ρ A))
    ⟨fun Γ ρ => sourceGridForcedValue r j hj old Γ ρ (.pi A B)
      (uniformUniverseEncode (r + 1) (typeSort (r + 2) Γ (.pi A B)) (T Γ ρ) ⟨j, Nat.lt_succ_of_le hj⟩), T⟩

theorem sourceGridStep_rawValue (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    ∃ v, (sourceGridStep r j hj old t).rawValue Γ ρ = sourceGridForcedValue r j hj old Γ ρ t v := by
  cases t <;> exact ⟨_, rfl⟩

theorem sourceGridStep_rawType (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    ∃ next, (sourceGridStep r j hj old t).rawType Γ ρ =
      sourceGridUpgrade (r + 1) j ((old t).interp Γ ρ) next := by
  cases t <;> exact ⟨_, rfl⟩

theorem sourceGridStep_eval_before (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    FiniteGridValue.Agree j ((sourceGridStep r j hj old t).eval Γ ρ) ((old t).eval Γ ρ) := by
  intro i hi
  change (sourceGridStep r j hj old t).rawValue Γ (GridEnvironment.truncate (i.val + 1) ρ) i = _
  obtain ⟨v, hv⟩ := sourceGridStep_rawValue r j hj old t Γ (GridEnvironment.truncate (i.val + 1) ρ)
  rw [hv]
  unfold sourceGridForcedValue
  rw [FiniteGridValue.set_other _ j i (by omega)]
  exact (old t).eval_causal Γ _ ρ i (GridEnvironment.truncate_below ρ (i.val + 1))

theorem sourceGridStep_interp_before (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (i : Nat) (hi : i ≤ r + 1) (hij : i ≤ j) (v : TowerFamily (carrierGrid (r + 1))) :
    ((sourceGridStep r j hj old t).interp Γ ρ).carrier.code i hi v = ((old t).interp Γ ρ).carrier.code i hi v := by
  change ((sourceGridStep r j hj old t).rawType Γ (GridEnvironment.truncate i ρ)).carrier.code i hi v = _
  obtain ⟨next, he⟩ := sourceGridStep_rawType r j hj old t Γ (GridEnvironment.truncate i ρ)
  rw [he, sourceGridUpgrade_before _ j _ next i hi hij]
  exact (old t).interp_causal Γ _ ρ i hi (GridEnvironment.truncate_below ρ i) v

/-- All stages exist for every finite row. This is a definition by coordinate
induction, with structural term recursion inside each successor stage. -/
noncomputable def sourceGridStages (r : Nat) : (d : Nat) → d ≤ r + 2 → Tm → SourceGridMeaning (r + 1)
  | 0, _ => sourceGridBase r
  | d + 1, hd => sourceGridStep r d (by omega) (sourceGridStages r d (by omega))

noncomputable def sourceGridMeaning (r : Nat) (t : Tm) : SourceGridMeaning (r + 1) :=
  sourceGridStages r (r + 2) (Nat.le_refl _) t

noncomputable def sourceGridEval (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (t : Tm) :
    FiniteGridValue (r + 1) := (sourceGridMeaning r t).eval Γ ρ

noncomputable def sourceGridInterpretation (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (t : Tm) :
    FiniteGridType (r + 1) := (sourceGridMeaning r t).interp Γ ρ

theorem sourceGridEval_causal (r : Nat) (Γ : List Tm) (ρ δ : GridEnvironment (r + 1)) (t : Tm)
    (i : Fin (r + 2)) (h : GridEnvironment.Agree (i.val + 1) ρ δ) :
    sourceGridEval r Γ ρ t i = sourceGridEval r Γ δ t i :=
  (sourceGridMeaning r t).eval_causal Γ ρ δ i h

theorem sourceGridInterpretation_causal (r : Nat) (Γ : List Tm) (ρ δ : GridEnvironment (r + 1)) (t : Tm)
    (i : Nat) (hi : i ≤ r + 1) (h : GridEnvironment.Agree i ρ δ) (v : TowerFamily (carrierGrid (r + 1))) :
    (sourceGridInterpretation r Γ ρ t).carrier.code i hi v =
      (sourceGridInterpretation r Γ δ t).carrier.code i hi v :=
  (sourceGridMeaning r t).interp_causal Γ ρ δ i hi h v

end Submission.Helpers
