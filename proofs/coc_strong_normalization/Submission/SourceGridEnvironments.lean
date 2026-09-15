import Submission.SourceGridSorts

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

def SourceGridContextPrefix (r : Nat) (Γ : List Tm) (τ : Nat → Tm) (d : Nat) (hd : d ≤ r + 2)
    (ρ : GridEnvironment (r + 1)) : Prop :=
  ∀ x, (sourceGridInterpretation r Γ ρ (τ x)).carrier.Coherent d hd (FiniteGridValue.toTower _ (ρ x))

noncomputable def sourceGridEnvironmentStep (r : Nat) (Γ : List Tm) (τ : Nat → Tm)
    (j : Nat) (hj : j ≤ r + 1) (ρ : GridEnvironment (r + 1)) : GridEnvironment (r + 1) :=
  fun x =>
    let C := (sourceGridInterpretation r Γ ρ (τ x)).carrier.code j hj (FiniteGridValue.toTower _ (ρ x))
    (ρ x).set j ⟨C, (carrierGrid (r + 1) j).point C⟩

theorem sourceGridEnvironmentStep_before (r : Nat) (Γ : List Tm) (τ : Nat → Tm)
    (j : Nat) (hj : j ≤ r + 1) (ρ : GridEnvironment (r + 1)) :
    GridEnvironment.Agree j ρ (sourceGridEnvironmentStep r Γ τ j hj ρ) :=
  fun x i hi => (FiniteGridValue.set_below (ρ x) j _ i hi).symm

theorem sourceGridEnvironmentStep_code (r : Nat) (Γ : List Tm) (τ : Nat → Tm)
    (j : Nat) (hj : j ≤ r + 1) (ρ : GridEnvironment (r + 1)) (x : Nat) :
    (sourceGridEnvironmentStep r Γ τ j hj ρ x ⟨j, Nat.lt_succ_of_le hj⟩).code =
      (sourceGridInterpretation r Γ ρ (τ x)).carrier.code j hj (FiniteGridValue.toTower _ (ρ x)) := by
  unfold sourceGridEnvironmentStep
  rw [FiniteGridValue.set_same]

theorem sourceGridEnvironmentStep_coherent (r : Nat) (Γ : List Tm) (τ : Nat → Tm)
    (j : Nat) (hj : j ≤ r + 1) (ρ : GridEnvironment (r + 1))
    (hρ : SourceGridContextPrefix r Γ τ j (by omega) ρ) :
    SourceGridContextPrefix r Γ τ (j + 1) (by omega) (sourceGridEnvironmentStep r Γ τ j hj ρ) := by
  let δ := sourceGridEnvironmentStep r Γ τ j hj ρ
  have he : GridEnvironment.Agree j ρ δ := sourceGridEnvironmentStep_before r Γ τ j hj ρ
  intro x i hi
  have hc : (FiniteGridValue.toTower _ (δ x) i).code =
      (sourceGridInterpretation r Γ ρ (τ x)).carrier.code i (by omega) (FiniteGridValue.toTower _ (ρ x)) := by
    by_cases hil : i < j
    · exact (congrArg TowerValue.code ((he x).toTower i hil).symm).trans (hρ x i hil)
    · have hei : i = j := by omega
      subst i
      rw [FiniteGridValue.toTower_at _ (δ x) ⟨j, by omega⟩]
      exact sourceGridEnvironmentStep_code r Γ τ j hj ρ x
  exact hc.trans
    (((sourceGridInterpretation r Γ ρ (τ x)).carrier.causal i (by omega) _ _
      ((he x).mono (by omega)).toTower).trans
      (sourceGridInterpretation_causal r Γ ρ δ (τ x) i (by omega) (he.mono (by omega)) _))

noncomputable def sourceGridEnvironmentStages (r : Nat) (Γ : List Tm) (τ : Nat → Tm) :
    (d : Nat) → d ≤ r + 2 → GridEnvironment (r + 1)
  | 0, _ => fun _ => FiniteGridValue.ofTower _ (TowerFamily.point (carrierGrid (r + 1)))
  | d + 1, hd => sourceGridEnvironmentStep r Γ τ d (by omega) (sourceGridEnvironmentStages r Γ τ d (by omega))

theorem sourceGridEnvironmentStages_coherent (r : Nat) (Γ : List Tm) (τ : Nat → Tm)
    (d : Nat) (hd : d ≤ r + 2) :
    SourceGridContextPrefix r Γ τ d hd (sourceGridEnvironmentStages r Γ τ d hd) := by
  induction d with
  | zero => intro x i hi; omega
  | succ d ih => exact sourceGridEnvironmentStep_coherent r Γ τ d (by omega) _ (ih (by omega))

/-- Even an arbitrary list of source declarations has a compatible semantic
environment. Values are built from carrier points in increasing coordinate
order, with no source normalization or typing hypothesis. -/
theorem sourceGridEnvironment_exists (r : Nat) (Γ : List Tm) (τ : Nat → Tm) :
    ∃ ρ : GridEnvironment (r + 1), ∀ x, (sourceGridInterpretation r Γ ρ (τ x)).Valid (ρ x) :=
  ⟨sourceGridEnvironmentStages r Γ τ (r + 2) (Nat.le_refl _),
    sourceGridEnvironmentStages_coherent r Γ τ (r + 2) (Nat.le_refl _)⟩

def SourceGridAdmissible (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) : Prop :=
  ∀ x, (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ (.var x))).Valid (ρ x)

theorem sourceGrid_admissible_exists (r : Nat) (Γ : List Tm) :
    ∃ ρ, SourceGridAdmissible r Γ ρ := sourceGridEnvironment_exists r Γ (fun x => chosenType (r + 2) Γ (.var x))

end Submission.Helpers
