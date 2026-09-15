import Submission.SourceOperationalLambda

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem FiniteGridType.reify_coordinate_congr (r k : Nat) (A B : FiniteGridType (r + 1 + k))
    (j : Nat) (hj : j < r + 1 + k)
    (hC : CausalGridType.Agree (j + 2) A.carrier B.carrier) :
    A.reify r k ⟨j, by omega⟩ = B.reify r k ⟨j, by omega⟩ := by
  change universeReifyValues r k A.carrier _ j = universeReifyValues r k B.carrier _ j
  by_cases hk : k ≤ j
  · obtain ⟨d, he⟩ : ∃ d, j = d + k := ⟨j - k, by omega⟩
    subst j
    rw [universeReifyValues_at, universeReifyValues_at]
    apply universeReify_proper_congr r k _ _ _ _ d (by omega)
    intro i hi hil
    exact hC i hi (by omega)
  · unfold universeReifyValues
    rw [dif_neg hk, dif_neg hk]

/-- At coordinate j, universe introduction reads carrier fields through
j+1; only the final coordinate reads the candidate function. -/
theorem uniformUniverseEncode_coordinate_congr (R : Nat) (s : Option Srt)
    (A B : FiniteGridType R) (j : Nat) (hj : j ≤ R)
    (hC : CausalGridType.Agree (j + 2) A.carrier B.carrier)
    (hJ : j = R → A.candidate = B.candidate) :
    uniformUniverseEncode R s A ⟨j, Nat.lt_succ_of_le hj⟩ =
      uniformUniverseEncode R s B ⟨j, Nat.lt_succ_of_le hj⟩ := by
  by_cases he : j = R
  · have hAB : A = B := FiniteGridType.ext_fields A B
      (fun i hi v => congrFun (hC i hi (by omega)) v) (fun v => congrFun (hJ he) v)
    rw [hAB]
  · cases s with
    | none => rfl
    | some s =>
      cases s with
      | prop =>
        change propReifyValues R _ j = propReifyValues R _ j
        unfold propReifyValues
        rw [dif_neg he, dif_neg he]
      | type i =>
        by_cases hi : i + 1 ≤ R
        · obtain ⟨k, hR⟩ : ∃ k, R = i + 1 + k := ⟨R - (i + 1), by omega⟩
          subst R
          rw [uniformUniverseEncode_at, uniformUniverseEncode_at]
          exact FiniteGridType.reify_coordinate_congr i k A B j (by omega) hC
        · unfold uniformUniverseEncode
          dsimp only
          rw [dif_neg hi, dif_neg hi]

theorem sourceGridStep_rawType_complete (r j : Nat) (hj : j ≤ r + 1)
    (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (t : Tm) :
    CausalGridType.Agree (j + 2)
      ((sourceGridStep r j hj (sourceGridStages r j (by omega)) t).rawType
        Γ (GridEnvironment.truncate (j + 1) ρ)).carrier
      (sourceGridInterpretation r Γ ρ t).carrier := by
  intro i hi hij
  funext v
  by_cases he : i = j + 1
  · subst i
    exact (sourceGridStages_interp_before r (r + 2) (Nat.le_refl _) (j + 1) (by omega)
      t Γ ρ (j + 1) hi (Nat.le_refl _) v).symm
  · obtain ⟨next, hn⟩ := sourceGridStep_rawType r j hj (sourceGridStages r j (by omega))
      t Γ (GridEnvironment.truncate (j + 1) ρ)
    rw [hn, sourceGridUpgrade_before _ j _ next i hi (by omega)]
    exact congrFun (sourceGridStages_interp_agree r j (by omega) t Γ _ ρ
      ((GridEnvironment.truncate_below ρ (j + 1)).mono (by omega)) i hi (by omega)) v

theorem sourceGridStep_rawCandidate_complete (r : Nat) (Γ : List Tm)
    (ρ : GridEnvironment (r + 1)) (t : Tm) :
    ((sourceGridStep r (r + 1) (Nat.le_refl _) (sourceGridStages r (r + 1) (by omega)) t).rawType
      Γ (GridEnvironment.truncate (r + 2) ρ)).candidate =
      (sourceGridInterpretation r Γ ρ t).candidate := by
  rw [GridEnvironment.truncate_full]
  rfl

def SourceGridEncodedTerm (t : Tm) : Prop :=
  (∃ s, t = .srt s) ∨ ∃ A B, t = .pi A B

theorem sourceGridStep_encode_raw (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (ht : SourceGridEncodedTerm t)
    (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    (sourceGridStep r j hj old t).rawValue Γ ρ = sourceGridForcedValue r j hj old Γ ρ t
      (uniformUniverseEncode (r + 1) (typeSort (r + 2) Γ t)
        ((sourceGridStep r j hj old t).rawType Γ ρ) ⟨j, Nat.lt_succ_of_le hj⟩) := by
  rcases ht with ⟨s, rfl⟩ | ⟨A, B, rfl⟩ <;> rfl

theorem sourceGridEval_encode_coordinate (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (t : Tm) (ht : SourceGridEncodedTerm t) (i : Fin (r + 2)) :
    sourceGridEval r Γ ρ t i =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)).forceCoordinate
        (sourceGridEval r Γ ρ t) i
        (uniformUniverseEncode (r + 1) (typeSort (r + 2) Γ t) (sourceGridInterpretation r Γ ρ t) i) := by
  obtain ⟨j, hj⟩ := i
  rw [sourceGridEval_current r Γ ρ t j (by omega), sourceGridStep_encode_raw r j (by omega) _ t ht]
  unfold sourceGridForcedValue
  rw [FiniteGridValue.set_same]
  rw [uniformUniverseEncode_coordinate_congr (r + 1) _ _ (sourceGridInterpretation r Γ ρ t) j (by omega)
    (sourceGridStep_rawType_complete r j (by omega) Γ ρ t)
    (fun he => by subst j; exact sourceGridStep_rawCandidate_complete r Γ ρ t)]
  rw [sourceGridInferred_complete r j (by omega) Γ _ ρ
    ((GridEnvironment.truncate_below ρ (j + 1)).mono (by omega))]
  rfl

theorem sourceGridEval_encode_normalize (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (t : Tm) (ht : SourceGridEncodedTerm t) : sourceGridEval r Γ ρ t =
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)).normalizeValue
        (uniformUniverseEncode (r + 1) (typeSort (r + 2) Γ t) (sourceGridInterpretation r Γ ρ t)) :=
  ((sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)).normalizeValue_of_coordinates
    _ _ (sourceGridEval_encode_coordinate r Γ ρ t ht)).symm

end Submission.Helpers
