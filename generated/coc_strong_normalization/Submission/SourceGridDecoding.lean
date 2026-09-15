import Submission.CoherentLambdaConversion

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem uniformUniverseDecode_causal (R : Nat) (s : Option Srt)
    (u w : FiniteGridValue R) (j : Nat) (hj : j ≤ R)
    (h : FiniteGridValue.Agree j u w) (v : TowerFamily (carrierGrid R)) :
    (uniformUniverseDecode R s u).carrier.code j hj v =
      (uniformUniverseDecode R s w).carrier.code j hj v := by
  cases s with
  | none => rfl
  | some s =>
    cases s with
    | prop => rfl
    | type i =>
      by_cases hi : i + 1 ≤ R
      · obtain ⟨k, he⟩ : ∃ k, R = i + 1 + k := ⟨R - (i + 1), by omega⟩
        subst R
        rw [uniformUniverseDecode_at, uniformUniverseDecode_at]
        exact decodedUniverseCarrier_stored_congr i k u w j hj h.toTower v
      · unfold uniformUniverseDecode
        dsimp only
        rw [dif_neg hi, dif_neg hi]

theorem uniformUniverseDecode_zero (R : Nat) (s : Option Srt) (u : FiniteGridValue R)
    (v : TowerFamily (carrierGrid R)) :
    (uniformUniverseDecode R s u).carrier.code 0 (Nat.zero_le _) v =
      (carrierGrid R 0).defaultCode := by
  cases s with
  | none => rfl
  | some s =>
    cases s with
    | prop => rfl
    | type i =>
      by_cases hi : i + 1 ≤ R
      · obtain ⟨k, he⟩ : ∃ k, R = i + 1 + k := ⟨R - (i + 1), by omega⟩
        subst R
        rw [uniformUniverseDecode_at]
        exact decodedUniverseCarrier_low i k u 0 (by omega) (Nat.zero_le _) v
      · unfold uniformUniverseDecode
        dsimp only
        rw [dif_neg hi]
        rfl

theorem GridEnvironment.truncate_full (ρ : GridEnvironment R) :
    GridEnvironment.truncate (R + 1) ρ = ρ :=
  funext (fun x => FiniteGridValue.truncate_full (ρ x) _ (Nat.le_refl _))

theorem sourceGridStep_raw_eval (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (Γ : List Tm)
    (ρ : GridEnvironment (r + 1)) :
    FiniteGridValue.Agree (j + 1)
      ((sourceGridStep r j hj old t).rawValue Γ (GridEnvironment.truncate (j + 1) ρ))
      ((sourceGridStep r j hj old t).eval Γ ρ) := by
  intro i hi
  by_cases hij : i.val = j
  · have he : i = ⟨j, Nat.lt_succ_of_le hj⟩ := Fin.ext hij
    subst i
    rfl
  · obtain ⟨v, hv⟩ := sourceGridStep_rawValue r j hj old t Γ (GridEnvironment.truncate (j + 1) ρ)
    rw [hv]
    unfold sourceGridForcedValue
    rw [FiniteGridValue.set_other _ j i hij]
    exact ((old t).eval_causal Γ _ ρ i
      ((GridEnvironment.truncate_below ρ (j + 1)).mono (by omega))).trans
        (sourceGridStep_eval_before r j hj old t Γ ρ i (by omega)).symm

def SourceGridDecodedTerm (t : Tm) : Prop :=
  (∃ x, t = .var x) ∨ ∃ f a, t = .app f a

theorem sourceGridStep_decode_raw (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1)) (t : Tm) (ht : SourceGridDecodedTerm t)
    (Γ : List Tm) (ρ : GridEnvironment (r + 1)) :
    (sourceGridStep r j hj old t).rawType Γ ρ =
      sourceGridUpgrade (r + 1) j ((old t).interp Γ ρ)
        (uniformUniverseDecode (r + 1) (typeSort (r + 2) Γ t)
          ((sourceGridStep r j hj old t).rawValue Γ ρ)) := by
  rcases ht with ⟨x, rfl⟩ | ⟨f, a, rfl⟩ <;> rfl

/-- For variables and applications, the source carrier is the universe
decoder applied to the complete source value, at every finite row. -/
theorem sourceGridInterpretation_decode_carrier (r : Nat) (Γ : List Tm)
    (ρ : GridEnvironment (r + 1)) (t : Tm) (ht : SourceGridDecodedTerm t)
    (j : Nat) (hj : j ≤ r + 1) (v : TowerFamily (carrierGrid (r + 1))) :
    (sourceGridInterpretation r Γ ρ t).carrier.code j hj v =
      (uniformUniverseDecode (r + 1) (typeSort (r + 2) Γ t)
        (sourceGridEval r Γ ρ t)).carrier.code j hj v := by
  cases j with
  | zero =>
    rw [sourceGridInterpretation_zero, uniformUniverseDecode_zero]
    rcases ht with ⟨x, rfl⟩ | ⟨f, a, rfl⟩ <;> rfl
  | succ j =>
    let old := sourceGridStages r j (by omega)
    let M := sourceGridStep r j (by omega) old t
    have he := sourceGridStages_interp_before r (r + 2) (Nat.le_refl _) (j + 1)
      (by omega) t Γ ρ (j + 1) hj (Nat.le_refl _) v
    refine he.trans ?_
    change (M.rawType Γ (GridEnvironment.truncate (j + 1) ρ)).carrier.code (j + 1) hj v = _
    rw [sourceGridStep_decode_raw r j (by omega) old t ht]
    change (if j + 1 = j + 1 then _ else _) = _
    rw [if_pos rfl]
    apply uniformUniverseDecode_causal
    intro i hi
    exact (sourceGridStep_raw_eval r j (by omega) old t Γ ρ i hi).trans
      (sourceGridStages_eval_before r (r + 2) (Nat.le_refl _) (j + 1) (by omega) t Γ ρ i hi).symm

theorem sourceGridInterpretation_decode_candidate (r : Nat) (Γ : List Tm)
    (ρ : GridEnvironment (r + 1)) (t : Tm) (ht : SourceGridDecodedTerm t)
    (v : FiniteGridValue (r + 1)) :
    (sourceGridInterpretation r Γ ρ t).candidate v =
      (uniformUniverseDecode (r + 1) (typeSort (r + 2) Γ t)
        (sourceGridEval r Γ ρ t)).candidate v := by
  let old := sourceGridStages r (r + 1) (by omega)
  let M := sourceGridStep r (r + 1) (Nat.le_refl _) old t
  have he : M.rawValue Γ ρ = sourceGridEval r Γ ρ t := by
    funext i
    have hh := sourceGridStep_raw_eval r (r + 1) (Nat.le_refl _) old t Γ ρ i i.isLt
    rw [GridEnvironment.truncate_full] at hh
    exact hh
  change (M.rawType Γ ρ).candidate v = _
  rw [sourceGridStep_decode_raw r (r + 1) (Nat.le_refl _) old t ht]
  change ((if r + 1 = r + 1 then _ else _) : FiniteGridValue (r + 1) → Candidate) v = _
  rw [if_pos rfl, he]

theorem sourceGridInterpretation_decode (r : Nat) (Γ : List Tm)
    (ρ : GridEnvironment (r + 1)) (t : Tm) (ht : SourceGridDecodedTerm t) :
    sourceGridInterpretation r Γ ρ t =
      uniformUniverseDecode (r + 1) (typeSort (r + 2) Γ t) (sourceGridEval r Γ ρ t) := by
  apply FiniteGridType.ext_fields
  · exact sourceGridInterpretation_decode_carrier r Γ ρ t ht
  · exact sourceGridInterpretation_decode_candidate r Γ ρ t ht

theorem sourceGridInterpretation_var (r : Nat) (Γ : List Tm)
    (ρ : GridEnvironment (r + 1)) (hρ : SourceGridAdmissible r Γ ρ) (x : Nat) :
    sourceGridInterpretation r Γ ρ (.var x) =
      uniformUniverseDecode (r + 1) (typeSort (r + 2) Γ (.var x)) (ρ x) := by
  rw [sourceGridInterpretation_decode r Γ ρ (.var x) (Or.inl ⟨x, rfl⟩),
    sourceGridEval_variable r Γ ρ hρ x]

end Submission.Helpers
