import Submission.CoherentUniverseDecoding

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem CarrierTelescope.compatible_snoc {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (i : Nat) (A : T.El → (S i).Code) (v : TowerFamily V) :
    (T.snoc i A).Compatible R v ↔ T.Compatible R v ∧ (v i).code = (R i).code (A (T.project R v)) := by
  induction T with
  | nil => simp only [snoc, Compatible, project, and_true, true_and]
  | cons j B C ih => simp only [snoc, Compatible, project, ih, and_assoc]

theorem CarrierTelescope.compatible_set_below {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (h : T.Ordered lo hi) (v : TowerFamily V) (j : Nat) (hj : j < lo) (z : TowerValue (V j)) :
    T.Compatible R (v.set j z) ↔ T.Compatible R v := by
  induction T generalizing lo with
  | nil => rfl
  | cons i A B ih =>
    have hij : i ≠ j := by have hh := h.1; omega
    simp only [Compatible]
    erw [TowerFamily.set_other v j i z hij]
    exact and_congr_right (fun _ => ih _ (h.2.2 _) (by have hh := h.1; omega))

theorem CarrierTelescope.compatible_section {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (h : T.Ordered lo hi) (x : T.El) : T.Compatible R (T.sectionValues R x) := by
  induction T generalizing lo with
  | nil => trivial
  | cons i A B ih =>
    obtain ⟨x, y⟩ := x
    simp only [sectionValues, Compatible]
    erw [TowerFamily.set_same]
    refine ⟨rfl, ?_⟩
    erw [TowerValue.cast_mk, ((R i).values A).roundtrip]
    exact ((B x).compatible_set_below R (h.2.2 x) _ i (Nat.lt_succ_self i) _).mpr
      (ih x (h.2.2 x) y)

/-- A type carrier at coordinate `j` reads strictly earlier semantic values.
This is the dependency discipline of a source tower, independent of syntax. -/
structure CausalGridType (R : Nat) where
  code : (j : Nat) → j ≤ R → TowerFamily (carrierGrid R) → (carrierGrid R j).Code
  causal : ∀ j hj, TowerFamily.DependsBelow j (code j hj)

noncomputable def uniformSortType (R : Nat) (s : Srt) : CausalGridType R where
  code j hj := uniformSortCode R j hj s
  causal j hj := uniformSortCode_congr R j hj s

noncomputable def CausalGridType.telescopeAt (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1) :
    UniversePrefix R d := carrierFieldPrefix R A.code d hd

theorem CausalGridType.full (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1) :
    (A.telescopeAt d hd).Full := carrierFieldPrefix_full R A.code d hd

noncomputable def CausalGridType.arguments (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1) :
    CarrierRetraction (A.telescopeAt d hd).El (TowerFamily (carrierGrid R)) :=
  (A.telescopeAt d hd).telescope.valuesRetraction
    (fun i => CarrierRepresentation.identity (carrierGrid R i)) (A.telescopeAt d hd).ordered

def CausalGridType.Coherent (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) : Prop :=
  ∀ i (hi : i < d), (v i).code = A.code i (by omega) v

theorem CausalGridType.compatible_iff (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) :
    (A.telescopeAt d hd).telescope.Compatible (fun i => CarrierRepresentation.identity (carrierGrid R i)) v ↔
      A.Coherent d hd v := by
  induction d with
  | zero => exact ⟨fun _ i hi => by omega, fun _ => True.intro⟩
  | succ d ih =>
    change ((A.telescopeAt d (by omega)).telescope.snoc d
      (fun x => A.code d (by omega) ((A.arguments d (by omega)).encode x))).Compatible _ v ↔ _
    rw [CarrierTelescope.compatible_snoc]
    constructor
    · intro h
      have hp := (ih (by omega)).mp h.1
      have he : A.code d (by omega) ((A.arguments d (by omega)).encode ((A.arguments d (by omega)).decode v)) =
          A.code d (by omega) v := by
        apply A.causal
        intro i hi
        exact (A.telescopeAt d (by omega)).telescope.section_project_at _ (fun _ _ _ => rfl)
          (A.full d (by omega)) v h.1 i (Nat.zero_le _) hi
      intro i hi
      by_cases hid : i < d
      · exact hp i hid
      · have hid : i = d := by omega
        subst i
        exact h.2.trans he
    · intro h
      have hp := (ih (by omega)).mpr (fun i hi => h i (by omega))
      refine ⟨hp, ?_⟩
      have he : A.code d (by omega) ((A.arguments d (by omega)).encode ((A.arguments d (by omega)).decode v)) =
          A.code d (by omega) v := by
        apply A.causal
        intro i hi
        exact (A.telescopeAt d (by omega)).telescope.section_project_at _ (fun _ _ _ => rfl)
          (A.full d (by omega)) v hp i (Nat.zero_le _) hi
      exact (h d (Nat.lt_succ_self d)).trans he.symm

theorem CausalGridType.recover (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) (hv : A.Coherent d hd v) :
    TowerFamily.AgreeBelow d ((A.arguments d hd).encode ((A.arguments d hd).decode v)) v := by
  intro i hi
  exact (A.telescopeAt d hd).telescope.section_project_at _ (fun _ _ _ => rfl)
    (A.full d hd) v ((A.compatible_iff d hd v).mpr hv) i (Nat.zero_le _) hi

theorem CausalGridType.section_coherent (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (x : (A.telescopeAt d hd).El) : A.Coherent d hd ((A.arguments d hd).encode x) :=
  (A.compatible_iff d hd _).mp
    ((A.telescopeAt d hd).telescope.compatible_section _ (A.telescopeAt d hd).ordered x)

def CausalGridType.Formed (A : CausalGridType R) (s : Srt) : Prop :=
  ∀ j hj v, GridFormation R j s (A.code j hj v)

theorem uniformSortType_formed (R : Nat) (hAx : Ax s s') : (uniformSortType R s).Formed s' :=
  fun j hj v => uniformSortCode_formation R j hj hAx v

end Submission.Helpers
