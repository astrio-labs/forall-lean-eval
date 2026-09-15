import Submission.UniverseInterpretation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

abbrev TowerFamily (S : Nat → CarrierSystem) := (i : Nat) → TowerValue (S i)

def TowerFamily.point (S : Nat → CarrierSystem) : TowerFamily S :=
  fun i => ⟨(S i).defaultCode, (S i).point (S i).defaultCode⟩

def TowerFamily.set {S : Nat → CarrierSystem} (v : TowerFamily S) (i : Nat) (x : TowerValue (S i)) :
    TowerFamily S := fun j => if h : j = i then h.symm ▸ x else v j

theorem TowerFamily.set_same {S : Nat → CarrierSystem} (v : TowerFamily S) (i : Nat)
    (x : TowerValue (S i)) : v.set i x i = x := by simp [set]

theorem TowerFamily.set_other {S : Nat → CarrierSystem} (v : TowerFamily S) (i j : Nat)
    (x : TowerValue (S i)) (h : j ≠ i) : v.set i x j = v j := by simp only [set, dif_neg h]

/-- Projection reads each dependent argument through its exact carrier
representation. Codes are checked by `cast` before data are decoded. -/
noncomputable def CarrierTelescope.project {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) :
    (T : CarrierTelescope S) → TowerFamily V → T.El
  | .nil, _ => ()
  | .cons i A B, v =>
    let x := ((R i).values A).decode ((v i).cast ((R i).code A))
    ⟨x, (B x).project R v⟩

/-- The section fills unused coordinates with points. Increasing coordinate
order is used in the roundtrip theorem, not assumed by this definition. -/
noncomputable def CarrierTelescope.sectionValues {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) :
    (T : CarrierTelescope S) → T.El → TowerFamily V
  | .nil, _ => TowerFamily.point V
  | .cons i A B, x =>
    ((B x.1).sectionValues R x.2).set i ⟨(R i).code A, ((R i).values A).encode x.1⟩

theorem CarrierTelescope.project_set_below {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (h : T.Ordered lo hi) (v : TowerFamily V) (j : Nat) (hj : j < lo) (z : TowerValue (V j)) :
    T.project R (v.set j z) = T.project R v := by
  induction T generalizing lo with
  | nil => rfl
  | cons i A B ih =>
    have hji : i ≠ j := by have hh := h.1; omega
    simp only [project]
    erw [TowerFamily.set_other v j i z hji]
    let x := ((R i).values A).decode ((v i).cast ((R i).code A))
    exact congrArg (fun y : (B x).El => (⟨x, y⟩ : (a : (S i).El A) × (B a).El))
      (ih x (h.2.2 x) (by have hh := h.1; omega))

theorem CarrierTelescope.project_section {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (h : T.Ordered lo hi) (x : T.El) : T.project R (T.sectionValues R x) = x := by
  induction T generalizing lo with
  | nil => cases x; rfl
  | cons i A B ih =>
    obtain ⟨x, y⟩ := x
    simp only [sectionValues, project]
    erw [TowerFamily.set_same, TowerValue.cast_mk, ((R i).values A).roundtrip]
    erw [CarrierTelescope.project_set_below R (B x) (h.2.2 x) _ i (Nat.lt_succ_self i)]
    exact congrArg (fun y : (B x).El => (⟨x, y⟩ : (a : (S i).El A) × (B a).El)) (ih x (h.2.2 x) y)

noncomputable def CarrierTelescope.valuesRetraction {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (h : T.Ordered lo hi) : CarrierRetraction T.El (TowerFamily V) :=
  ⟨T.sectionValues R, T.project R, T.project_section R h⟩

end Submission.Helpers
