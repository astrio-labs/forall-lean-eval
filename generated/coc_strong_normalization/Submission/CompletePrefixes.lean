import Submission.UniformLiterals

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- A complete telescope has exactly one entry at each coordinate in its
interval. This strengthens ordering without imposing any typing premise. -/
def CarrierTelescope.Complete {S : Nat → CarrierSystem} (lo hi : Nat) : CarrierTelescope S → Prop
  | .nil => lo = hi
  | .cons i _ B => i = lo ∧ lo < hi ∧ ∀ x, (B x).Complete (lo + 1) hi

theorem CarrierTelescope.Complete.ordered {S : Nat → CarrierSystem} {T : CarrierTelescope S}
    (h : T.Complete lo hi) : T.Ordered lo hi := by
  induction T generalizing lo with
  | nil => trivial
  | cons i A B ih =>
    obtain ⟨he, hh, hB⟩ := h
    subst lo
    exact ⟨Nat.le_refl _, hh, fun x => ih x (hB x)⟩

theorem CarrierTelescope.Complete.snoc {S : Nat → CarrierSystem} {T : CarrierTelescope S}
    (h : T.Complete lo hi) (A : T.El → (S hi).Code) :
    (T.snoc hi A).Complete lo (hi + 1) := by
  induction T generalizing lo with
  | nil =>
    change lo = hi at h
    subst lo
    exact ⟨rfl, Nat.lt_succ_self _, fun _ => rfl⟩
  | cons i B C ih =>
    exact ⟨h.1, by have hh := h.2.1; omega, fun x => ih x (h.2.2 x) _⟩

def UniversePrefix.Full (P : UniversePrefix r d) : Prop := P.telescope.Complete 0 d

theorem UniversePrefix.full_empty (r : Nat) : (UniversePrefix.empty r).Full := rfl

theorem UniversePrefix.Full.next {P : UniversePrefix r d} (h : P.Full)
    (A : P.El → (carrierGrid r d).Code) : (P.next A).Full := h.snoc A

theorem UniversePrefix.fromValues_full (r k d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (fun i => carrierGrid (r + 1 + k) (i + k))) :
    (UniversePrefix.fromValues r k d hd v).Full := by
  induction d with
  | zero => exact full_empty r
  | succ d ih => exact (ih (by omega)).next _

theorem carrierFieldPrefix_full (r : Nat)
    (C : (d : Nat) → d ≤ r → TowerFamily (carrierGrid r) → (carrierGrid r d).Code)
    (d : Nat) (hd : d ≤ r + 1) : (carrierFieldPrefix r C d hd).Full := by
  induction d with
  | zero => exact UniversePrefix.full_empty r
  | succ d ih => exact (ih (by omega)).next _

/-- Compatibility checks codes at every dependent entry, using the same
projection that supplies the next entry's parameters. -/
noncomputable def CarrierTelescope.Compatible {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) : CarrierTelescope S → TowerFamily V → Prop
  | .nil, _ => True
  | .cons i A B, v =>
    (v i).code = (R i).code A ∧
      (B (((R i).values A).decode ((v i).cast ((R i).code A)))).Compatible R v

theorem CarrierRepresentation.recover_value (R : CarrierRepresentation S V) (A : S.Code)
    (hR : ∀ x, (R.values A).encode ((R.values A).decode x) = x)
    (v : TowerValue V) (hv : v.code = R.code A) :
    (TowerValue.mk (R.code A) ((R.values A).encode ((R.values A).decode (v.cast (R.code A))))) = v := by
  rw [hR]
  exact v.mk_cast hv

/-- On a complete prefix, code compatibility suffices to recover every
retained value whenever the component representations have both roundtrips. -/
theorem CarrierTelescope.section_project_at {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i))
    (hR : ∀ i A x, ((R i).values A).encode (((R i).values A).decode x) = x)
    (T : CarrierTelescope S) (hT : T.Complete lo hi) (v : TowerFamily V)
    (hv : T.Compatible R v) (j : Nat) (hlo : lo ≤ j) (hhi : j < hi) :
    T.sectionValues R (T.project R v) j = v j := by
  induction T generalizing lo with
  | nil => change lo = hi at hT; omega
  | cons i A B ih =>
    let x := ((R i).values A).decode ((v i).cast ((R i).code A))
    change ((B x).sectionValues R ((B x).project R v)).set i
      ⟨(R i).code A, ((R i).values A).encode x⟩ j = v j
    by_cases hj : j = i
    · subst j
      rw [TowerFamily.set_same]
      exact (R i).recover_value A (hR i A) (v i) hv.1
    · rw [TowerFamily.set_other _ i j _ hj]
      exact ih x (hT.2.2 x) hv.2 (by have he := hT.1; omega)

theorem universeOutputValues_reverse (r d k : Nat) (A : (carrierGrid r d).Code)
    (x : (carrierGrid (r + 1 + k) (d + 1 + k)).El ((universeOutputCodes r d k).encode A)) :
    (universeOutputValues r d k A).encode ((universeOutputValues r d k A).decode x) = x := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih x

/-- Unlike a general retraction, the diagonal universe argument embedding
loses no data at a compatible code. -/
theorem UniversePrefix.arguments_recover (P : UniversePrefix r d) (hP : P.Full) (k : Nat)
    (v : TowerFamily (universeArgumentSystems r k))
    (hv : P.telescope.Compatible (universeArgumentRepresentation r k) v)
    (i : Nat) (hi : i < d) :
    (P.arguments k).encode ((P.arguments k).decode v) i = v i :=
  P.telescope.section_project_at (universeArgumentRepresentation r k)
    (fun i A x => universeOutputValues_reverse r i k A x) hP v hv i (Nat.zero_le _) hi

end Submission.Helpers
