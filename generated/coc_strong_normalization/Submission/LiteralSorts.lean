import Submission.UniverseMachine

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 2000000

noncomputable def UniversePrefix.shiftCandidateObject (P : UniversePrefix r (r + 1)) (k : Nat) :
    CarrierObject (carrierGrid (r + 1 + k) (r + 1 + k)) (P.El → Candidate) :=
  CarrierObject.map (carrierGridImageEmbedding (r + 1) (r + 1) k).representation P.candidateObject

theorem UniversePrefix.shiftCandidateObject_code (P : UniversePrefix r (r + 1)) (k : Nat) :
    (P.shiftCandidateObject k).code = (P.shiftObject (Nat.le_refl _) k).code := by
  unfold shiftCandidateObject shiftObject
  simp only [object, dif_neg (Nat.not_succ_le_self r), CarrierObject.map, CarrierObject.ofDataEq_code]

noncomputable def UniversePrefix.encodeCandidate (P : UniversePrefix r (r + 1)) (k : Nat)
    (C : P.El → Candidate) : TowerValue (carrierGrid (r + 1 + k) (r + 1 + k)) :=
  ⟨(P.shiftCandidateObject k).code, (P.shiftCandidateObject k).values.encode C⟩

noncomputable def UniversePrefix.decodeCandidate (P : UniversePrefix r (r + 1)) (k : Nat)
    (v : TowerValue (carrierGrid (r + 1 + k) (r + 1 + k))) : P.El → Candidate :=
  (P.shiftCandidateObject k).values.decode (v.cast (P.shiftCandidateObject k).code)

theorem UniversePrefix.decodeCandidate_encodeCandidate (P : UniversePrefix r (r + 1)) (k : Nat)
    (C : P.El → Candidate) : P.decodeCandidate k (P.encodeCandidate k C) = C := by
  unfold decodeCandidate encodeCandidate
  rw [TowerValue.cast_mk]
  exact (P.shiftCandidateObject k).roundtrip C

/-- The lower type represented by the literal sort `Type r`. Every field is
the uniform universe code evaluated on the preceding dependent arguments. -/
noncomputable def literalSortPrefix (r : Nat) : (d : Nat) → d ≤ r + 2 → UniversePrefix (r + 1) d
  | 0, _ => UniversePrefix.empty (r + 1)
  | d + 1, hd =>
    let P := literalSortPrefix r d (by omega)
    P.next (fun x => universeSortAt r 0 d (by omega)
      (P.telescope.sectionValues (fun i => CarrierRepresentation.identity (carrierGrid (r + 1) i)) x))

noncomputable def literalSortField (r d : Nat) (hd : d ≤ r + 1) :
    (literalSortPrefix r d (by omega)).El → (carrierGrid (r + 1) d).Code :=
  fun x => universeSortAt r 0 d hd
    ((literalSortPrefix r d (by omega)).telescope.sectionValues
      (fun i => CarrierRepresentation.identity (carrierGrid (r + 1) i)) x)

theorem literalSortPrefix_succ (r d : Nat) (hd : d ≤ r + 1) :
    literalSortPrefix r (d + 1) (by omega) = (literalSortPrefix r d (by omega)).next (literalSortField r d hd) := rfl

/-- Values of the literal sort are encoded in its declared next universe.
The final value stores the constant strong-normalization candidate. -/
noncomputable def literalSortValue (r k d : Nat) : TowerValue (carrierGrid (r + 2 + k) (d + k)) := by
  classical
  exact if hd : d ≤ r + 1 then
    (literalSortPrefix r d (by omega)).encodeCode hd k (literalSortField r d hd)
  else if he : d = r + 2 then
    gridValueCast rfl (congrArg (fun d => d + k) he.symm)
      ((literalSortPrefix r (r + 2) (Nat.le_refl _)).encodeCandidate k (fun _ => Candidate.sn))
  else ⟨(carrierGrid (r + 2 + k) (d + k)).defaultCode,
    (carrierGrid (r + 2 + k) (d + k)).point (carrierGrid (r + 2 + k) (d + k)).defaultCode⟩

theorem literalSortValue_proper (r k d : Nat) (hd : d ≤ r + 1) :
    literalSortValue r k d = (literalSortPrefix r d (by omega)).encodeCode hd k (literalSortField r d hd) := by
  unfold literalSortValue
  rw [dif_pos hd]

theorem literalSortValue_final (r k : Nat) :
    literalSortValue r k (r + 2) =
      (literalSortPrefix r (r + 2) (Nat.le_refl _)).encodeCandidate k (fun _ => Candidate.sn) := by
  unfold literalSortValue
  rw [dif_neg (show ¬r + 2 ≤ r + 1 by omega), dif_pos rfl]
  rfl

/-- Reconstructing the declared universe from these values recovers the
literal sort's prefix, uniformly through the candidate boundary. -/
theorem literalSortValue_prefix (r k d : Nat) (hd : d ≤ r + 2) :
    UniversePrefix.fromValues (r + 1) k d hd (literalSortValue r k) = literalSortPrefix r d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [UniversePrefix.fromValues, ih (by omega), literalSortValue_proper r k d (by omega),
      UniversePrefix.decodeCode_encodeCode]
    rfl

theorem literalSortValue_code (r k d : Nat) (hd : d ≤ r + 2) :
    (literalSortValue r k d).code = ((literalSortPrefix r d hd).shiftObject hd k).code := by
  by_cases hl : d ≤ r + 1
  · rw [literalSortValue_proper r k d hl]
    exact (literalSortPrefix r d hd).shiftCodeObject_code hl k
  · have he : d = r + 2 := by omega
    subst d
    rw [literalSortValue_final]
    exact (literalSortPrefix r (r + 2) hd).shiftCandidateObject_code k

/-- Insert the inactive leading coordinates required by a larger finite
source bound. Only the active coordinates are read by the declared universe. -/
noncomputable def literalSortFullValues (r k : Nat) : TowerFamily (carrierGrid (r + 2 + k)) :=
  fun j => if hj : k ≤ j then gridValueCast rfl (Nat.sub_add_cancel hj) (literalSortValue r k (j - k))
    else (TowerFamily.point (carrierGrid (r + 2 + k))) j

theorem gridValueCast_family (he : d' = d) (hj : d' + k = d + k)
    (f : (i : Nat) → TowerValue (carrierGrid R (i + k))) :
    gridValueCast rfl hj (f d') = f d := by
  cases he
  rfl

theorem literalSortFullValues_at (r k d : Nat) :
    literalSortFullValues r k (d + k) = literalSortValue r k d := by
  unfold literalSortFullValues
  rw [dif_pos (show k ≤ d + k by omega)]
  exact gridValueCast_family (by omega) _ (literalSortValue r k)

/-- The evaluated literal `Type r` has the carrier of its trusted declared
type `Type (r+1)`, at every active coordinate and every larger finite bound. -/
theorem literalSortFullValues_typed_code (r k d : Nat) (hd : d ≤ r + 2) :
    (literalSortFullValues r k (d + k)).code =
      uniformSortCode (r + 2 + k) (d + k) (by omega) (.type (r + 1)) (literalSortFullValues r k) := by
  rw [literalSortFullValues_at, uniformSortCode_at (r + 1) k d hd]
  unfold universeSortAt
  have hv : (fun i => literalSortFullValues r k (i + k)) = literalSortValue r k :=
    funext (literalSortFullValues_at r k)
  rw [hv, literalSortValue_prefix]
  exact literalSortValue_code r k d hd

theorem literalSortFullValues_candidate (r k : Nat) :
    (literalSortPrefix r (r + 2) (Nat.le_refl _)).decodeCandidate k
      (literalSortFullValues r k (r + 2 + k)) = fun _ => Candidate.sn := by
  rw [literalSortFullValues_at, literalSortValue_final, UniversePrefix.decodeCandidate_encodeCandidate]

end Submission.Helpers
