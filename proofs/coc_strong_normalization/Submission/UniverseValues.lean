import Submission.UniverseFamilies

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def UniversePrefix.shiftCodeObject (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat) :
    CarrierObject (carrierGrid (r + 1 + k) (d + k)) (P.El → (carrierGrid r d).Code) :=
  CarrierObject.map (carrierGridImageEmbedding (r + 1) d k).representation (P.codeObject hd)

noncomputable def UniversePrefix.encodeCode (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (C : P.El → (carrierGrid r d).Code) : TowerValue (carrierGrid (r + 1 + k) (d + k)) :=
  ⟨(P.shiftCodeObject hd k).code, (P.shiftCodeObject hd k).values.encode C⟩

noncomputable def UniversePrefix.decodeCode (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (v : TowerValue (carrierGrid (r + 1 + k) (d + k))) : P.El → (carrierGrid r d).Code :=
  (P.shiftCodeObject hd k).values.decode (v.cast (P.shiftCodeObject hd k).code)

theorem UniversePrefix.decodeCode_encodeCode (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (C : P.El → (carrierGrid r d).Code) : P.decodeCode hd k (P.encodeCode hd k C) = C := by
  unfold decodeCode encodeCode
  rw [TowerValue.cast_mk]
  exact (P.shiftCodeObject hd k).roundtrip C

theorem UniversePrefix.shiftCodeObject_code (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat) :
    (P.shiftCodeObject hd k).code = (P.shiftObject (Nat.le_trans hd (Nat.le_succ r)) k).code := by
  unfold shiftCodeObject shiftObject
  simp only [object, dif_pos hd, CarrierObject.map, CarrierObject.ofDataEq_code]

/-- Reconstructing the next lower-row type prefix reads only the preceding
universe values. Each recursive call decreases the coordinate. -/
noncomputable def UniversePrefix.fromValues (r k : Nat) :
    (d : Nat) → d ≤ r + 1 → TowerFamily (fun i => carrierGrid (r + 1 + k) (i + k)) → UniversePrefix r d
  | 0, _, _ => .empty r
  | d + 1, hd, v =>
    let P := UniversePrefix.fromValues r k d (by omega) v
    P.next (P.decodeCode (by omega) k (v d))

theorem UniversePrefix.fromValues_congr (r k d : Nat) (hd : d ≤ r + 1)
    (v w : TowerFamily (fun i => carrierGrid (r + 1 + k) (i + k)))
    (h : ∀ i, i < d → v i = w i) :
    UniversePrefix.fromValues r k d hd v = UniversePrefix.fromValues r k d hd w := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [fromValues, fromValues, ih (by omega) (fun i hi => h i (by omega)), h d (Nat.lt_succ_self d)]

/-- Extending a prefix with an encoded code family recovers that family
exactly, including the last lower-row code before the candidate boundary. -/
theorem UniversePrefix.fromValues_next (r k d : Nat) (hd : d ≤ r)
    (v : TowerFamily (fun i => carrierGrid (r + 1 + k) (i + k)))
    (C : (UniversePrefix.fromValues r k d (by omega) v).El → (carrierGrid r d).Code) :
    UniversePrefix.fromValues r k (d + 1) (by omega)
      (v.set d ((UniversePrefix.fromValues r k d (by omega) v).encodeCode hd k C)) =
      (UniversePrefix.fromValues r k d (by omega) v).next C := by
  rw [fromValues]
  have he : UniversePrefix.fromValues r k d (by omega)
      (v.set d ((UniversePrefix.fromValues r k d (by omega) v).encodeCode hd k C)) =
      UniversePrefix.fromValues r k d (by omega) v :=
    fromValues_congr r k d (by omega) _ _ (fun i hi => TowerFamily.set_other _ d i _ (by omega))
  rw [he, TowerFamily.set_same, decodeCode_encodeCode]

end Submission.Helpers
