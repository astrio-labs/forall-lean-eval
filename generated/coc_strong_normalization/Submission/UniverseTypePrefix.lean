import Submission.UniverseArguments

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- Read a formed type's active carrier fields into lower-row codes. The
prefix is defined by coordinate recursion; formation is used only in proofs. -/
noncomputable def universeTypePrefix (r k : Nat) (C : CausalGridType (r + 1 + k)) :
    (d : Nat) → d ≤ r + 1 → UniversePrefix r d
  | 0, _ => UniversePrefix.empty r
  | d + 1, hd =>
    let P := universeTypePrefix r k C d (by omega)
    P.next (fun x => (universeOutputCodes r d k).decode
      (C.code (d + 1 + k) (by omega) (universeArgumentLift r k ((P.arguments k).encode x))))

noncomputable def universeTypeField (r k : Nat) (C : CausalGridType (r + 1 + k))
    (d : Nat) (hd : d ≤ r) :
    (universeTypePrefix r k C d (by omega)).El → (carrierGrid r d).Code :=
  fun x => (universeOutputCodes r d k).decode
    (C.code (d + 1 + k) (by omega)
      (universeArgumentLift r k (((universeTypePrefix r k C d (by omega)).arguments k).encode x)))

theorem universeTypePrefix_full (r k : Nat) (C : CausalGridType (r + 1 + k))
    (d : Nat) (hd : d ≤ r + 1) : (universeTypePrefix r k C d hd).Full := by
  induction d with
  | zero => exact UniversePrefix.full_empty r
  | succ d ih => exact (ih (by omega)).next _

theorem formedType_low_values (r k : Nat) (C : CausalGridType (r + 1 + k))
    (hC : C.Formed (.type r)) (d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1 + k))) (hv : C.Coherent (d + 1 + k) (by omega) v)
    (i : Nat) (hi : i ≤ k) : (v i).code = (carrierGrid (r + 1 + k) i).defaultCode :=
  (hv i (by omega)).trans ((hC i (by omega) v).lower (by simp only [sortRank]; omega))

/-- A coherent source carrier yields compatibility with its reconstructed
universe prefix. Both image membership and argument preservation are derived. -/
theorem universeTypePrefix_compatible (r k : Nat) (C : CausalGridType (r + 1 + k))
    (hC : C.Formed (.type r)) (d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1 + k))) (hv : C.Coherent (d + 1 + k) (by omega) v) :
    (universeTypePrefix r k C d hd).telescope.Compatible (universeArgumentRepresentation r k)
      (universeArgumentSlice r k v) := by
  induction d with
  | zero => trivial
  | succ d ih =>
    have hp := ih (by omega) (hv.mono (by omega))
    change ((universeTypePrefix r k C d (by omega)).telescope.snoc d
      (universeTypeField r k C d (by omega))).Compatible _ _
    erw [CarrierTelescope.compatible_snoc]
    refine ⟨hp, ?_⟩
    have hrec := (universeTypePrefix r k C d (by omega)).lift_arguments_recover
      (universeTypePrefix_full r k C d (by omega)) k v hp
      (formedType_low_values r k C hC (d + 1) hd v hv)
    have he := C.causal (d + 1 + k) (by omega) _ v hrec
    change (v (d + 1 + k)).code = (universeOutputCodes r d k).encode
      ((universeOutputCodes r d k).decode
        (C.code (d + 1 + k) (by omega)
          (universeArgumentLift r k
            (((universeTypePrefix r k C d (by omega)).arguments k).encode
              (((universeTypePrefix r k C d (by omega)).arguments k).decode (universeArgumentSlice r k v))))))
    rw [he]
    exact (hv (d + 1 + k) (by omega)).trans
      (universeOutputCodes_formed r d k _ (hC _ (by omega) v)).symm

/-- Reconstructing all active arguments preserves the exact prefix read by
the next carrier, including the complete input of the candidate boundary. -/
theorem universeTypePrefix_recover (r k : Nat) (C : CausalGridType (r + 1 + k))
    (hC : C.Formed (.type r)) (d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1 + k))) (hv : C.Coherent (d + 1 + k) (by omega) v) :
    TowerFamily.AgreeBelow (d + 1 + k)
      (universeArgumentLift r k
        (((universeTypePrefix r k C d hd).arguments k).encode
          (((universeTypePrefix r k C d hd).arguments k).decode (universeArgumentSlice r k v)))) v :=
  (universeTypePrefix r k C d hd).lift_arguments_recover (universeTypePrefix_full r k C d hd) k v
    (universeTypePrefix_compatible r k C hC d hd v hv) (formedType_low_values r k C hC d hd v hv)

end Submission.Helpers
