import Submission.UniverseReifierCausality

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- Conversely, compatibility with a reconstructed universe telescope gives
the original carrier equations, when the leading coordinates are terminal. -/
theorem universeTypePrefix_coherent (r k : Nat) (C : CausalGridType (r + 1 + k))
    (hC : C.Formed (.type r)) (d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1 + k)))
    (hlow : ∀ i, i ≤ k → (v i).code = (carrierGrid (r + 1 + k) i).defaultCode)
    (hv : (universeTypePrefix r k C d hd).telescope.Compatible
      (universeArgumentRepresentation r k) (universeArgumentSlice r k v)) :
    C.Coherent (d + 1 + k) (by omega) v := by
  induction d with
  | zero =>
    intro i hi
    exact (hlow i (by omega)).trans ((hC i (by omega) v).lower (by simp only [sortRank]; omega)).symm
  | succ d ih =>
    change ((universeTypePrefix r k C d (by omega)).telescope.snoc d
      (universeTypeField r k C d (by omega))).Compatible _ _ at hv
    erw [CarrierTelescope.compatible_snoc] at hv
    have hp := ih (by omega) hv.1
    have hrec := (universeTypePrefix r k C d (by omega)).lift_arguments_recover
      (universeTypePrefix_full r k C d (by omega)) k v hv.1 hlow
    have he := C.causal (d + 1 + k) (by omega) _ v hrec
    have hc := hv.2
    change (v (d + 1 + k)).code = (universeOutputCodes r d k).encode
      ((universeOutputCodes r d k).decode
        (C.code (d + 1 + k) (by omega)
          (universeArgumentLift r k
            (((universeTypePrefix r k C d (by omega)).arguments k).encode
              (((universeTypePrefix r k C d (by omega)).arguments k).decode (universeArgumentSlice r k v)))))) at hc
    rw [he, universeOutputCodes_formed r d k _ (hC _ (by omega) v)] at hc
    intro i hi
    by_cases hil : i < d + 1 + k
    · exact hp i hil
    · have hei : i = d + 1 + k := by omega
      subst i
      exact hc

theorem universeArgumentSlice_lift (r k : Nat) (v : TowerFamily (universeArgumentSystems r k)) :
    universeArgumentSlice r k (universeArgumentLift r k v) = v := by
  funext i
  exact universeArgumentLift_at r k i v

/-- Every argument used to encode a universe field is a coherent prefix of
the original formed type. This also holds at the final candidate boundary. -/
theorem universeTypePrefix_section_coherent (r k : Nat) (C : CausalGridType (r + 1 + k))
    (hC : C.Formed (.type r)) (d : Nat) (hd : d ≤ r + 1)
    (x : (universeTypePrefix r k C d hd).El) :
    C.Coherent (d + 1 + k) (by omega)
      (universeArgumentLift r k (((universeTypePrefix r k C d hd).arguments k).encode x)) := by
  apply universeTypePrefix_coherent r k C hC d hd
  · intro i hi
    rw [universeArgumentLift_low r k i hi]
    rfl
  · rw [universeArgumentSlice_lift]
    exact (universeTypePrefix r k C d hd).telescope.compatible_section
      (universeArgumentRepresentation r k) (universeTypePrefix r k C d hd).ordered x

end Submission.Helpers
