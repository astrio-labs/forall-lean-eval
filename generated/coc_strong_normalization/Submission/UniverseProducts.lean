import Submission.LiteralSorts

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def UniversePrefix.storeCodeFamily (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (C : TowerFamily (universeArgumentSystems r k) → (carrierGrid (r + 1 + k) (d + 1 + k)).Code) :
    TowerValue (carrierGrid (r + 1 + k) (d + k)) :=
  P.encodeCode hd k (familyEncode (P.arguments k) (universeOutputCodes r d k) C)

noncomputable def UniversePrefix.readCodeFamily (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (v : TowerValue (carrierGrid (r + 1 + k) (d + k))) :
    TowerFamily (universeArgumentSystems r k) → (carrierGrid (r + 1 + k) (d + 1 + k)).Code :=
  familyDecode (P.arguments k) (universeOutputCodes r d k) (P.decodeCode hd k v)

/-- The precise image and argument-dependence conditions for storing a type
family in the preceding universe value. -/
theorem UniversePrefix.read_store_iff (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (C : TowerFamily (universeArgumentSystems r k) → (carrierGrid (r + 1 + k) (d + 1 + k)).Code) :
    P.readCodeFamily hd k (P.storeCodeFamily hd k C) = C ↔
      FamilyAdmissible (P.arguments k) (universeOutputCodes r d k) C := by
  unfold readCodeFamily storeCodeFamily
  rw [decodeCode_encodeCode]
  exact family_decode_encode_iff _ _ C

theorem UniversePrefix.read_store_formed (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (C : TowerFamily (universeArgumentSystems r k) → (carrierGrid (r + 1 + k) (d + 1 + k)).Code)
    (hform : ∀ v, GridFormation (r + 1 + k) (d + 1 + k) (.type r) (C v))
    (hcanonical : ∀ v, C ((P.arguments k).encode ((P.arguments k).decode v)) = C v) :
    P.readCodeFamily hd k (P.storeCodeFamily hd k C) = C :=
  (P.read_store_iff hd k C).mpr ⟨fun v => universeOutputCodes_formed r d k (C v) (hform v), hcanonical⟩

/-- A family depending directly on the retained dependent arguments has
the required canonicality by construction. -/
theorem UniversePrefix.read_store_projected (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (C : P.El → (carrierGrid (r + 1 + k) (d + 1 + k)).Code)
    (hform : ∀ x, GridFormation (r + 1 + k) (d + 1 + k) (.type r) (C x)) :
    P.readCodeFamily hd k (P.storeCodeFamily hd k (fun v => C ((P.arguments k).decode v))) =
      fun v => C ((P.arguments k).decode v) := by
  apply P.read_store_formed hd k _ (fun v => hform _)
  intro v
  rw [(P.arguments k).roundtrip]

noncomputable def universeProductCode (r d k : Nat) (hd : d ≤ r)
    (T : CarrierTelescope (carrierGrid (r + k + 1))) (hw : T.Within (d + k))
    (D B : T.El → (carrierGrid (r + k + 1) (d + k + 1)).Code) :
    (carrierGrid (r + 1 + k) (d + 1 + k)).Code :=
  gridCodeCast (by omega) (by omega) (carrierGridBinderCode (r + k) (d + k) (by omega) T hw D B)

theorem universeProductCode_formation (r d k : Nat) (hd : d ≤ r)
    (T : CarrierTelescope (carrierGrid (r + k + 1))) (hw : T.Within (d + k))
    (D B : T.El → (carrierGrid (r + k + 1) (d + k + 1)).Code)
    (hr : Rl sA sB (.type r)) (hT : T.GridForm (r + k + 1) sA)
    (hD : ∀ x, GridFormation (r + k + 1) (d + k + 1) sA (D x))
    (hB : ∀ x, GridFormation (r + k + 1) (d + k + 1) sB (B x)) :
    GridFormation (r + 1 + k) (d + 1 + k) (.type r) (universeProductCode r d k hd T hw D B) :=
  (carrierGridBinderCode_formation (r + k) (d + k) (by omega) T hw D B hr hT hD hB).cast
    (by omega) (by omega)

/-- Predicative products over arbitrary finite semantic telescopes can be
stored in, and recovered from, the preceding universe value at every depth.
All formation premises are the original product rule's premises. -/
theorem UniversePrefix.read_store_products (P : UniversePrefix r d) (hd : d ≤ r) (k : Nat)
    (T : P.El → CarrierTelescope (carrierGrid (r + k + 1)))
    (hw : ∀ x, (T x).Within (d + k))
    (D B : (x : P.El) → (T x).El → (carrierGrid (r + k + 1) (d + k + 1)).Code)
    (hr : Rl sA sB (.type r)) (hT : ∀ x, (T x).GridForm (r + k + 1) sA)
    (hD : ∀ x y, GridFormation (r + k + 1) (d + k + 1) sA (D x y))
    (hB : ∀ x y, GridFormation (r + k + 1) (d + k + 1) sB (B x y)) :
    let C := fun v =>
      let x := (P.arguments k).decode v
      universeProductCode r d k hd (T x) (hw x) (D x) (B x)
    P.readCodeFamily hd k (P.storeCodeFamily hd k C) = C :=
  P.read_store_projected hd k _ (fun x => universeProductCode_formation r d k hd (T x) (hw x)
    (D x) (B x) hr (hT x) (hD x) (hB x))

noncomputable def UniversePrefix.storeCandidateFamily (P : UniversePrefix r (r + 1)) (k : Nat)
    (C : TowerFamily (universeArgumentSystems r k) → Candidate) :
    TowerValue (carrierGrid (r + 1 + k) (r + 1 + k)) :=
  P.encodeCandidate k (familyEncode (P.arguments k) (CarrierRetraction.identity Candidate) C)

noncomputable def UniversePrefix.readCandidateFamily (P : UniversePrefix r (r + 1)) (k : Nat)
    (v : TowerValue (carrierGrid (r + 1 + k) (r + 1 + k))) :
    TowerFamily (universeArgumentSystems r k) → Candidate :=
  familyDecode (P.arguments k) (CarrierRetraction.identity Candidate) (P.decodeCandidate k v)

theorem UniversePrefix.read_store_candidate (P : UniversePrefix r (r + 1)) (k : Nat)
    (C : TowerFamily (universeArgumentSystems r k) → Candidate)
    (hcanonical : ∀ v, C ((P.arguments k).encode ((P.arguments k).decode v)) = C v) :
    P.readCandidateFamily k (P.storeCandidateFamily k C) = C := by
  unfold readCandidateFamily storeCandidateFamily
  rw [decodeCandidate_encodeCandidate]
  exact (family_decode_encode_iff _ _ C).mpr ⟨fun _ => rfl, hcanonical⟩

end Submission.Helpers
