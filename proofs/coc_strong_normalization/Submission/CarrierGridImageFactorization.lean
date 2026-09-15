import Submission.CarrierGridTelescopeFormation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Iterated diagonal inclusion has an explicit code decoder at every depth. -/
def carrierGridImageCodes (r d : Nat) : (k : Nat) →
    CarrierRetraction (carrierGrid r d).Code (carrierGrid (r + k) (d + k)).Code
  | 0 => CarrierRetraction.identity _
  | k + 1 => (carrierGridImageCodes r d k).comp
      ⟨LayerCode.small, LayerCode.asSmall, fun _ => rfl⟩

def carrierGridImageValues (r d : Nat) : (k : Nat) → (A : (carrierGrid r d).Code) →
    CarrierRetraction ((carrierGrid r d).El A)
      ((carrierGrid (r + k) (d + k)).El ((carrierGridImageCodes r d k).encode A))
  | 0, _ => CarrierRetraction.identity _
  | k + 1, A => carrierGridImageValues r d k A

def carrierGridImageEmbedding (r d k : Nat) :
    CarrierEmbedding (carrierGrid r d) (carrierGrid (r + k) (d + k)) :=
  ⟨carrierGridImageCodes r d k, carrierGridImageValues r d k⟩

theorem carrierGridImageCodes_image (r d k : Nat) (A : (carrierGrid r d).Code) :
    GridCodeImage (r + k) (d + k) k ((carrierGridImageCodes r d k).encode A) := by
  induction k with
  | zero => exact .base _
  | succ k ih => exact .small ih

/-- The exact image invariant is necessary and sufficient for the reverse
code roundtrip. This is semantic factorization, with no source-bound descent. -/
theorem carrierGridImageCodes_encode_decode_iff (r d k : Nat)
    (A : (carrierGrid (r + k) (d + k)).Code) :
    (carrierGridImageCodes r d k).encode ((carrierGridImageCodes r d k).decode A) = A ↔
      GridCodeImage (r + k) (d + k) k A := by
  constructor
  · intro h
    rw [← h]
    exact carrierGridImageCodes_image r d k _
  · intro h
    induction k with
    | zero => rfl
    | succ k ih =>
      exact (congrArg LayerCode.small (ih A.asSmall h.peel)).trans h.small_eq.symm

theorem carrierGridImageCodes_family_iff (r d k : Nat) {X : Type}
    (C : X → (carrierGrid (r + k) (d + k)).Code) :
    (fun x => (carrierGridImageCodes r d k).encode ((carrierGridImageCodes r d k).decode (C x))) = C ↔
      ∀ x, GridCodeImage (r + k) (d + k) k (C x) := by
  constructor
  · intro h x
    exact (carrierGridImageCodes_encode_decode_iff r d k (C x)).mp (congrFun h x)
  · intro h
    exact funext (fun x => (carrierGridImageCodes_encode_decode_iff r d k (C x)).mpr (h x))

/-- Universe formation yields faithful decoding for any finite image depth,
uniformly for families indexed by arbitrary preceding semantic data. -/
theorem gridFormation_family_decode_encode (r d k : Nat) {X : Type}
    (C : X → (carrierGrid (r + k) (d + k)).Code)
    (hs : sortRank s ≤ r + 1) (hC : ∀ x, GridFormation (r + k) (d + k) s (C x)) :
    (fun x => (carrierGridImageCodes r d k).encode ((carrierGridImageCodes r d k).decode (C x))) = C :=
  (carrierGridImageCodes_family_iff r d k C).mpr (fun x => (hC x).image.mono (by omega))

theorem carrierGridImageEmbedding_value_roundtrip (r d k : Nat) (A : (carrierGrid r d).Code)
    (x : (carrierGrid r d).El A) :
    ((carrierGridImageEmbedding r d k).values A).decode
      (((carrierGridImageEmbedding r d k).values A).encode x) = x :=
  ((carrierGridImageEmbedding r d k).values A).roundtrip x

/-- Product formation discharges the exact image premise of universe
decoding for every image depth and every finite preceding telescope. -/
theorem carrierGrid_binder_image_decode_encode (r d k : Nat) (hd : d ≤ r)
    (T : CarrierTelescope (carrierGrid (r + k + 1))) (hw : T.Within (d + k))
    (D B : T.El → (carrierGrid (r + k + 1) (d + k + 1)).Code)
    (hr : Rl sA sB sC) (hs : sortRank sC ≤ r + 1)
    (hT : T.GridForm (r + k + 1) sA)
    (hD : ∀ x, GridFormation (r + k + 1) (d + k + 1) sA (D x))
    (hB : ∀ x, GridFormation (r + k + 1) (d + k + 1) sB (B x)) :
    (carrierGridImageCodes r d (k + 1)).encode
      ((carrierGridImageCodes r d (k + 1)).decode
        (carrierGridBinderCode (r + k) (d + k) (by omega) T hw D B)) =
      carrierGridBinderCode (r + k) (d + k) (by omega) T hw D B :=
  (carrierGridImageCodes_encode_decode_iff r d (k + 1) _).mpr
    ((carrierGridBinderCode_formation (r + k) (d + k) (by omega) T hw D B hr hT hD hB).image.mono
      (by omega))

end Submission.Helpers
