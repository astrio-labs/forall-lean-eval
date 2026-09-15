import Submission.CarrierEmbedding

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Codes may extend even at the bottom. Extension of their data is requested
only under the separate proposition `p`. -/
structure PartialCarrierEmbedding (S T : CarrierSystem) (p : Prop) where
  codes : CarrierRetraction S.Code T.Code
  values : p → (A : S.Code) → CarrierRetraction (S.El A) (T.El (codes.encode A))

def PartialCarrierEmbedding.full (R : PartialCarrierEmbedding S T p) (hp : p) : CarrierEmbedding S T :=
  ⟨R.codes, R.values hp⟩

def PartialCarrierEmbedding.ofEq (hS : S = S') (hT : T = T')
    (R : PartialCarrierEmbedding S' T' p) : PartialCarrierEmbedding S T p := by
  cases hS
  cases hT
  exact R

/-- Increasing a row preserves every code in its triangle. The values are
preserved strictly above the bottom. The code and value dependencies both
decrease the sum of the row and coordinate, including the universe case. -/
noncomputable def carrierGridVertical : (r d : Nat) → d ≤ r →
    PartialCarrierEmbedding (carrierGrid r d) (carrierGrid (r + 1) d) (d < r)
  | 0, 0, _ => ⟨CarrierRetraction.identity Arity, fun h _ => by omega⟩
  | 0, _ + 1, h => by omega
  | _ + 1, 0, _ => ⟨CarrierRetraction.identity Arity,
      fun _ A => CarrierRetraction.identity A.ShapeEl⟩
  | r + 1, d + 1, h => by
    have hle : d ≤ r := Nat.le_of_succ_le_succ h
    let R := carrierGridVertical r d hle
    let Q := (carrierGridVertical (r + 1) d (by omega)).full (by omega)
    by_cases hlt : d < r
    · let L := carrierGridVertical r (d + 1) (by omega)
      apply PartialCarrierEmbedding.ofEq
        (carrierGrid_intermediate r d hlt)
        (carrierGrid_intermediate (r + 1) d (by omega))
      refine ⟨LayerCode.mapRetraction R.codes Q Q.codes.encode Q.codes.injective, ?_⟩
      intro _ A
      exact LayerCode.mapValues
        (U := universeCarrierAtoms (carrierGrid (r + 1) d) (carrierGrid r (d + 1)))
        (V := universeCarrierAtoms (carrierGrid (r + 2) d) (carrierGrid (r + 1) (d + 1)))
        R.codes.encode Q.representation Q.codes.encode
        (R.values hlt) (fun a => (Q.values a).arrow L.codes) A
    · have hd : d = r := by omega
      subst d
      apply PartialCarrierEmbedding.ofEq (carrierGrid_bottom r)
        (carrierGrid_intermediate (r + 1) r (Nat.lt_succ_self r))
      let u : noCarrierAtoms.Code →
          (universeCarrierAtoms (carrierGrid (r + 2) r) (carrierGrid (r + 1) (r + 1))).Code :=
        fun e => nomatch e
      refine ⟨LayerCode.mapRetraction R.codes Q u (fun e => nomatch e), ?_⟩
      intro hstrict _
      omega
termination_by r d _ => r + d

theorem carrierGrid_vertical_code_roundtrip (r d : Nat) (hd : d ≤ r)
    (A : (carrierGrid r d).Code) :
    (carrierGridVertical r d hd).codes.decode ((carrierGridVertical r d hd).codes.encode A) = A :=
  (carrierGridVertical r d hd).codes.roundtrip A

theorem carrierGrid_vertical_value_roundtrip (r d : Nat) (hd : d < r)
    (A : (carrierGrid r d).Code) (x : (carrierGrid r d).El A) :
    ((carrierGridVertical r d (Nat.le_of_lt hd)).values hd A).decode
      (((carrierGridVertical r d (Nat.le_of_lt hd)).values hd A).encode x) = x :=
  ((carrierGridVertical r d (Nat.le_of_lt hd)).values hd A).roundtrip x

end Submission.Helpers
