import Submission.CarrierUniverseAlgebra

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def CarrierRetraction.comp (R : CarrierRetraction A B) (S : CarrierRetraction B C) :
    CarrierRetraction A C where
  encode x := S.encode (R.encode x)
  decode x := R.decode (S.decode x)
  roundtrip x := by rw [S.roundtrip, R.roundtrip]

/-- A code representation includes an exact retraction on its data. -/
structure CarrierRepresentation (S T : CarrierSystem) where
  code : S.Code → T.Code
  values : (A : S.Code) → CarrierRetraction (S.El A) (T.El (code A))

def CarrierRepresentation.identity (S : CarrierSystem) : CarrierRepresentation S S :=
  ⟨id, fun A => CarrierRetraction.identity (S.El A)⟩

def CarrierRepresentation.comp (R : CarrierRepresentation S T) (Q : CarrierRepresentation T W) :
    CarrierRepresentation S W := ⟨fun A => Q.code (R.code A), fun A => (R.values A).comp (Q.values (R.code A))⟩

def CarrierRepresentation.ofEq (hS : S = S') (hT : T = T')
    (R : CarrierRepresentation S' T') : CarrierRepresentation S T := by
  cases hS
  cases hT
  exact R

structure CarrierAtomsRepresentation (U V : CarrierAtoms) where
  code : U.Code → V.Code
  values : (A : U.Code) → CarrierRetraction (U.El A) (V.El (code A))

namespace LayerCode

variable {S I T J : CarrierSystem} {U V : CarrierAtoms}

def smallRepresentation : CarrierRepresentation S (layerCarrierSystem S I U) :=
  ⟨LayerCode.small, fun A => CarrierRetraction.identity (S.El A)⟩

/-- A raw quantifier retains its index code, even when its data carrier is a
singleton. This provides an injection of codes, not a source-bound descent. -/
def indexCode : LayerCode S I U → I.Code
  | .all a _ => a
  | _ => I.defaultCode

def codeRetraction : CarrierRetraction I.Code (layerCarrierSystem S I U).Code where
  encode A := .all A (fun _ => .small S.defaultCode)
  decode := indexCode
  roundtrip _ := rfl

def representCode (R : CarrierRepresentation S T) (Q : CarrierRepresentation I J)
    (P : CarrierAtomsRepresentation U V) : LayerCode S I U → LayerCode T J V
  | .small A => .small (R.code A)
  | .atom A => .atom (P.code A)
  | .fn A B => .fn (representCode R Q P A) (representCode R Q P B)
  | .all A B => .all (Q.code A) (fun x => representCode R Q P (B ((Q.values A).decode x)))

def representValues (R : CarrierRepresentation S T) (Q : CarrierRepresentation I J)
    (P : CarrierAtomsRepresentation U V) : (A : LayerCode S I U) →
    CarrierRetraction (A.El S I U) ((representCode R Q P A).El T J V)
  | .small A => R.values A
  | .atom A => P.values A
  | .fn A B => (representValues R Q P A).arrow (representValues R Q P B)
  | .all A B => CarrierRetraction.pi (Q.values A)
      (fun x => (B x).El S I U) (fun x => (representCode R Q P (B x)).El T J V)
      (fun x => representValues R Q P (B x))

def representation (R : CarrierRepresentation S T) (Q : CarrierRepresentation I J)
    (P : CarrierAtomsRepresentation U V) :
    CarrierRepresentation (layerCarrierSystem S I U) (layerCarrierSystem T J V) :=
  ⟨representCode R Q P, representValues R Q P⟩

end LayerCode

def universeCarrierRepresentation (R : CarrierRepresentation I J)
    (Q : CarrierRetraction S.Code T.Code) :
    CarrierAtomsRepresentation (universeCarrierAtoms I S) (universeCarrierAtoms J T) :=
  ⟨R.code, fun A => (R.values A).arrow Q⟩

/-- Every intermediate coordinate represents the preceding coordinate. The
atom case moves lower codes rightward through their raw quantifier tag. Both
recursive carrier representations use strictly earlier coordinates. -/
def carrierGridHorizontal : (r d : Nat) → d + 1 < r →
    CarrierRepresentation (carrierGrid r d) (carrierGrid r (d + 1))
  | 0, _, h => by omega
  | 1, _, h => by omega
  | _ + 2, 0, _ => LayerCode.smallRepresentation
  | r + 2, d + 1, h => by
    let R := carrierGridHorizontal (r + 1) d (by omega)
    let Q := carrierGridHorizontal (r + 2) d (by omega)
    let L : CarrierRetraction (carrierGrid (r + 1) (d + 1)).Code
        (carrierGrid (r + 1) (d + 2)).Code := LayerCode.codeRetraction
    exact CarrierRepresentation.ofEq
      (carrierGrid_intermediate (r + 1) d (by omega))
      (carrierGrid_intermediate (r + 1) (d + 1) (by omega))
      (LayerCode.representation R Q (universeCarrierRepresentation Q L))
termination_by _ d _ => d

theorem carrierGrid_horizontal_roundtrip (r d : Nat) (hd : d + 1 < r)
    (A : (carrierGrid r d).Code) (x : (carrierGrid r d).El A) :
    ((carrierGridHorizontal r d hd).values A).decode
      (((carrierGridHorizontal r d hd).values A).encode x) = x :=
  ((carrierGridHorizontal r d hd).values A).roundtrip x

def carrierGridAdvance (r d : Nat) : (k : Nat) → d + k < r →
    CarrierRepresentation (carrierGrid r d) (carrierGrid r (d + k))
  | 0, _ => CarrierRepresentation.identity _
  | k + 1, h => (carrierGridAdvance r d k (by omega)).comp
      (carrierGridHorizontal r (d + k) (by omega))

/-- Consequently every earlier coordinate can be used as an index at any
later intermediate coordinate. -/
def carrierGridPrefixRepresentation (r d e : Nat) (hde : d ≤ e) (he : e < r) :
    CarrierRepresentation (carrierGrid r d) (carrierGrid r e) := by
  have h : d + (e - d) = e := Nat.add_sub_of_le hde
  exact CarrierRepresentation.ofEq rfl (congrArg (carrierGrid r) h.symm)
    (carrierGridAdvance r d (e - d) (by omega))

theorem carrierGrid_prefix_roundtrip (r d e : Nat) (hde : d ≤ e) (he : e < r)
    (A : (carrierGrid r d).Code) (x : (carrierGrid r d).El A) :
    ((carrierGridPrefixRepresentation r d e hde he).values A).decode
      (((carrierGridPrefixRepresentation r d e hde he).values A).encode x) = x :=
  ((carrierGridPrefixRepresentation r d e hde he).values A).roundtrip x

end Submission.Helpers
