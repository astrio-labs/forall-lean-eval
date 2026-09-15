import Submission.ThirdTowerBridge

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Optional atoms do not need a default tag: the bottom layer has no universe atom. -/
structure CarrierAtoms where
  Code : Type
  El : Code → Type
  point : (A : Code) → El A

def noCarrierAtoms : CarrierAtoms where
  Code := Empty
  El e := nomatch e
  point e := nomatch e

/-- An intermediate universe stores lower codes indexed by preceding data. -/
def universeCarrierAtoms (I L : CarrierSystem) : CarrierAtoms where
  Code := I.Code
  El a := I.El a → L.Code
  point _ _ := L.defaultCode

inductive LayerCode (S I : CarrierSystem) (U : CarrierAtoms) where
  | small : S.Code → LayerCode S I U
  | atom : U.Code → LayerCode S I U
  | fn : LayerCode S I U → LayerCode S I U → LayerCode S I U
  | all (a : I.Code) : (I.El a → LayerCode S I U) → LayerCode S I U

def LayerCode.El (S I : CarrierSystem) (U : CarrierAtoms) : LayerCode S I U → Type
  | .small a => S.El a
  | .atom a => U.El a
  | .fn A B => A.El S I U → B.El S I U
  | .all _ B => (x : _) → (B x).El S I U

def LayerCode.point (S I : CarrierSystem) (U : CarrierAtoms) :
    (A : LayerCode S I U) → A.El S I U
  | .small a => S.point a
  | .atom a => U.point a
  | .fn _ B => fun _ => B.point S I U
  | .all _ B => fun x => (B x).point S I U

abbrev layerCarrierSystem (S I : CarrierSystem) (U : CarrierAtoms) : CarrierSystem where
  Code := LayerCode S I U
  El := LayerCode.El S I U
  point := LayerCode.point S I U
  defaultCode := .small S.defaultCode

def arityCarrierSystem : CarrierSystem where
  Code := Arity
  El := Arity.El
  point := Arity.point
  defaultCode := .unit

def shapeCarrierSystem : CarrierSystem where
  Code := Arity
  El := Arity.ShapeEl
  point := Arity.shapePoint
  defaultCode := .unit

/-- A diagonal is built from left to right. Universe atoms refer to the already
constructed preceding diagonal; quantifier domains refer to the preceding
coordinate on this diagonal. Neither operation refers to its own decoder. -/
def buildCarrierRow (previous : Nat → CarrierSystem) (r : Nat) : Nat → CarrierSystem
  | 0 => shapeCarrierSystem
  | d + 1 =>
      let I := buildCarrierRow previous r d
      layerCarrierSystem (previous d) I
        (if d < r then universeCarrierAtoms I (previous (d + 1)) else noCarrierAtoms)

/-- The two indices separate total refinement resources from the coordinate
being interpreted. Only coordinates `d ≤ r` are used in the triangular grid. -/
def carrierGrid : Nat → Nat → CarrierSystem
  | 0, _ => arityCarrierSystem
  | r + 1, d => buildCarrierRow (carrierGrid r) r d

/-- At coordinate `d`, `h` semantic coordinates remain below it. -/
def carrierGridLevel (h d : Nat) : CarrierSystem := carrierGrid (h + d) d

theorem carrierGrid_succ (r d : Nat) :
    carrierGrid (r + 1) (d + 1) =
      layerCarrierSystem (carrierGrid r d) (carrierGrid (r + 1) d)
        (if d < r then universeCarrierAtoms (carrierGrid (r + 1) d) (carrierGrid r (d + 1))
          else noCarrierAtoms) := rfl

theorem carrierGrid_bottom (r : Nat) :
    carrierGrid (r + 1) (r + 1) =
      layerCarrierSystem (carrierGrid r r) (carrierGrid (r + 1) r) noCarrierAtoms := by
  rw [carrierGrid_succ, if_neg (Nat.lt_irrefl r)]

theorem carrierGrid_intermediate (r d : Nat) (hd : d < r) :
    carrierGrid (r + 1) (d + 1) =
      layerCarrierSystem (carrierGrid r d) (carrierGrid (r + 1) d)
        (universeCarrierAtoms (carrierGrid (r + 1) d) (carrierGrid r (d + 1))) := by
  rw [carrierGrid_succ, if_pos hd]

/-- Every cell has a point without any normalization hypothesis. -/
theorem carrierGrid_inhabited (r d : Nat) (A : (carrierGrid r d).Code) :
    Nonempty ((carrierGrid r d).El A) := ⟨(carrierGrid r d).point A⟩

/-- The first bottom cell represents the checked fiber carriers. -/
def fiberGridCode : FiberCode → (carrierGrid 1 1).Code
  | .small a => .small a
  | .fn A B => .fn (fiberGridCode A) (fiberGridCode B)
  | .quant a B => .all a (fun x => fiberGridCode (B x))

def fiberGridDecode : (carrierGrid 1 1).Code → FiberCode
  | .small a => .small a
  | .atom e => nomatch e
  | .fn A B => .fn (fiberGridDecode A) (fiberGridDecode B)
  | .all a B => .quant a (fun x => fiberGridDecode (B x))

theorem fiberGrid_code_roundtrip (A : FiberCode) : fiberGridDecode (fiberGridCode A) = A := by
  induction A with
  | small a => rfl
  | fn A B ihA ihB => change FiberCode.fn _ _ = _; rw [ihA, ihB]
  | quant a B ih =>
    change FiberCode.quant a (fun x => fiberGridDecode (fiberGridCode (B x))) = _
    congr 1
    funext x
    exact ih x

def fiberGridCodeRetraction : CarrierRetraction FiberCode (carrierGrid 1 1).Code :=
  ⟨fiberGridCode, fiberGridDecode, fiberGrid_code_roundtrip⟩

def fiberGridRetraction : (A : FiberCode) → CarrierRetraction A.El ((carrierGrid 1 1).El (fiberGridCode A))
  | .small a => CarrierRetraction.identity a.El
  | .fn A B => (fiberGridRetraction A).arrow (fiberGridRetraction B)
  | .quant a B => CarrierRetraction.pi (CarrierRetraction.identity a.ShapeEl)
      (fun x => (B x).El) (fun x => (carrierGrid 1 1).El (fiberGridCode (B x)))
      (fun x => fiberGridRetraction (B x))

/-- The first intermediate cell has exactly the extra universe-code data
needed by the source bound-three middle layer. -/
def middleGridCode : MiddleCode → (carrierGrid 2 1).Code
  | .small a => .small a
  | .universe a => .atom a
  | .fn A B => .fn (middleGridCode A) (middleGridCode B)
  | .quant a B => .all a (fun x => middleGridCode (B x))

def middleGridRetraction : (A : MiddleCode) →
    CarrierRetraction A.El ((carrierGrid 2 1).El (middleGridCode A))
  | .small a => CarrierRetraction.identity a.ShapeEl
  | .universe a => (CarrierRetraction.identity a.ShapeEl).arrow fiberGridCodeRetraction
  | .fn A B => (middleGridRetraction A).arrow (middleGridRetraction B)
  | .quant a B => CarrierRetraction.pi (CarrierRetraction.identity a.ShapeEl)
      (fun x => (B x).El) (fun x => (carrierGrid 2 1).El (middleGridCode (B x)))
      (fun x => middleGridRetraction (B x))

/-- The second bottom cell represents all carriers used by `BoundedModel 3`. -/
def thirdGridCode : ThirdCode → (carrierGrid 2 2).Code
  | .small a => .small (fiberGridCode a)
  | .fn A B => .fn (thirdGridCode A) (thirdGridCode B)
  | .quant A B => .all (middleGridCode A)
      (fun x => thirdGridCode (B ((middleGridRetraction A).decode x)))

def thirdGridRetraction : (A : ThirdCode) →
    CarrierRetraction A.El ((carrierGrid 2 2).El (thirdGridCode A))
  | .small a => fiberGridRetraction a
  | .fn A B => (thirdGridRetraction A).arrow (thirdGridRetraction B)
  | .quant A B => CarrierRetraction.pi (middleGridRetraction A)
      (fun x => (B x).El) (fun x => (carrierGrid 2 2).El (thirdGridCode (B x)))
      (fun x => thirdGridRetraction (B x))

theorem middle_grid_roundtrip (A : MiddleCode) (x : A.El) :
    (middleGridRetraction A).decode ((middleGridRetraction A).encode x) = x :=
  (middleGridRetraction A).roundtrip x

theorem third_grid_roundtrip (A : ThirdCode) (x : A.El) :
    (thirdGridRetraction A).decode ((thirdGridRetraction A).encode x) = x :=
  (thirdGridRetraction A).roundtrip x

end Submission.Helpers
