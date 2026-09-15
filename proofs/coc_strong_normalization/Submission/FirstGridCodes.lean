import Submission.CarrierGridRepresentation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The first intermediate coordinate has a variable lower universe. Its
code syntax is independent of the carrier of that lower universe. -/
abbrev firstGridSystem (L : CarrierSystem) :=
  layerCarrierSystem shapeCarrierSystem shapeCarrierSystem
    (universeCarrierAtoms shapeCarrierSystem L)

def MiddleCode.recode (L : CarrierSystem) : MiddleCode → (firstGridSystem L).Code
  | .small a => .small a
  | .universe a => .atom a
  | .fn A B => .fn (A.recode L) (B.recode L)
  | .quant a B => .all a (fun x => (B x).recode L)

def MiddleCode.uncode (L : CarrierSystem) : (firstGridSystem L).Code → MiddleCode
  | .small a => .small a
  | .atom a => .universe a
  | .fn A B => .fn (uncode L A) (uncode L B)
  | .all a B => .quant a (fun x => uncode L (B x))

theorem MiddleCode.recode_roundtrip (L : CarrierSystem) (A : MiddleCode) :
    MiddleCode.uncode L (A.recode L) = A := by
  induction A with
  | small => rfl
  | «universe» => rfl
  | fn A B ihA ihB => change MiddleCode.fn _ _ = _; rw [ihA, ihB]
  | quant a B ih =>
    change MiddleCode.quant a _ = _
    exact congrArg (MiddleCode.quant a) (funext ih)

theorem MiddleCode.recode_injective (L : CarrierSystem) : Function.Injective (MiddleCode.recode L) := by
  intro A B h
  have he := congrArg (MiddleCode.uncode L) h
  rw [MiddleCode.recode_roundtrip, MiddleCode.recode_roundtrip] at he
  exact he

theorem MiddleCode.recode_arrow (L : CarrierSystem) (A B : MiddleCode) :
    (A.arrow B).recode L = (LayerCode.arrows shapeCarrierArrows).code (A.recode L) (B.recode L) := by
  cases A <;> cases B with
  | small b => cases b <;>
      simp [MiddleCode.arrow, MiddleCode.recode, LayerCode.arrows, LayerCode.compactArrow,
        shapeCarrierArrows, shapeCarrierSystem, Arity.arrow]
  | _ => simp [MiddleCode.arrow, MiddleCode.recode, LayerCode.arrows, LayerCode.compactArrow,
      shapeCarrierSystem]

theorem MiddleCode.recode_all (L : CarrierSystem) (a : Arity) (B : a.ShapeEl → MiddleCode) :
    (MiddleCode.all a B).recode L =
      (LayerCode.freeQuantifiers shapeCarrierArrows.terminal shapeCarrierArrows.terminal).code
        a (fun x => (B x).recode L) := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · rw [MiddleCode.all_trivial a B h]
    symm
    exact LayerCode.freeAll_trivial shapeCarrierArrows.terminal shapeCarrierArrows.terminal
      a _ (fun x => congrArg (MiddleCode.recode L) (h x))
  · have he : ¬ ∀ x : a.ShapeEl, (B x).recode L = LayerCode.small Arity.unit := by
      intro hh
      exact h (fun x => MiddleCode.recode_injective L (hh x))
    have he' : ¬ ∀ x : shapeCarrierSystem.El a, (B x).recode L =
        (LayerCode.small shapeCarrierSystem.defaultCode : (firstGridSystem L).Code) := he
    change _ = LayerCode.freeAll shapeCarrierArrows.terminal shapeCarrierArrows.terminal
      a (fun x => (B x).recode L)
    unfold LayerCode.freeAll
    rw [if_neg he']
    unfold MiddleCode.all
    rw [if_neg h]
    cases a <;> simp [shapeCarrierSystem, Arity.shapePoint, MiddleCode.recode]
    rfl

theorem MiddleCode.recode_pi (L : CarrierSystem) (a : Arity) (D B : a.ShapeEl → MiddleCode) :
    (MiddleCode.pi a D B).recode L =
      (LayerCode.freeQuantifiers shapeCarrierArrows.terminal shapeCarrierArrows.terminal).pi
        (LayerCode.arrows shapeCarrierArrows) a (fun x => (D x).recode L) (fun x => (B x).recode L) := by
  unfold MiddleCode.pi CarrierQuantifiers.pi
  rw [MiddleCode.recode_all]
  exact congrArg
    ((LayerCode.freeQuantifiers (U := universeCarrierAtoms shapeCarrierSystem L)
      shapeCarrierArrows.terminal shapeCarrierArrows.terminal).code a)
    (funext (fun x => MiddleCode.recode_arrow L (D x) (B x)))

def firstGridCode (r : Nat) (A : MiddleCode) : (carrierGrid (r + 2) 1).Code :=
  A.recode (carrierGrid (r + 1) 1)

theorem firstGridCode_arrow (r : Nat) (A B : MiddleCode) :
    firstGridCode r (A.arrow B) = (carrierGridArrows (r + 2) 1).code
      (firstGridCode r A) (firstGridCode r B) := MiddleCode.recode_arrow _ A B

theorem firstGridCode_pi (r : Nat) (a : Arity) (D B : a.ShapeEl → MiddleCode) :
    firstGridCode r (MiddleCode.pi a D B) =
      (carrierGridQuantifiers (r + 1) 0).pi (carrierGridArrows (r + 2) 1)
        a (fun x => firstGridCode r (D x)) (fun x => firstGridCode r (B x)) :=
  MiddleCode.recode_pi _ a D B

end Submission.Helpers
