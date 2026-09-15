import Submission.CarrierGridCandidates
import Submission.CarrierGridVertical

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A concrete carrier code representing a specified type of semantic data. -/
structure CarrierObject (S : CarrierSystem) (X : Type) where
  code : S.Code
  values : CarrierRetraction X (S.El code)

def CarrierObject.direct (S : CarrierSystem) (A : S.Code) : CarrierObject S (S.El A) :=
  ⟨A, CarrierRetraction.identity _⟩

def CarrierObject.ofEq (h : S = T) (R : CarrierObject T X) : CarrierObject S X := by
  cases h
  exact R

def CarrierObject.pullback (R : CarrierRetraction X Y) (O : CarrierObject S Y) : CarrierObject S X :=
  ⟨O.code, R.comp O.values⟩

def CarrierObject.map (R : CarrierRepresentation S T) (O : CarrierObject S X) : CarrierObject T X :=
  ⟨R.code O.code, O.values.comp (R.values O.code)⟩

noncomputable def CarrierObject.arrow (P : CarrierArrows S)
    (A : CarrierObject S X) (B : CarrierObject S Y) : CarrierObject S (X → Y) :=
  ⟨P.code A.code B.code, (A.values.arrow B.values).comp ((P.functions A.code B.code).toRetraction)⟩

noncomputable def CarrierQuantifiers.representPi {X : Type} {Y : X → Type}
    (Q : CarrierQuantifiers I S) (a : I.Code)
    (R : CarrierRetraction X (I.El a)) (B : (x : X) → CarrierObject S (Y x)) :
    CarrierObject S ((x : X) → Y x) :=
  ⟨Q.code a (fun v => (B (R.decode v)).code),
    (CarrierRetraction.pi R Y (fun x => S.El (B x).code) (fun x => (B x).values)).comp
      ((Q.functions a (fun v => (B (R.decode v)).code)).toRetraction)⟩

theorem CarrierObject.roundtrip (O : CarrierObject S X) (x : X) :
    O.values.decode (O.values.encode x) = x := O.values.roundtrip x

/-- A genuine atom in an intermediate grid cell stores a family of lower
codes indexed by the preceding carrier. -/
def carrierGridUniverseAtom (r d : Nat) (hd : d < r) (a : (carrierGrid (r + 1) d).Code) :
    CarrierObject (carrierGrid (r + 1) (d + 1))
      ((carrierGrid (r + 1) d).El a → (carrierGrid r (d + 1)).Code) :=
  CarrierObject.ofEq (carrierGrid_intermediate r d hd)
    (CarrierObject.direct
      (layerCarrierSystem (carrierGrid r d) (carrierGrid (r + 1) d)
        (universeCarrierAtoms (carrierGrid (r + 1) d) (carrierGrid r (d + 1)))) (.atom a))

/-- Refining an intermediate universe stores lower codes depending on both
the preceding value and its next value. The two required data representations
come from the horizontal and vertical constructions respectively. -/
noncomputable def carrierGridUniverseNext (r d : Nat) (hd : d + 1 < r)
    (a : (carrierGrid (r + 1) d).Code)
    (F : (carrierGrid (r + 1) d).El a → (carrierGrid r (d + 1)).Code) :
    CarrierObject (carrierGrid (r + 1) (d + 2))
      ((x : (carrierGrid (r + 1) d).El a) →
        (carrierGrid r (d + 1)).El (F x) → (carrierGrid r (d + 2)).Code) :=
  let H := carrierGridHorizontal (r + 1) d (by omega)
  let V := (carrierGridVertical r (d + 1) (Nat.le_of_lt hd)).full hd
  (carrierGridQuantifiers r (d + 1)).representPi (H.code a) (H.values a) (fun x =>
    CarrierObject.pullback ((V.values (F x)).arrow (CarrierRetraction.identity _))
      (carrierGridUniverseAtom r (d + 1) hd (V.codes.encode (F x))))

theorem carrierGrid_universe_next_roundtrip (r d : Nat) (hd : d + 1 < r)
    (a : (carrierGrid (r + 1) d).Code)
    (F : (carrierGrid (r + 1) d).El a → (carrierGrid r (d + 1)).Code)
    (C : (x : (carrierGrid (r + 1) d).El a) →
      (carrierGrid r (d + 1)).El (F x) → (carrierGrid r (d + 2)).Code) :
    (carrierGridUniverseNext r d hd a F).values.decode
      ((carrierGridUniverseNext r d hd a F).values.encode C) = C :=
  (carrierGridUniverseNext r d hd a F).roundtrip C

/-- At the bottom, the index and fiber already factor through the preceding
row. That row's product then represents the complete candidate family. -/
noncomputable def carrierGridUniverseBottom (r : Nat)
    (a : (carrierGrid (r + 1) r).Code)
    (F : (carrierGrid (r + 1) r).El a → (carrierGrid (r + 1) (r + 1)).Code) :
    CarrierObject (carrierGrid (r + 2) (r + 2))
      ((x : (carrierGrid (r + 1) r).El a) →
        (carrierGrid (r + 1) (r + 1)).El (F x) → Candidate) :=
  CarrierObject.map LayerCode.smallRepresentation
    ((carrierGridQuantifiers r r).representPi a (CarrierRetraction.identity _) (fun x =>
      CarrierObject.arrow (carrierGridArrows (r + 1) (r + 1))
        (CarrierObject.direct _ (F x))
        ⟨carrierGridCandidateCode (r + 1), carrierGridCandidateRetraction (r + 1)⟩))

theorem carrierGrid_universe_bottom_roundtrip (r : Nat)
    (a : (carrierGrid (r + 1) r).Code)
    (F : (carrierGrid (r + 1) r).El a → (carrierGrid (r + 1) (r + 1)).Code)
    (C : (x : (carrierGrid (r + 1) r).El a) →
      (carrierGrid (r + 1) (r + 1)).El (F x) → Candidate) :
    (carrierGridUniverseBottom r a F).values.decode
      ((carrierGridUniverseBottom r a F).values.encode C) = C :=
  (carrierGridUniverseBottom r a F).roundtrip C

end Submission.Helpers
