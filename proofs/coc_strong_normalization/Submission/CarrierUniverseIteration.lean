import Submission.SecondGridOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A further universe coordinate retains all three preceding arguments.
The strict inequality supplies value representations only above the bottom. -/
noncomputable def carrierGridUniverseTwice (r d : Nat) (hd : d + 2 < r)
    (a : (carrierGrid (r + 1) d).Code)
    (F : (carrierGrid (r + 1) d).El a → (carrierGrid r (d + 1)).Code)
    (G : (x : (carrierGrid (r + 1) d).El a) →
      (carrierGrid r (d + 1)).El (F x) → (carrierGrid r (d + 2)).Code) :
    CarrierObject (carrierGrid (r + 1) (d + 3))
      ((x : (carrierGrid (r + 1) d).El a) →
        (y : (carrierGrid r (d + 1)).El (F x)) →
          (carrierGrid r (d + 2)).El (G x y) → (carrierGrid r (d + 3)).Code) :=
  let H := carrierGridPrefixRepresentation (r + 1) d (d + 2) (by omega) (by omega)
  let V := (carrierGridVertical r (d + 1) (by omega)).full (by omega)
  let J := carrierGridHorizontal (r + 1) (d + 1) (by omega)
  let W := (carrierGridVertical r (d + 2) (by omega)).full hd
  (carrierGridQuantifiers r (d + 2)).representPi (H.code a) (H.values a) (fun x =>
    (carrierGridQuantifiers r (d + 2)).representPi (J.code (V.codes.encode (F x)))
      ((V.values (F x)).comp (J.values (V.codes.encode (F x)))) (fun y =>
        CarrierObject.pullback ((W.values (G x y)).arrow (CarrierRetraction.identity _))
          (carrierGridUniverseAtom r (d + 2) hd (W.codes.encode (G x y)))))

theorem carrierGrid_universe_twice_roundtrip (r d : Nat) (hd : d + 2 < r)
    (a : (carrierGrid (r + 1) d).Code)
    (F : (carrierGrid (r + 1) d).El a → (carrierGrid r (d + 1)).Code)
    (G : (x : (carrierGrid (r + 1) d).El a) →
      (carrierGrid r (d + 1)).El (F x) → (carrierGrid r (d + 2)).Code)
    (C : (x : (carrierGrid (r + 1) d).El a) →
      (y : (carrierGrid r (d + 1)).El (F x)) →
        (carrierGrid r (d + 2)).El (G x y) → (carrierGrid r (d + 3)).Code) :
    (carrierGridUniverseTwice r d hd a F G).values.decode
      ((carrierGridUniverseTwice r d hd a F G).values.encode C) = C :=
  (carrierGridUniverseTwice r d hd a F G).roundtrip C

/-- The analogous three-argument family at the boundary stores candidates.
Only the two earlier coordinates are quantifier indices in the lower row. -/
noncomputable def carrierGridUniverseTwiceBottom (r : Nat)
    (a : (carrierGrid (r + 2) r).Code)
    (F : (carrierGrid (r + 2) r).El a → (carrierGrid (r + 2) (r + 1)).Code)
    (G : (x : (carrierGrid (r + 2) r).El a) →
      (carrierGrid (r + 2) (r + 1)).El (F x) → (carrierGrid (r + 2) (r + 2)).Code) :
    CarrierObject (carrierGrid (r + 3) (r + 3))
      ((x : (carrierGrid (r + 2) r).El a) →
        (y : (carrierGrid (r + 2) (r + 1)).El (F x)) →
          (carrierGrid (r + 2) (r + 2)).El (G x y) → Candidate) :=
  let H := carrierGridHorizontal (r + 2) r (by omega)
  CarrierObject.map LayerCode.smallRepresentation
    ((carrierGridQuantifiers (r + 1) (r + 1)).representPi (H.code a) (H.values a) (fun x =>
      (carrierGridQuantifiers (r + 1) (r + 1)).representPi (F x) (CarrierRetraction.identity _) (fun y =>
        CarrierObject.arrow (carrierGridArrows (r + 2) (r + 2))
          (CarrierObject.direct _ (G x y))
          ⟨carrierGridCandidateCode (r + 2), carrierGridCandidateRetraction (r + 2)⟩)))

theorem carrierGrid_universe_twice_bottom_roundtrip (r : Nat)
    (a : (carrierGrid (r + 2) r).Code)
    (F : (carrierGrid (r + 2) r).El a → (carrierGrid (r + 2) (r + 1)).Code)
    (G : (x : (carrierGrid (r + 2) r).El a) →
      (carrierGrid (r + 2) (r + 1)).El (F x) → (carrierGrid (r + 2) (r + 2)).Code)
    (C : (x : (carrierGrid (r + 2) r).El a) →
      (y : (carrierGrid (r + 2) (r + 1)).El (F x)) →
        (carrierGrid (r + 2) (r + 2)).El (G x y) → Candidate) :
    (carrierGridUniverseTwiceBottom r a F G).values.decode
      ((carrierGridUniverseTwiceBottom r a F G).values.encode C) = C :=
  (carrierGridUniverseTwiceBottom r a F G).roundtrip C

end Submission.Helpers
