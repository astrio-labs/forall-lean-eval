import Submission.CarrierTelescopeAlgebra

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Constant functions provide a retraction for every inhabited index. -/
def CarrierRetraction.constants (X Y : Type) (x : X) : CarrierRetraction Y (X → Y) :=
  ⟨fun y _ => y, fun f => f x, fun _ => rfl⟩

/-- A telescope may mix values from the current row and its preceding row. -/
def carrierGridUniverseSources (r : Nat) (upper : Nat → Bool) (depth : Nat → Nat) (i : Nat) : CarrierSystem :=
  if upper i then carrierGrid (r + 1) (depth i) else carrierGrid r (depth i)

noncomputable def carrierGridUniverseSourceRepresentation (r e : Nat) (he : e < r)
    (upper : Nat → Bool) (depth : Nat → Nat) (i : Nat) (hi : depth i ≤ e) :
    CarrierRepresentation (carrierGridUniverseSources r upper depth i) (carrierGrid (r + 1) e) := by
  unfold carrierGridUniverseSources
  split
  · exact carrierGridPrefixRepresentation (r + 1) (depth i) e hi (by omega)
  · exact ((carrierGridVertical r (depth i) (by omega)).full (by omega)).representation.comp
      (carrierGridPrefixRepresentation (r + 1) (depth i) e hi (by omega))

noncomputable def carrierGridLowerCodeObject (r e : Nat) (he : e < r) :
    CarrierObject (carrierGrid (r + 1) (e + 1)) (carrierGrid r (e + 1)).Code :=
  let I := carrierGrid (r + 1) e
  CarrierObject.pullback (CarrierRetraction.constants (I.El I.defaultCode) _ (I.point I.defaultCode))
    (carrierGridUniverseAtom r e he I.defaultCode)

/-- All lower-code families over a finite dependent telescope have a carrier
in the next intermediate coordinate. The telescope length is arbitrary;
the only restriction concerns the coordinates from which its values come. -/
noncomputable def carrierGridUniverseTelescope (r e : Nat) (he : e < r)
    (upper : Nat → Bool) (depth : Nat → Nat)
    (T : CarrierTelescope (carrierGridUniverseSources r upper depth))
    (h : T.All (fun i => depth i ≤ e)) :
    CarrierObject (carrierGrid (r + 1) (e + 1)) (T.El → (carrierGrid r (e + 1)).Code) :=
  T.representPi (carrierGridQuantifiers r e) (carrierGridUniverseSourceRepresentation r e he upper depth)
    h (fun _ => (carrierGrid r (e + 1)).Code) (fun _ => carrierGridLowerCodeObject r e he)

theorem carrierGrid_universe_telescope_roundtrip (r e : Nat) (he : e < r)
    (upper : Nat → Bool) (depth : Nat → Nat)
    (T : CarrierTelescope (carrierGridUniverseSources r upper depth)) (h : T.All (fun i => depth i ≤ e))
    (C : T.El → (carrierGrid r (e + 1)).Code) :
    (carrierGridUniverseTelescope r e he upper depth T h).values.decode
      ((carrierGridUniverseTelescope r e he upper depth T h).values.encode C) = C :=
  (carrierGridUniverseTelescope r e he upper depth T h).roundtrip C

/-- At the boundary, the lower row represents the preceding telescope and
an additional value in its bottom carrier before returning a candidate. -/
noncomputable def carrierGridUniverseTelescopeBottom (r : Nat)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within r)
    (D : T.El → (carrierGrid (r + 1) (r + 1)).Code) :
    CarrierObject (carrierGrid (r + 2) (r + 2))
      ((x : T.El) → (carrierGrid (r + 1) (r + 1)).El (D x) → Candidate) :=
  CarrierObject.map LayerCode.smallRepresentation
    (T.representPi (carrierGridQuantifiers r r)
      (fun i hi => carrierGridPrefixRepresentation (r + 1) i r hi (Nat.lt_succ_self r))
      ((T.within_all r).mp h) (fun x => (carrierGrid (r + 1) (r + 1)).El (D x) → Candidate)
      (fun x => CarrierObject.arrow (carrierGridArrows (r + 1) (r + 1))
        (CarrierObject.direct _ (D x)) ⟨carrierGridCandidateCode (r + 1), carrierGridCandidateRetraction (r + 1)⟩))

theorem carrierGrid_universe_telescope_bottom_roundtrip (r : Nat)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within r)
    (D : T.El → (carrierGrid (r + 1) (r + 1)).Code)
    (C : (x : T.El) → (carrierGrid (r + 1) (r + 1)).El (D x) → Candidate) :
    (carrierGridUniverseTelescopeBottom r T h D).values.decode
      ((carrierGridUniverseTelescopeBottom r T h D).values.encode C) = C :=
  (carrierGridUniverseTelescopeBottom r T h D).roundtrip C

theorem carrierGridUniverseTelescopeBottom_small (r : Nat)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within r)
    (D : T.El → (carrierGrid (r + 1) (r + 1)).Code) :
    (carrierGridUniverseTelescopeBottom r T h D).code.IsSmall := ⟨_, rfl⟩

end Submission.Helpers
