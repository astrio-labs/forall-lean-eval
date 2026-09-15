import Submission.UniversePrefix

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

def CarrierRetraction.unitFiber (X Y : Type) :
    CarrierRetraction (((_ : X) × Unit) → Y) (X → Y) where
  encode f x := f ⟨x, ()⟩
  decode f x := f x.1
  roundtrip f := by funext ⟨x, ⟨⟩⟩; rfl

def carrierGridCandidateObject (r : Nat) : CarrierObject (carrierGrid r r) Candidate :=
  ⟨carrierGridCandidateCode r, carrierGridCandidateRetraction r⟩

/-- The last lower-row argument may use the bottom carrier. It is interpreted
by an arrow; only earlier arguments need horizontal index representations. -/
noncomputable def orderedCandidateObjectSucc (r : Nat) :
    (T : CarrierTelescope (carrierGrid (r + 1))) → (lo : Nat) → T.Ordered lo (r + 2) →
      CarrierObject (carrierGrid (r + 1) (r + 1)) (T.El → Candidate)
  | .nil, _, _ => CarrierObject.pullback
      ((CarrierFunction.singletonDomain () (inferInstanceAs (Subsingleton Unit))
        (fun _ => Candidate)).toRetraction) (carrierGridCandidateObject (r + 1))
  | .cons i A B, lo, h => by
    by_cases hi : i < r + 1
    · let R := carrierGridPrefixRepresentation (r + 1) i r (by omega) (Nat.lt_succ_self r)
      exact CarrierObject.pullback
        (CarrierRetraction.curry ((carrierGrid (r + 1) i).El A) (fun x => (B x).El) (fun _ => Candidate))
        ((carrierGridQuantifiers r r).representPi (R.code A) (R.values A) (fun x =>
          orderedCandidateObjectSucc r (B x) (i + 1) (h.2.2 x)))
    · have he : i = r + 1 := by have hh := h.2.1; omega
      subst i
      have hB : B = fun _ => .nil := funext (fun x => (h.2.2 x).empty (Nat.le_refl _))
      subst B
      exact CarrierObject.pullback (CarrierRetraction.unitFiber _ Candidate)
        (CarrierObject.arrow (carrierGridArrows (r + 1) (r + 1))
          (CarrierObject.direct _ A) (carrierGridCandidateObject (r + 1)))

noncomputable def orderedCandidateObjectZero (T : CarrierTelescope (carrierGrid 0))
    (lo : Nat) (h : T.Ordered lo 1) : CarrierObject (carrierGrid 0 0) (T.El → Candidate) := by
  cases T with
  | nil =>
    exact CarrierObject.pullback
      ((CarrierFunction.singletonDomain () (inferInstanceAs (Subsingleton Unit))
        (fun _ => Candidate)).toRetraction) (carrierGridCandidateObject 0)
  | cons i A B =>
    have hi : i = 0 := by have hh := h.2.1; omega
    subst i
    have hB : B = fun _ => .nil := funext (fun x => (h.2.2 x).empty (Nat.le_refl _))
    subst B
    exact CarrierObject.pullback (CarrierRetraction.unitFiber _ Candidate)
      (CarrierObject.arrow (carrierGridArrows 0 0) (CarrierObject.direct _ A) (carrierGridCandidateObject 0))

noncomputable def orderedCandidateObject (r : Nat) (T : CarrierTelescope (carrierGrid r))
    (lo : Nat) (h : T.Ordered lo (r + 1)) : CarrierObject (carrierGrid r r) (T.El → Candidate) :=
  match r with
  | 0 => orderedCandidateObjectZero T lo h
  | r + 1 => orderedCandidateObjectSucc r T lo h

/-- The universe boundary is available at every row, including row zero;
no vertical value embedding across that boundary is used. -/
noncomputable def UniversePrefix.candidateObject (P : UniversePrefix r (r + 1)) :
    CarrierObject (carrierGrid (r + 1) (r + 1)) (P.El → Candidate) :=
  CarrierObject.map LayerCode.smallRepresentation (orderedCandidateObject r P.telescope 0 P.ordered)

theorem UniversePrefix.candidate_roundtrip (P : UniversePrefix r (r + 1)) (C : P.El → Candidate) :
    P.candidateObject.values.decode (P.candidateObject.values.encode C) = C :=
  P.candidateObject.roundtrip C

end Submission.Helpers
