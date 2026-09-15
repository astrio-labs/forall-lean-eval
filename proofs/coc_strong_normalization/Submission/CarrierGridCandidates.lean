import Submission.CarrierGridTelescope

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Realizability quantifies over the whole preceding telescope and the final
argument. No normalization hypothesis occurs in this candidate definition. -/
noncomputable def carrierGridBinderCandidate (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (p : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) → Candidate)
    (q : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) →
      (carrierGrid (r + 1) (e + 1)).El (B x) → Candidate)
    (f : (carrierGrid (r + 1) (e + 1)).El (carrierGridBinderCode r e he T h D B)) : Candidate :=
  Candidate.inter (fun x : T.El => Candidate.inter
    (fun y : (carrierGrid (r + 1) (e + 1)).El (D x) =>
      (p x y).arrow (q x y (carrierGridBinderApply r e he T h D B f x y))))

theorem carrierGridBinderCandidate_apply (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (p : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) → Candidate)
    (q : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) →
      (carrierGrid (r + 1) (e + 1)).El (B x) → Candidate)
    (f : (carrierGrid (r + 1) (e + 1)).El (carrierGridBinderCode r e he T h D B))
    (x : T.El) (y : (carrierGrid (r + 1) (e + 1)).El (D x))
    (hf : (carrierGridBinderCandidate r e he T h D B p q f).contains t)
    (ha : (p x y).contains a) :
    (q x y (carrierGridBinderApply r e he T h D B f x y)).contains (.app t a) :=
  ((hf.2 x).2 y).2 a ha

theorem carrierGridBinderCandidate_lambda (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (p : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) → Candidate)
    (q : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) →
      (carrierGrid (r + 1) (e + 1)).El (B x) → Candidate)
    (f : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) →
      (carrierGrid (r + 1) (e + 1)).El (B x))
    (hC : SN C)
    (hb : ∀ x y a, (p x y).contains a → (q x y (f x y)).contains (subst 0 a b)) :
    (carrierGridBinderCandidate r e he T h D B p q
      (carrierGridBinderLambda r e he T h D B f)).contains (.lam C b) := by
  have hh (x : T.El) (y : (carrierGrid (r + 1) (e + 1)).El (D x)) :
      ((p x y).arrow (q x y (carrierGridBinderApply r e he T h D B
        (carrierGridBinderLambda r e he T h D B f) x y))).contains (.lam C b) := by
    rw [carrierGrid_binder_beta]
    exact Candidate.lambda _ _ hC (hb x y)
  have hsn : SN (.lam C b) := (hh T.point ((carrierGrid (r + 1) (e + 1)).point (D T.point))).1
  exact ⟨hsn, fun x => ⟨hsn, fun y => hh x y⟩⟩

/-- The candidate atom is carried along the small diagonal to every bottom
cell. Its data remain candidates; the code does not refer to its own universe. -/
def carrierGridCandidateCode : (r : Nat) → (carrierGrid r r).Code
  | 0 => Arity.prop
  | r + 1 => .small (carrierGridCandidateCode r)

def carrierGridCandidateRetraction : (r : Nat) →
    CarrierRetraction Candidate ((carrierGrid r r).El (carrierGridCandidateCode r))
  | 0 => CarrierRetraction.identity Candidate
  | r + 1 => carrierGridCandidateRetraction r

/-- A candidate family on any finite preceding telescope fits in the bottom
carrier using the already checked telescope abstraction. -/
noncomputable def carrierGridCandidateFamilyCode (r : Nat)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within r) :
    (carrierGrid (r + 1) (r + 1)).Code :=
  carrierGridTelescopeCode r r (Nat.lt_succ_self r) T h (fun _ => carrierGridCandidateCode (r + 1))

noncomputable def carrierGridCandidateFamilyRetraction (r : Nat)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within r) :
    CarrierRetraction (T.El → Candidate)
      ((carrierGrid (r + 1) (r + 1)).El (carrierGridCandidateFamilyCode r T h)) :=
  (CarrierRetraction.pi (CarrierRetraction.identity T.El) (fun _ => Candidate)
    (fun _ => (carrierGrid (r + 1) (r + 1)).El (carrierGridCandidateCode (r + 1)))
    (fun _ => carrierGridCandidateRetraction (r + 1))).comp
      (carrierGridTelescopeRetraction r r (Nat.lt_succ_self r) T h (fun _ => carrierGridCandidateCode (r + 1)))

theorem carrierGrid_candidate_family_roundtrip (r : Nat)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within r) (C : T.El → Candidate) :
    (carrierGridCandidateFamilyRetraction r T h).decode
      ((carrierGridCandidateFamilyRetraction r T h).encode C) = C :=
  (carrierGridCandidateFamilyRetraction r T h).roundtrip C

end Submission.Helpers
