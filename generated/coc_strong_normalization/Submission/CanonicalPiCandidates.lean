import Submission.DecodedUniverseTypes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem FiniteGridType.sort_canonicalCandidate (R : Nat) (s : Srt) (v : FiniteGridValue R) :
    (FiniteGridType.sort R s).canonicalCandidate v = Candidate.sn := rfl

/-- Canonical candidates satisfy the exact dependent product equation on
valid function values. The codomain application is valid by construction. -/
theorem finitePiType_canonical_product (r : Nat) (A : FiniteGridType (r + 1))
    (B : FiniteGridFamily (r + 1)) (f : FiniteGridValue (r + 1))
    (hf : (finitePiType r A B).Valid f) :
    (finitePiType r A B).canonicalCandidate f =
      Candidate.inter (fun x : {a // A.Valid a} =>
        (A.canonicalCandidate x.1).arrow
          ((B.fiber x.1).canonicalCandidate (finiteTypeApplication r A B f x.1))) := by
  rw [(finitePiType r A B).canonicalCandidate_eq f hf]
  change Candidate.inter _ = Candidate.inter _
  apply congrArg Candidate.inter
  funext x
  rw [A.canonicalCandidate_eq x.1 x.2,
    (B.fiber x.1).canonicalCandidate_eq _ (finiteTypeApplication_valid r A B f x.1 x.2)]

theorem finitePiType_canonical_apply (r : Nat) (A : FiniteGridType (r + 1))
    (B : FiniteGridFamily (r + 1)) (f x : FiniteGridValue (r + 1))
    (hf : (finitePiType r A B).Valid f) (hx : A.Valid x)
    (ht : ((finitePiType r A B).canonicalCandidate f).contains t)
    (ha : (A.canonicalCandidate x).contains a) :
    ((B.fiber x).canonicalCandidate (finiteTypeApplication r A B f x)).contains (.app t a) := by
  rw [finitePiType_canonical_product r A B f hf] at ht
  exact (ht.2 ⟨x, hx⟩).2 a ha

theorem finitePiType_canonical_lambda (r : Nat) (A : FiniteGridType (r + 1))
    (B : FiniteGridFamily (r + 1)) (F : FiniteGridMap (r + 1))
    (hF : ∀ a, A.Valid a → (B.fiber a).Valid (F.eval a)) (hD : SN D)
    (hb : ∀ x, A.Valid x → ∀ a, (A.canonicalCandidate x).contains a →
      ((B.fiber x).canonicalCandidate (F.eval x)).contains (subst 0 a b)) :
    ((finitePiType r A B).canonicalCandidate (finiteTypeLambda r A B F)).contains (.lam D b) := by
  rw [(finitePiType r A B).canonicalCandidate_eq _ (finiteTypeLambda_valid r A B F)]
  apply finitePiType_candidate_lambda r A B F hF hD
  intro x hx a ha
  have hh := hb x hx a
  rw [A.canonicalCandidate_eq x hx, (B.fiber x).canonicalCandidate_eq _ (hF x hx)] at hh
  exact hh ha

end Submission.Helpers
