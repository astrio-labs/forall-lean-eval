import Submission.CoherentPiOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem Candidate.ext_contains (A B : Candidate) (h : ∀ t, A.contains t ↔ B.contains t) : A = B := by
  cases A
  cases B
  congr 1
  funext t
  exact propext (h t)

theorem finitePiType_candidate_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (f : FiniteGridValue (r + 1)) : (finitePiType r A B).candidate f = (finitePiType r A' B').candidate f := by
  have he (a : FiniteGridValue (r + 1)) (ha : A.Valid a) :
      (A.candidate a).arrow ((B.fiber a).candidate (finiteTypeApplication r A B f a)) =
        (A'.candidate a).arrow ((B'.fiber a).candidate (finiteTypeApplication r A' B' f a)) := by
    rw [hA.candidate a ha, (hB a ha).candidate _ (finiteTypeApplication_valid r A B f a ha),
      finiteTypeApplication_coherent_eq r A A' B B' hA hB f a]
  apply Candidate.ext_contains
  intro t
  constructor
  · intro ht
    refine ⟨ht.1, ?_⟩
    intro x
    have hx : A.Valid x.1 := (hA.valid_iff x.1).mpr x.2
    dsimp only
    rw [← he x.1 hx]
    exact ht.2 ⟨x.1, hx⟩
  · intro ht
    refine ⟨ht.1, ?_⟩
    intro x
    dsimp only
    rw [he x.1 x.2]
    exact ht.2 ⟨x.1, (hA.valid_iff x.1).mp x.2⟩

/-- Dependent products respect semantic equality on coherent data. Equality
of codomain types is required only at valid domain values, and the result
is equality of the whole Pi type, including its candidate function. -/
theorem finitePiType_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a)) :
    finitePiType r A B = finitePiType r A' B' := by
  apply FiniteGridType.ext_fields
  · exact finitePiType_carrier_coherent_eq r A A' B B' hA hB
  · exact finitePiType_candidate_coherent_eq r A A' B B' hA hB

end Submission.Helpers
