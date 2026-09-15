import Submission.SourceGridCoherence

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def sourceGridApply (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A B : Tm) (f a : FiniteGridValue (r + 1)) : FiniteGridValue (r + 1) :=
  finiteTypeApplication r (sourceGridInterpretation r Γ ρ A)
    ((sourceGridMeaning r B).bodyFamily Γ ρ A) f a

theorem sourceGridApply_valid (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A B : Tm) (f a : FiniteGridValue (r + 1)) (ha : (sourceGridInterpretation r Γ ρ A).Valid a) :
    (sourceGridInterpretation r (A :: Γ) (push a ρ) B).Valid (sourceGridApply r Γ ρ A B f a) :=
  finiteTypeApplication_valid r _ _ f a ha

/-- The actual source interpretation has the dependent candidate equation
at its last stage. There is no assumed source product law in this proof. -/
theorem sourceGridInterpretation_pi_candidate (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A B : Tm) (f : FiniteGridValue (r + 1)) :
    (sourceGridInterpretation r Γ ρ (.pi A B)).candidate f =
      Candidate.inter (fun x : {a // (sourceGridInterpretation r Γ ρ A).Valid a} =>
        ((sourceGridInterpretation r Γ ρ A).candidate x.1).arrow
          ((sourceGridInterpretation r (A :: Γ) (push x.1 ρ) B).candidate
            (sourceGridApply r Γ ρ A B f x.1))) := by
  change (sourceGridUpgrade (r + 1) (r + 1)
    ((sourceGridStages r (r + 1) (by omega) (.pi A B)).interp Γ ρ)
    (finitePiType r (sourceGridInterpretation r Γ ρ A)
      ((sourceGridMeaning r B).bodyFamily Γ ρ A))).candidate f = _
  change ((if r + 1 = r + 1 then _ else _) : FiniteGridValue (r + 1) → Candidate) f = _
  rw [if_pos rfl]
  rfl

theorem sourceGridInterpretation_sort_candidate (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (s : Srt) (v : FiniteGridValue (r + 1)) :
    (sourceGridInterpretation r Γ ρ (.srt s)).candidate v = Candidate.sn := by
  change (sourceGridUpgrade (r + 1) (r + 1)
    ((sourceGridStages r (r + 1) (by omega) (.srt s)).interp Γ ρ) (FiniteGridType.sort (r + 1) s)).candidate v = _
  change ((if r + 1 = r + 1 then _ else _) : FiniteGridValue (r + 1) → Candidate) v = _
  rw [if_pos rfl]
  rfl

theorem sourceGridInterpretation_sort_canonical (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (s : Srt) (v : FiniteGridValue (r + 1)) :
    (sourceGridInterpretation r Γ ρ (.srt s)).canonicalCandidate v = Candidate.sn :=
  sourceGridInterpretation_sort_candidate r Γ ρ s _

/-- Canonicalization preserves the source product equation on valid function
values and yields the precise product field required by `BoundedModel`. -/
theorem sourceGridInterpretation_canonical_product (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1))
    (A B : Tm) (f : FiniteGridValue (r + 1)) (hf : (sourceGridInterpretation r Γ ρ (.pi A B)).Valid f) :
    (sourceGridInterpretation r Γ ρ (.pi A B)).canonicalCandidate f =
      Candidate.inter (fun x : {a // (sourceGridInterpretation r Γ ρ A).Valid a} =>
        ((sourceGridInterpretation r Γ ρ A).canonicalCandidate x.1).arrow
          ((sourceGridInterpretation r (A :: Γ) (push x.1 ρ) B).canonicalCandidate
            (sourceGridApply r Γ ρ A B f x.1))) := by
  rw [(sourceGridInterpretation r Γ ρ (.pi A B)).canonicalCandidate_eq f hf,
    sourceGridInterpretation_pi_candidate]
  apply congrArg Candidate.inter
  funext x
  rw [(sourceGridInterpretation r Γ ρ A).canonicalCandidate_eq x.1 x.2,
    (sourceGridInterpretation r (A :: Γ) (push x.1 ρ) B).canonicalCandidate_eq _
      (sourceGridApply_valid r Γ ρ A B f x.1 x.2)]

end Submission.Helpers
