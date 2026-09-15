import Submission.SourceContextFirst

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem BoundedSubCtx.convert_head (hA : BoundedTyping n Γ A (.srt s))
    (hA' : BoundedTyping n Γ A' (.srt s')) (hc : Conv A A') :
    BoundedSubCtx n (A :: Γ) (A' :: Γ) Tm.var := by
  intro i C hi
  rw [sub_var]
  exact (BoundedTyping.var (.cons hA.wf hA) hi).context_conv hA hA' hA.sort_bound hc

/-- Conversion of a context declaration is semantic transport at the first
stage, obtained from the actual typed substitution theorem. -/
theorem sourceGrid_context_conversion_first (ht : BoundedTyping (r + 2) (A :: Γ) t T)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hA' : BoundedTyping (r + 2) Γ A' (.srt s'))
    (hc : Conv A A') (hρ : SourceGridContextFirst r (A' :: Γ) ρ) :
    FiniteGridValue.Agree 1 (sourceGridEval r (A' :: Γ) ρ t) (sourceGridEval r (A :: Γ) ρ t) ∧
    (∀ q, BoundedTyping (r + 2) (A :: Γ) t (.srt q) →
      SourceTypeEqPrefix 1 (sourceGridInterpretation r (A' :: Γ) ρ t) (sourceGridInterpretation r (A :: Γ) ρ t)) := by
  have he : GridEnvironment.SubstitutedFirst r (A :: Γ) (A' :: Γ) Tm.var ρ ρ := by
    intro i C hi
    apply FiniteGridValue.agree_one
    cases i with
    | zero => exact hρ.variable (.cons hA'.wf hA') (A := A') rfl
    | succ i => exact hρ.variable (.cons hA'.wf hA') hi
  simpa only [sub_var] using sourceGrid_substitute_first ht (.cons hA'.wf hA')
    (BoundedSubCtx.convert_head hA hA' hc) (fun _ => rfl) he

theorem sourceTypeEqPrefix_of_eval_first (hA : BoundedTyping (r + 2) Γ A (.srt s))
    (hB : BoundedTyping (r + 2) Γ B (.srt s)) (hs : sortRank s ≤ r + 1)
    (ρ : GridEnvironment (r + 1))
    (he : FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ A) (sourceGridEval r Γ ρ B)) :
    SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) :=
  ((sourceGridInterpretation_decode_first hA hs ρ).trans
    (sourceTypeEqPrefix_decode (r + 1) 1 (some s) _ _ he)).trans
      (sourceGridInterpretation_decode_first hB hs ρ).symm

theorem sourceGridInferred_step_first (h : BoundedTyping (r + 2) Γ t T) (hs : Step t u)
    (ρ : GridEnvironment (r + 1)) :
    FiniteGridCodeEqBelow 1 (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t))
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ u)) :=
  sourceGridCode_first_of_arity r Γ Γ ρ ρ _ _ (inferredArityAt_step h hs rfl).symm

end Submission.Helpers
