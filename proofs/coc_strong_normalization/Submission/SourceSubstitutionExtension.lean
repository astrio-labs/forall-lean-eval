import Submission.SourceTypedPrefixes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Substitution environments extend by a partially coherent argument.
This is the form needed when preceding carrier conversion identifies
chosen and substituted domains only through the retained prefix. -/
theorem GridEnvironment.SubstitutedBelow.up_coherent (F : SourceSubstitutionFrontier r d)
    (he : SubstitutedBelow r d Γ Δ σ ρ δ)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hρ : F.admissible Δ ρ)
    (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).carrier.Coherent d F.conversion.depth
      (FiniteGridValue.toTower _ x)) :
    SubstitutedBelow r d (A :: Γ) (sub σ A :: Δ) (upSub σ) (push x ρ) (push x δ) := by
  have hA' := hA.substitute hw hσ
  have hctx := F.extend hA' hρ hx
  have hrel : GridEnvironment.RenamedBelow d Δ Nat.succ ρ (push x ρ) := by
    intro j C hj i hi
    rfl
  intro j C hj
  cases j with
  | zero =>
    have hv : BoundedTyping (r + 2) (sub σ A :: Δ) (.var 0) (lift 1 0 (sub σ A)) :=
      .var (.cons hw hA') rfl
    have hChosen := chosenType_typing hv
    have hEq := F.conversion.convert hChosen.type_expression hv.type_expression hctx
      (typing_unique hChosen.forget hv.forget)
    have hRen := (F.rename_stage hA' (.cons hw hA') (.weaken Δ (sub σ A)) hρ hctx hrel).2 s hA'
    have hCode : FiniteGridCodeEqBelow d
        (sourceGridInterpretation r (sub σ A :: Δ) (push x ρ) (chosenType (r + 2) (sub σ A :: Δ) (.var 0)))
        (sourceGridInterpretation r Δ ρ (sub σ A)) := by
      rw [← ren_shift] at hEq
      exact hEq.trans (hRen.code.mono (Nat.le_succ _))
    have hc := hCode.coherent_backward d F.conversion.depth (Nat.le_refl _) _
      hx
    change FiniteGridValue.Agree d (sourceGridEval r (sub σ A :: Δ) (push x ρ) (.var 0)) x
    rw [sourceGridEval_var_normalize]
    exact FiniteGridType.normalizeValue_recover_prefix _ d F.conversion.depth _ hc
  | succ j =>
    have hh := (F.rename_stage (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A)) hρ hctx hrel).1
    exact fun i hi => (hh i hi).trans (he j C hj i hi)

end Submission.Helpers
