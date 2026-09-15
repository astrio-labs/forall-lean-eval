import Submission.SourceSubstitutionSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem SourceTransportStage.extend_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hρ : SourceGridCompatible r (d + 1) Γ ρ)
    (hx : (sourceGridInterpretation r Γ ρ A).carrier.Coherent (d + 1) hd
      (FiniteGridValue.toTower _ x)) : SourceGridCompatible r (d + 1) (A :: Γ) (push x ρ) :=
  hρ.up (S.substitution_frontier hd) (by omega) hA (hρ.mono (Nat.le_succ d)) hx

theorem SourceTransportStage.typed_coherent_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2)
    (h : BoundedTyping (r + 2) Γ t A) (hρ : SourceGridCompatible r d Γ ρ) :
    (sourceGridInterpretation r Γ ρ A).carrier.Coherent (d + 1) hd
      (FiniteGridValue.toTower _ (sourceGridEval r Γ ρ t)) :=
  sourceGridEval_coherent_of_conversion (S.conversion_input hd) h hρ

theorem SourceTransportStage.single_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2)
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hA : BoundedTyping (r + 2) Γ A (.srt sA))
    (ha : BoundedTyping (r + 2) Γ a A) (hρ : SourceGridCompatible r (d + 1) Γ ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (subst 0 a b))
      (sourceGridEval r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b) ∧
    (∀ s, BoundedTyping (r + 2) (A :: Γ) b (.srt s) →
      SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r Γ ρ (subst 0 a b))
        (sourceGridInterpretation r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b)) := by
  rw [subst_eq_sub]
  apply sourceGrid_substitute_stage (S.substitution_frontier hd) hb ha.wf (BoundedSubCtx.single ha)
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · exact S.extend hA (hρ.mono (Nat.le_succ d)) (S.typed_coherent ha (hρ.mono (Nat.le_succ d)))
  · exact hρ.mono (Nat.le_succ d)
  · intro j C hj
    cases j with
    | zero => intro i hi; rfl
    | succ j => exact hρ.lookup j C hj

/-- Context transport at the new stage uses identity substitution at that
stage, with admissibility transferred by the preceding context law. -/
theorem SourceTransportStage.context_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2)
    (ht : BoundedTyping (r + 2) (A :: Γ) t T)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hA' : BoundedTyping (r + 2) Γ A' (.srt s'))
    (hc : Conv A A') (hρ : SourceGridCompatible r (d + 1) (A' :: Γ) ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r (A' :: Γ) ρ t) (sourceGridEval r (A :: Γ) ρ t) ∧
    (∀ q, BoundedTyping (r + 2) (A :: Γ) t (.srt q) →
      SourceTypeEqPrefix (d + 1) (sourceGridInterpretation r (A' :: Γ) ρ t) (sourceGridInterpretation r (A :: Γ) ρ t)) := by
  have he : GridEnvironment.SubstitutedBelow r (d + 1) (A :: Γ) (A' :: Γ) Tm.var ρ ρ := by
    intro j C hj
    cases j with
    | zero => exact hρ.lookup 0 A' rfl
    | succ j => exact hρ.lookup (j + 1) C hj
  simpa only [sub_var] using sourceGrid_substitute_stage (S.substitution_frontier hd) ht (.cons hA'.wf hA')
    (BoundedSubCtx.convert_head hA hA' hc) (fun _ => rfl)
    (S.context_compatible hA hA' hc (hρ.mono (Nat.le_succ d))) (hρ.mono (Nat.le_succ d)) he

end Submission.Helpers
