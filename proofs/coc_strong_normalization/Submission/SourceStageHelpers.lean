import Submission.SourceStageData

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem SourceTransportStage.type_rename (S : SourceTransportStage r d)
    (h : FiberTypeExpression (r + 2) Γ A) (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    (hρ : SourceGridCompatible r d Γ ρ) (hδ : SourceGridCompatible r d Δ δ)
    (he : GridEnvironment.RenamedBelow d Γ ι ρ δ) :
    SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (ren ι A)) (sourceGridInterpretation r Γ ρ A) := by
  rcases h with ⟨s, hA⟩ | ⟨s, rfl⟩
  · exact (S.rename_law hA hw hr hρ hδ he).2 s hA
  · apply SourceTypeEqPrefix.of_eq
    change sourceGridInterpretation r Δ δ (.srt s) = _
    rw [sourceGridInterpretation_sort, sourceGridInterpretation_sort]

theorem SourceTransportStage.type_substitute (S : SourceTransportStage r d)
    (h : FiberTypeExpression (r + 2) Γ A) (hw : BoundedWf (r + 2) Δ)
    (hσ : BoundedSubCtx (r + 2) Γ Δ σ) (hk : ∀ j, kindAt (.type r) (σ j) = false)
    (hδ : SourceGridCompatible r d Γ δ) (hρ : SourceGridCompatible r d Δ ρ)
    (he : GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ) :
    SourceTypeEqPrefix d (sourceGridInterpretation r Δ ρ (sub σ A)) (sourceGridInterpretation r Γ δ A) := by
  rcases h with ⟨s, hA⟩ | ⟨s, rfl⟩
  · exact (S.substitute_law hA hw hσ hk hδ hρ he).2 s hA
  · apply SourceTypeEqPrefix.of_eq
    change sourceGridInterpretation r Δ ρ (.srt s) = _
    rw [sourceGridInterpretation_sort, sourceGridInterpretation_sort]

theorem SourceTransportStage.context_compatible (S : SourceTransportStage r d)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hA' : BoundedTyping (r + 2) Γ A' (.srt s'))
    (hc : Conv A A') (hρ : SourceGridCompatible r d (A' :: Γ) ρ) :
    SourceGridCompatible r d (A :: Γ) ρ := by
  refine ⟨hρ.first.convert_head hA hA' hc, ?_⟩
  intro j C hj
  have hv : BoundedTyping (r + 2) (A :: Γ) (.var j) (lift (j + 1) 0 C) := .var (.cons hA.wf hA) hj
  have he := (S.context_law hv hA hA' hc hρ).1
  have ht : FiniteGridValue.Agree d (sourceGridEval r (A' :: Γ) ρ (.var j)) (ρ j) := by
    cases j with
    | zero => exact hρ.lookup 0 A' rfl
    | succ j => exact hρ.lookup (j + 1) C hj
  exact fun i hi => (he i hi).symm.trans (ht i hi)

theorem SourceTransportStage.typed_coherent (S : SourceTransportStage r d)
    (h : BoundedTyping (r + 2) Γ t A) (hρ : SourceGridCompatible r d Γ ρ) :
    (sourceGridInterpretation r Γ ρ A).carrier.Coherent d S.depth
      (FiniteGridValue.toTower _ (sourceGridEval r Γ ρ t)) := by
  have ht := chosenType_typing h
  have he := S.conversion_law ht.type_expression h.type_expression hρ (typing_unique ht.forget h.forget)
  exact he.code.coherent_forward d S.depth (by omega) _
    ((sourceGridEval_inferred r Γ ρ t).mono (hd := Nat.le_refl (r + 2)) S.depth)

theorem SourceTransportStage.substitution_up (S : SourceTransportStage r d)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hρ : SourceGridCompatible r d Δ ρ)
    (he : GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ)
    (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).carrier.Coherent d S.depth
      (FiniteGridValue.toTower _ x)) :
    GridEnvironment.SubstitutedBelow r d (A :: Γ) (sub σ A :: Δ) (upSub σ) (push x ρ) (push x δ) := by
  have hA' := hA.substitute hw hσ
  have hctx := S.extend hA' hρ hx
  intro j C hj
  cases j with
  | zero => exact hctx.lookup 0 (sub σ A) rfl
  | succ j =>
    have hh := (S.rename_law (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A)) hρ hctx
      (by intro k D hk i hi; rfl)).1
    exact fun i hi => (hh i hi).trans (he j C hj i hi)

theorem SourceTransportStage.single_substitution (S : SourceTransportStage r d)
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hA : BoundedTyping (r + 2) Γ A (.srt sA))
    (ha : BoundedTyping (r + 2) Γ a A) (hρ : SourceGridCompatible r d Γ ρ) :
    FiniteGridValue.Agree d (sourceGridEval r Γ ρ (subst 0 a b))
      (sourceGridEval r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b) ∧
    (∀ s, BoundedTyping (r + 2) (A :: Γ) b (.srt s) →
      SourceTypeEqPrefix d (sourceGridInterpretation r Γ ρ (subst 0 a b))
        (sourceGridInterpretation r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b)) := by
  rw [subst_eq_sub]
  apply S.substitute_law hb ha.wf (BoundedSubCtx.single ha)
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · exact S.extend hA hρ (S.typed_coherent ha hρ)
  · exact hρ
  · intro j C hj
    cases j with
    | zero => intro i hi; rfl
    | succ j => exact hρ.lookup j C hj

theorem SourceTransportStage.conversion_input (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) :
    SourceCarrierConversion r (d + 1) (SourceGridCompatible r d) where
  depth := hd
  convert := fun hA hB hρ hc => (S.conversion_law hA hB hρ hc).code

end Submission.Helpers
