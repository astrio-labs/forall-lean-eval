import Submission.SourceReductionFirst

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem GridEnvironment.RenamedBelow.mono {ρ δ : GridEnvironment R}
    (h : RenamedBelow d Γ ι ρ δ) (hed : e ≤ d) : RenamedBelow e Γ ι ρ δ :=
  fun j A hj => (h j A hj).mono hed

theorem sourceGrid_type_rename_first (h : FiberTypeExpression (r + 2) Γ A)
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (he : GridEnvironment.RenamedBelow 1 Γ ι ρ δ) :
    SourceTypeEqPrefix 1 (sourceGridInterpretation r Δ δ (ren ι A)) (sourceGridInterpretation r Γ ρ A) := by
  rcases h with ⟨s, hA⟩ | ⟨s, rfl⟩
  · exact (sourceGrid_rename_stage (sourceRenamingBase r) hA hw hr trivial trivial he).2 s hA
  · apply SourceTypeEqPrefix.of_eq
    change sourceGridInterpretation r Δ δ (.srt s) = _
    rw [sourceGridInterpretation_sort, sourceGridInterpretation_sort]

theorem sourceGridInferred_rename_second (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (hδ : SourceGridContextFirst r Δ δ)
    (he : GridEnvironment.RenamedBelow 1 Γ ι ρ δ) :
    FiniteGridCodeEqBelow 2 (sourceGridInterpretation r Δ δ (chosenType (r + 2) Δ (ren ι t)))
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)) := by
  have hOld := chosenType_typing h
  have hRen := hOld.rename hw hr
  have hNew := chosenType_typing (h.rename hw hr)
  have hConv := sourceGrid_type_conv_first hNew.type_expression hRen.type_expression hδ
    (typing_unique hNew.forget hRen.forget)
  exact (hConv.trans (sourceGrid_type_rename_first hOld.type_expression hw hr he)).code

theorem sourceGridProduct_rename_second (h : BoundedTyping (r + 2) Γ f (.pi A B))
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (hδ : SourceGridContextFirst r Δ δ)
    (he : GridEnvironment.RenamedBelow 1 Γ ι ρ δ) :
    FiniteGridCodeEqBelow 2
      (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (ren ι f)).1)
      (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1) ∧
    (∀ x, (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (ren ι f)).1).Valid x →
      FiniteGridCodeEqBelow 2
        (sourceGridInterpretation r ((chosenProduct (r + 2) Δ (ren ι f)).1 :: Δ) (push x δ)
          (chosenProduct (r + 2) Δ (ren ι f)).2)
        (sourceGridInterpretation r ((chosenProduct (r + 2) Γ f).1 :: Γ) (push x ρ)
          (chosenProduct (r + 2) Γ f).2)) := by
  let D := (chosenProduct (r + 2) Γ f).1
  let C := (chosenProduct (r + 2) Γ f).2
  let D' := (chosenProduct (r + 2) Δ (ren ι f)).1
  let C' := (chosenProduct (r + 2) Δ (ren ι f)).2
  have hOld := chosenProduct_typing h
  have hNew := chosenProduct_typing (h.rename hw hr)
  obtain ⟨sPi, hPi⟩ := hOld.pi_type
  obtain ⟨sPi', hPi'⟩ := hNew.pi_type
  obtain ⟨sD, hD, _⟩ := hPi.pi_domain
  obtain ⟨sC, hC, _⟩ := hPi.pi_codomain
  obtain ⟨sD', hD', _⟩ := hPi'.pi_domain
  obtain ⟨sC', hC', _⟩ := hPi'.pi_codomain
  have hDRen : BoundedTyping (r + 2) Δ (ren ι D) (.srt sD) := hD.rename hw hr
  have hCRen : BoundedTyping (r + 2) (ren ι D :: Δ) (ren (upRen ι) C) (.srt sC) :=
    hC.rename (.cons hw hDRen) (hr.up D)
  have hConv : Conv D' (ren ι D) ∧ Conv C' (ren (upRen ι) C) := chosenProduct_conv (hOld.rename hw hr)
  have hDom := sourceGrid_type_conv_first (.inl ⟨sD', hD'⟩) (.inl ⟨sD, hDRen⟩) hδ hConv.1
  refine ⟨(hDom.trans (sourceGrid_type_rename_first (.inl ⟨sD, hD⟩) hw hr he)).code, ?_⟩
  intro x hx
  have hctx : SourceGridContextFirst r (D' :: Δ) (push x δ) := hδ.up (sourceGridValid_arity hx)
  have hCTrans := hCRen.context_conv hDRen hD' hDRen.sort_bound (conv_symm hConv.1)
  have hCod := sourceGrid_type_conv_first (.inl ⟨sC', hC'⟩) (.inl ⟨sC, hCTrans⟩) hctx hConv.2
  have hCtx := (sourceGrid_context_conversion_first hCRen hDRen hD' (conv_symm hConv.1) hctx).2 sC hCRen
  have hRen := sourceGrid_type_rename_first (.inl ⟨sC, hC⟩) (.cons hw hDRen) (hr.up D) (he.up D x)
  exact ((hCod.trans hCtx).trans hRen).code

/-- The second frontier is derived from actual source conversion and
renaming at the preceding stage. Its hypotheses contain no unproved law. -/
def sourceRenamingSecond (r : Nat) : SourceRenamingFrontier r 2 where
  admissible := SourceGridContextFirst r
  depth := by omega
  extend := by
    intro Γ ρ A s x hA hρ hx
    apply hρ.up
    have hc := hx 0 (Nat.zero_lt_succ _)
    rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hc
    exact hc
  inferred := by
    intro Γ Δ t T ι ρ δ h hw hr hρ hδ he
    exact sourceGridInferred_rename_second h hw hr hδ (he.mono (by omega))
  types := by
    intro Γ Δ A s ι ρ δ h hw hr hρ hδ he
    exact sourceGridInterpretation_rename_prefix h hw hr (he.mono (by omega))
  domain := by
    intro Γ Δ f A B ι ρ δ h hw hr hρ hδ he
    exact (sourceGridProduct_rename_second h hw hr hδ (he.mono (by omega))).1
  codomain := by
    intro Γ Δ f A B ι ρ δ h hw hr hρ hδ he
    exact (sourceGridProduct_rename_second h hw hr hδ (he.mono (by omega))).2

/-- Typed renaming now preserves two value coordinates and three carrier
coordinates at every finite source bound; at row one it also covers candidates. -/
theorem sourceGrid_rename_second (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (hρ : SourceGridContextFirst r Γ ρ) (hδ : SourceGridContextFirst r Δ δ)
    (he : GridEnvironment.RenamedBelow 2 Γ ι ρ δ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Δ δ (ren ι t)) (sourceGridEval r Γ ρ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix 2 (sourceGridInterpretation r Δ δ (ren ι t)) (sourceGridInterpretation r Γ ρ t)) :=
  sourceGrid_rename_stage (sourceRenamingSecond r) h hw hr hρ hδ he

end Submission.Helpers
