import Submission.SourceStageHelpers

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem SourceTransportStage.inferred_rename_next (S : SourceTransportStage r d) (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (hρ : SourceGridCompatible r d Γ ρ)
    (hδ : SourceGridCompatible r d Δ δ)
    (he : GridEnvironment.RenamedBelow d Γ ι ρ δ) :
    FiniteGridCodeEqBelow (d + 1) (sourceGridInterpretation r Δ δ (chosenType (r + 2) Δ (ren ι t)))
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)) := by
  have hOld := chosenType_typing h
  have hRen := hOld.rename hw hr
  have hNew := chosenType_typing (h.rename hw hr)
  have hConv := S.conversion_law hNew.type_expression hRen.type_expression hδ
    (typing_unique hNew.forget hRen.forget)
  exact (hConv.trans (S.type_rename hOld.type_expression hw hr hρ hδ he)).code

theorem SourceTransportStage.product_rename_next (S : SourceTransportStage r d) (h : BoundedTyping (r + 2) Γ f (.pi A B))
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (hρ : SourceGridCompatible r d Γ ρ)
    (hδ : SourceGridCompatible r d Δ δ)
    (he : GridEnvironment.RenamedBelow d Γ ι ρ δ) :
    FiniteGridCodeEqBelow (d + 1)
      (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (ren ι f)).1)
      (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1) ∧
    (∀ x, (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (ren ι f)).1).Valid x →
      FiniteGridCodeEqBelow (d + 1)
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
  have hDom := S.conversion_law (.inl ⟨sD', hD'⟩) (.inl ⟨sD, hDRen⟩) hδ hConv.1
  have hTotal := hDom.trans (S.type_rename (.inl ⟨sD, hD⟩) hw hr hρ hδ he)
  refine ⟨hTotal.code, ?_⟩
  intro x hx
  have hxd := hx.mono (hd := Nat.le_refl (r + 2)) S.depth
  have hctx : SourceGridCompatible r d (D' :: Δ) (push x δ) := S.extend hD' hδ hxd
  have hctxRen := S.extend hDRen hδ (hDom.code.coherent_forward d S.depth (by omega) _ hxd)
  have hctxOld := S.extend hD hρ (hTotal.code.coherent_forward d S.depth (by omega) _ hxd)
  have hCTrans := hCRen.context_conv hDRen hD' hDRen.sort_bound (conv_symm hConv.1)
  have hCod := S.conversion_law (.inl ⟨sC', hC'⟩) (.inl ⟨sC, hCTrans⟩) hctx hConv.2
  have hCtx := (S.context_law hCRen hDRen hD' (conv_symm hConv.1) hctx).2 sC hCRen
  have hRen := S.type_rename (.inl ⟨sC, hC⟩) (.cons hw hDRen) (hr.up D) hctxOld hctxRen (he.up D x)
  exact ((hCod.trans hCtx).trans hRen).code

/-- Uniform construction of the next renaming frontier from a completed
preceding stage. Only preceding carrier coordinates are consumed. -/
def SourceTransportStage.renaming_frontier (S : SourceTransportStage r d)
    (hd : d + 1 ≤ r + 2) : SourceRenamingFrontier r (d + 1) where
  admissible := SourceGridCompatible r d
  depth := hd
  extend := fun hA hρ hx => S.extend hA hρ (hx.mono (Nat.le_succ d))
  inferred := fun h hw hr hρ hδ he => S.inferred_rename_next h hw hr hρ hδ (he.mono (Nat.le_succ d))
  types := fun h hw hr hρ hδ he => (S.rename_law h hw hr hρ hδ (he.mono (Nat.le_succ d))).2 _ h |>.code
  domain := fun h hw hr hρ hδ he => (S.product_rename_next h hw hr hρ hδ (he.mono (Nat.le_succ d))).1
  codomain := fun h hw hr hρ hδ he => (S.product_rename_next h hw hr hρ hδ (he.mono (Nat.le_succ d))).2

end Submission.Helpers
