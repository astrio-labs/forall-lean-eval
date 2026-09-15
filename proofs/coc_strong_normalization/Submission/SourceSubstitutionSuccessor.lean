import Submission.SourceRenamingSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem SourceTransportStage.inferred_substitute_next (S : SourceTransportStage r d) (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    {ρ δ : GridEnvironment (r + 1)} (hρ : SourceGridCompatible r d Γ ρ)
    (hδ : SourceGridCompatible r d Δ δ)
    (he : GridEnvironment.SubstitutedBelow r d Γ Δ σ δ ρ) :
    FiniteGridCodeEqBelow (d + 1) (sourceGridInterpretation r Δ δ (chosenType (r + 2) Δ (sub σ t)))
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)) := by
  have hOld := chosenType_typing h
  have hRen := hOld.substitute hw hσ
  have hNew := chosenType_typing (h.substitute hw hσ)
  have hConv := S.conversion_law hNew.type_expression hRen.type_expression hδ
    (typing_unique hNew.forget hRen.forget)
  exact (hConv.trans (S.type_substitute hOld.type_expression hw hσ hk hρ hδ he)).code

theorem SourceTransportStage.product_substitute_next (S : SourceTransportStage r d) (h : BoundedTyping (r + 2) Γ f (.pi A B))
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    {ρ δ : GridEnvironment (r + 1)} (hρ : SourceGridCompatible r d Γ ρ)
    (hδ : SourceGridCompatible r d Δ δ)
    (he : GridEnvironment.SubstitutedBelow r d Γ Δ σ δ ρ) :
    FiniteGridCodeEqBelow (d + 1)
      (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (sub σ f)).1)
      (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1) ∧
    (∀ x, (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (sub σ f)).1).Valid x →
      FiniteGridCodeEqBelow (d + 1)
        (sourceGridInterpretation r ((chosenProduct (r + 2) Δ (sub σ f)).1 :: Δ) (push x δ)
          (chosenProduct (r + 2) Δ (sub σ f)).2)
        (sourceGridInterpretation r ((chosenProduct (r + 2) Γ f).1 :: Γ) (push x ρ)
          (chosenProduct (r + 2) Γ f).2)) := by
  let D := (chosenProduct (r + 2) Γ f).1
  let C := (chosenProduct (r + 2) Γ f).2
  let D' := (chosenProduct (r + 2) Δ (sub σ f)).1
  let C' := (chosenProduct (r + 2) Δ (sub σ f)).2
  have hOld := chosenProduct_typing h
  have hNew := chosenProduct_typing (h.substitute hw hσ)
  obtain ⟨sPi, hPi⟩ := hOld.pi_type
  obtain ⟨sPi', hPi'⟩ := hNew.pi_type
  obtain ⟨sD, hD, _⟩ := hPi.pi_domain
  obtain ⟨sC, hC, _⟩ := hPi.pi_codomain
  obtain ⟨sD', hD', _⟩ := hPi'.pi_domain
  obtain ⟨sC', hC', _⟩ := hPi'.pi_codomain
  have hDRen : BoundedTyping (r + 2) Δ (sub σ D) (.srt sD) := hD.substitute hw hσ
  have hCRen : BoundedTyping (r + 2) (sub σ D :: Δ) (sub (upSub σ) C) (.srt sC) :=
    hC.substitute (.cons hw hDRen) (hσ.up hw hDRen)
  have hConv : Conv D' (sub σ D) ∧ Conv C' (sub (upSub σ) C) := chosenProduct_conv (hOld.substitute hw hσ)
  have hDom := S.conversion_law (.inl ⟨sD', hD'⟩) (.inl ⟨sD, hDRen⟩) hδ hConv.1
  have hTotal := hDom.trans (S.type_substitute (.inl ⟨sD, hD⟩) hw hσ hk hρ hδ he)
  refine ⟨hTotal.code, ?_⟩
  intro x hx
  have hxd := hx.mono (hd := Nat.le_refl (r + 2)) S.depth
  have hctx : SourceGridCompatible r d (D' :: Δ) (push x δ) := S.extend hD' hδ hxd
  have hxSub := hDom.code.coherent_forward d S.depth (by omega) _ hxd
  have hctxSub := S.extend hDRen hδ hxSub
  have hctxOld := S.extend hD hρ (hTotal.code.coherent_forward d S.depth (by omega) _ hxd)
  have hCTrans := hCRen.context_conv hDRen hD' hDRen.sort_bound (conv_symm hConv.1)
  have hCod := S.conversion_law (.inl ⟨sC', hC'⟩) (.inl ⟨sC, hCTrans⟩) hctx hConv.2
  have hCtx := (S.context_law hCRen hDRen hD' (conv_symm hConv.1) hctx).2 sC hCRen
  have hRen := S.type_substitute (.inl ⟨sC, hC⟩) (.cons hw hDRen) (hσ.up hw hDRen)
    (upSub_not_kindAt hk) hctxOld hctxSub (S.substitution_up hw hσ hD hδ he hxSub)
  exact ((hCod.trans hCtx).trans hRen).code

/-- Uniform construction of the next substitution frontier. Renaming at
this depth is already derived; the substitution carrier inputs come only
from the completed preceding stage. -/
def SourceTransportStage.substitution_frontier (S : SourceTransportStage r d)
    (hd : d + 1 ≤ r + 2) : SourceSubstitutionFrontier r (d + 1) where
  admissible := SourceGridCompatible r d
  conversion := S.conversion_input hd
  extend := fun hA hρ hx => S.extend hA hρ (hx.mono (Nat.le_succ d))
  rename_stage := fun h hw hr hρ hδ he =>
    sourceGrid_rename_stage (S.renaming_frontier hd) h hw hr hρ hδ he
  inferred := fun h hw hσ hk hδ hρ he =>
    S.inferred_substitute_next h hw hσ hk hδ hρ (he.mono (Nat.le_succ d))
  types := fun h hw hσ hk hδ hρ he =>
    (S.substitute_law h hw hσ hk hδ hρ (he.mono (Nat.le_succ d))).2 _ h |>.code
  domain := fun h hw hσ hk hδ hρ he =>
    (S.product_substitute_next h hw hσ hk hδ hρ (he.mono (Nat.le_succ d))).1
  codomain := fun h hw hσ hk hδ hρ he =>
    (S.product_substitute_next h hw hσ hk hδ hρ (he.mono (Nat.le_succ d))).2

end Submission.Helpers
