import Submission.SourceReductionSecond

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Completed source laws at a retained depth. This is the induction
conclusion, not an assumption about normalization or reducibility. -/
structure SourceTransportStage (r d : Nat) : Prop where
  depth : d ≤ r + 2
  positive : 1 ≤ d
  extend : ∀ {Γ ρ A s x}, BoundedTyping (r + 2) Γ A (.srt s) → SourceGridCompatible r d Γ ρ →
    (sourceGridInterpretation r Γ ρ A).carrier.Coherent d depth (FiniteGridValue.toTower _ x) →
    SourceGridCompatible r d (A :: Γ) (push x ρ)
  rename_law : ∀ {Γ Δ t T ι ρ δ}, BoundedTyping (r + 2) Γ t T → BoundedWf (r + 2) Δ →
    RenCtx Γ Δ ι → SourceGridCompatible r d Γ ρ → SourceGridCompatible r d Δ δ →
    GridEnvironment.RenamedBelow d Γ ι ρ δ →
    FiniteGridValue.Agree d (sourceGridEval r Δ δ (ren ι t)) (sourceGridEval r Γ ρ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (ren ι t)) (sourceGridInterpretation r Γ ρ t))
  substitute_law : ∀ {Γ Δ t T σ ρ δ}, BoundedTyping (r + 2) Γ t T → BoundedWf (r + 2) Δ →
    BoundedSubCtx (r + 2) Γ Δ σ → (∀ j, kindAt (.type r) (σ j) = false) →
    SourceGridCompatible r d Γ δ → SourceGridCompatible r d Δ ρ →
    GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ →
    FiniteGridValue.Agree d (sourceGridEval r Δ ρ (sub σ t)) (sourceGridEval r Γ δ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix d (sourceGridInterpretation r Δ ρ (sub σ t)) (sourceGridInterpretation r Γ δ t))
  context_law : ∀ {Γ A A' t T s s' ρ}, BoundedTyping (r + 2) (A :: Γ) t T →
    BoundedTyping (r + 2) Γ A (.srt s) → BoundedTyping (r + 2) Γ A' (.srt s') →
    Conv A A' → SourceGridCompatible r d (A' :: Γ) ρ →
    FiniteGridValue.Agree d (sourceGridEval r (A' :: Γ) ρ t) (sourceGridEval r (A :: Γ) ρ t) ∧
    (∀ q, BoundedTyping (r + 2) (A :: Γ) t (.srt q) →
      SourceTypeEqPrefix d (sourceGridInterpretation r (A' :: Γ) ρ t) (sourceGridInterpretation r (A :: Γ) ρ t))
  conversion_law : ∀ {Γ A B ρ}, FiberTypeExpression (r + 2) Γ A →
    FiberTypeExpression (r + 2) Γ B → SourceGridCompatible r d Γ ρ → Conv A B →
    SourceTypeEqPrefix d (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B)

theorem sourceTransportStage_one (r : Nat) : SourceTransportStage r 1 where
  depth := by omega
  positive := by omega
  extend := by
    intro Γ ρ A s x hA hρ hx
    have hc := hx 0 (Nat.zero_lt_succ 0)
    rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hc
    have hfirst := hρ.first.up hc
    exact ⟨hfirst, fun j C hj => FiniteGridValue.agree_one (hfirst.variable (.cons hA.wf hA) hj)⟩
  rename_law := fun h hw hr hρ hδ he =>
    sourceGrid_rename_stage (sourceRenamingBase r) h hw hr trivial trivial he
  substitute_law := fun h hw hσ hk hδ hρ he => sourceGrid_substitute_first h hw hσ hk he
  context_law := fun ht hA hA' hc hρ => sourceGrid_context_conversion_first ht hA hA' hc hρ.first
  conversion_law := fun hA hB hρ hc => sourceGrid_type_conv_first hA hB hρ.first hc

theorem sourceTransportStage_two (r : Nat) : SourceTransportStage r 2 where
  depth := by omega
  positive := by omega
  extend := fun hA hρ hx => hρ.up_second hA hx
  rename_law := fun h hw hr hρ hδ he => sourceGrid_rename_second h hw hr hρ.first hδ.first he
  substitute_law := fun h hw hσ hk hδ hρ he => sourceGrid_substitute_second h hw hσ hk hδ.first hρ.first he
  context_law := fun ht hA hA' hc hρ => sourceGrid_context_conversion_second ht hA hA' hc hρ
  conversion_law := fun hA hB hρ hc => sourceGrid_type_conv_second hA hB hρ hc

end Submission.Helpers
