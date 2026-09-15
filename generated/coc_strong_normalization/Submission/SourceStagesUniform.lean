import Submission.SourceReductionSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- The completed source stage advances uniformly. Every field is derived
from the preceding stage, including the new reduction/conversion boundary. -/
theorem SourceTransportStage.next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) :
    SourceTransportStage r (d + 1) where
  depth := hd
  positive := by omega
  extend := fun hA hρ hx => S.extend_next hd hA hρ hx
  rename_law := fun h hw hr hρ hδ he =>
    sourceGrid_rename_stage (S.renaming_frontier hd) h hw hr
      (hρ.mono (Nat.le_succ d)) (hδ.mono (Nat.le_succ d)) he
  substitute_law := fun h hw hσ hk hδ hρ he =>
    sourceGrid_substitute_stage (S.substitution_frontier hd) h hw hσ hk
      (hδ.mono (Nat.le_succ d)) (hρ.mono (Nat.le_succ d)) he
  context_law := fun ht hA hA' hc hρ => S.context_next hd ht hA hA' hc hρ
  conversion_law := fun hA hB hρ hc => S.conversion_next hd hA hB hρ hc

/-- Actual source transport stages exist at every retained depth and every
finite source bound. There is no residual frontier or normalization premise. -/
theorem sourceTransportStage_uniform (r d : Nat) (hp : 1 ≤ d) (hd : d ≤ r + 2) :
    SourceTransportStage r d := by
  revert hp hd
  induction d with
  | zero => intro hp hd; omega
  | succ d ih =>
    intro hp hd
    by_cases hz : d = 0
    · subst d
      exact sourceTransportStage_one r
    · exact (ih (by omega) (by omega)).next hd

theorem sourceTransportStage_full (r : Nat) : SourceTransportStage r (r + 2) :=
  sourceTransportStage_uniform r (r + 2) (by omega) (Nat.le_refl _)

theorem sourceGridEval_typed_full (h : BoundedTyping (r + 2) Γ t A)
    (hρ : SourceGridCompatible r (r + 2) Γ ρ) :
    (sourceGridInterpretation r Γ ρ A).Valid (sourceGridEval r Γ ρ t) :=
  (sourceTransportStage_full r).typed_coherent h hρ

theorem sourceGridInterpretation_rename_full (h : BoundedTyping (r + 2) Γ A (.srt s))
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    (hρ : SourceGridCompatible r (r + 2) Γ ρ) (hδ : SourceGridCompatible r (r + 2) Δ δ)
    (he : GridEnvironment.RenamedBelow (r + 2) Γ ι ρ δ) :
    FiniteGridTypeEq (sourceGridInterpretation r Δ δ (ren ι A)) (sourceGridInterpretation r Γ ρ A) :=
  ((sourceTransportStage_full r).rename_law h hw hr hρ hδ he).2 s h |>.full (Nat.le_refl _)

theorem sourceGridInterpretation_subst_full (hB : BoundedTyping (r + 2) (A :: Γ) B (.srt sB))
    (hA : BoundedTyping (r + 2) Γ A (.srt sA)) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridCompatible r (r + 2) Γ ρ) :
    FiniteGridTypeEq (sourceGridInterpretation r Γ ρ (subst 0 a B))
      (sourceGridInterpretation r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) B) :=
  ((sourceTransportStage_full r).single_substitution hB hA ha hρ).2 sB hB |>.full (Nat.le_refl _)

theorem sourceGridInterpretation_conv_full (hA : FiberTypeExpression (r + 2) Γ A)
    (hB : FiberTypeExpression (r + 2) Γ B) (hρ : SourceGridCompatible r (r + 2) Γ ρ) (hc : Conv A B) :
    FiniteGridTypeEq (sourceGridInterpretation r Γ ρ A) (sourceGridInterpretation r Γ ρ B) :=
  ((sourceTransportStage_full r).conversion_law hA hB hρ hc).full (Nat.le_refl _)

end Submission.Helpers
