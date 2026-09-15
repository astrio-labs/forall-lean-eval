import Submission.SourceStagesUniform

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem sourceGridEval_rename_full (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    (hρ : SourceGridCompatible r (r + 2) Γ ρ) (hδ : SourceGridCompatible r (r + 2) Δ δ)
    (he : GridEnvironment.RenamedBelow (r + 2) Γ ι ρ δ) :
    sourceGridEval r Δ δ (ren ι t) = sourceGridEval r Γ ρ t := by
  funext i
  exact ((sourceTransportStage_full r).rename_law h hw hr hρ hδ he).1 i i.isLt

theorem sourceGridEval_app_full (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (ha : BoundedTyping (r + 2) Γ a A) (hρ : SourceGridCompatible r (r + 2) Γ ρ) :
    sourceGridEval r Γ ρ (.app f a) =
      sourceGridApply r Γ ρ A B (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a) := by
  have S := sourceTransportStage_uniform r (r + 1) (by omega) (by omega)
  have he := S.app_typed_next (by omega) hf ha (hρ.mono (by omega))
  funext i
  exact he i i.isLt

theorem sourceGridEval_lam_full (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hρ : SourceGridCompatible r (r + 2) Γ ρ) :
    sourceGridEval r Γ ρ (.lam A b) =
      finiteTypeLambda r (sourceGridInterpretation r Γ ρ A) ((sourceGridMeaning r B).bodyFamily Γ ρ A)
        ((sourceGridMeaning r b).bodyMap Γ ρ A) := by
  have S := sourceTransportStage_uniform r (r + 1) (by omega) (by omega)
  have he := S.lam_typed_next (by omega) hPi hb (hρ.mono (by omega))
  funext i
  exact he i i.isLt

theorem sourceGrid_abstraction_full (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hρ : SourceGridCompatible r (r + 2) Γ ρ)
    (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :
    sourceGridApply r Γ ρ A B (sourceGridEval r Γ ρ (.lam A b)) x =
      sourceGridEval r (A :: Γ) (push x ρ) b := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  rw [sourceGridEval_lam_full hPi hb hρ]
  unfold sourceGridApply
  apply finiteTypeLambda_beta r _ _ _ _ x hx
  intro y hy
  exact sourceGridEval_typed_full hb ((sourceTransportStage_full r).extend hA hρ hy)

end Submission.Helpers
