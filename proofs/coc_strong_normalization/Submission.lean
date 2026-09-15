import Submission.UniformLiterals
import Submission.SourceNormalization
import Submission.UniverseValueConversion
import Submission.UniverseProducts
import Submission.ThirdGridInference
import Submission.ThirdTowerBridge
import Submission.ThirdModel
import ChallengeDeps
import Submission.Consistency
import Submission.DependentCandidates
import Submission.TwoSortNormalization
import Submission.UniverseSyntax
import Submission.UniverseCodes
import Submission.TopArity
import Submission.TopErasure
import Submission.TopSubstitution
import Submission.TopHeadNormalization
import Submission.RetentionNormalization
import Submission.FiberCandidates
import Submission.SortClassification
import Submission.FiberUniverse
import Submission.FiberApplication
import Submission.FiberNormalization
import Submission.TowerCandidates
import Submission.TowerRefinement
import Submission.BoundedModel
import Submission.FiberModel

namespace Submission

open _root_.LeanEval.ProgramVerification.CoCStrongNormalization

namespace LeanEval.ProgramVerification.CoCStrongNormalization

theorem typing_polyId :
    Typing [] (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
      (.pi (.srt .prop) (.pi (.var 0) (.var 1))) := by
  have h₀ : Typing [] (.srt .prop) (.srt (.type 0)) := .srt .nil .prop
  have w₁ : Wf [.srt .prop] := .cons .nil h₀
  have h₁ : Typing [.srt .prop] (.var 0) (.srt .prop) := .var (i := 0) (A := .srt .prop) w₁ rfl
  have w₂ : Wf [.var 0, .srt .prop] := .cons w₁ h₁
  have h₂ : Typing [.var 0, .srt .prop] (.var 1) (.srt .prop) := .var (i := 1) (A := .srt .prop) w₂ rfl
  have hx : Typing [.var 0, .srt .prop] (.var 0) (.var 1) := .var (i := 0) (A := .var 0) w₂ rfl
  have hp : Typing [.srt .prop] (.pi (.var 0) (.var 1)) (.srt .prop) :=
    .pi h₁ h₂ (.prop .prop)
  exact .lam (.pi h₀ hp (.prop (.type 0))) (.lam hp hx)

theorem typing_polyId_app :
    Typing []
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.pi (.pi (.srt .prop) (.var 0)) (.pi (.srt .prop) (.var 0))) := by
  have h₀ : Typing [] (.srt .prop) (.srt (.type 0)) := .srt .nil .prop
  have h₁ : Typing [.srt .prop] (.var 0) (.srt .prop) :=
    .var (i := 0) (A := .srt .prop) (.cons .nil h₀) rfl
  exact .app typing_polyId (.pi h₀ h₁ (.prop (.type 0)))

theorem step_polyId_app :
    Step
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.lam (.pi (.srt .prop) (.var 0)) (.var 0)) := by
  exact .beta _ _ _

theorem subject_reduction (Γ : List Tm) (t t' A : Tm) :
    Typing Γ t A → Step t t' → Typing Γ t' A := by
  exact Submission.Helpers.preservation

theorem strong_normalization (Γ : List Tm) (t A : Tm) :
    Typing Γ t A → SN t := by
  exact Submission.Helpers.typing_normalization_uniform

theorem consistency : ¬ ∃ t : Tm, Typing [] t (.pi (.srt .prop) (.var 0)) := by
  exact Submission.Helpers.consistency_of_normalization strong_normalization

end LeanEval.ProgramVerification.CoCStrongNormalization
end Submission
