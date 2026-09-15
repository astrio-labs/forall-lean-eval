import Submission.SourceModel

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Strong normalization is uniform in every finite universe bound. -/
theorem bounded_normalization_uniform (h : BoundedTyping n Γ t A) : SN t := by
  by_cases hn : n ≤ 1
  · exact two_sort_normalization (h.mono hn)
  · obtain ⟨r, hr⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
    subst n
    exact sourceBoundedModel_normalization h

/-- Each finite derivation has a bound, so the concrete family of models
normalizes the full trusted calculus with its arbitrary universe hierarchy. -/
theorem typing_normalization_uniform (h : Typing Γ t A) : SN t :=
  normalization_of_bounded (fun _ _ _ _ ht => bounded_normalization_uniform ht) h

end Submission.Helpers
