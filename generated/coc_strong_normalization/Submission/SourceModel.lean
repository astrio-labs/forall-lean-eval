import Submission.SourceFullOperations
import Submission.BoundedModel

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Declared variables recover their supplied semantic entries. This is
inhabited even for arbitrary lists; typing supplies carrier compatibility. -/
def sourceModelAdmissible (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) : Prop :=
  ∀ j A, Γ[j]? = some A → sourceGridEval r Γ ρ (.var j) = ρ j

theorem sourceModelAdmissible_compatible (hw : BoundedWf (r + 2) Γ)
    (hρ : sourceModelAdmissible r Γ ρ) : SourceGridCompatible r (r + 2) Γ ρ := by
  constructor
  · intro j A hj
    have hv := sourceGridEval_arity (.var hw hj) ρ
    rw [hρ j A hj] at hv
    simpa only [← ren_shift, arityAt_ren] using hv
  · intro j A hj i hi
    exact congrFun (hρ j A hj) i

theorem sourceModelAdmissible_of_compatible (hρ : SourceGridCompatible r (r + 2) Γ ρ) :
    sourceModelAdmissible r Γ ρ := by
  intro j A hj
  funext i
  exact hρ.lookup j A hj i i.isLt

theorem sourceModel_environment (r : Nat) (Γ : List Tm) : ∃ ρ, sourceModelAdmissible r Γ ρ := by
  obtain ⟨ρ, hρ⟩ := sourceGrid_admissible_exists r Γ
  exact ⟨ρ, fun j A hj => sourceGridEval_variable r Γ ρ hρ j⟩

/-- A concrete model at every finite bound r+2. All interpretation fields
follow from the completed coordinate induction; no normalization is assumed. -/
noncomputable def sourceBoundedModel (r : Nat) : BoundedModel (r + 2) where
  Value := FiniteGridValue (r + 1)
  eval := sourceGridEval r
  candidate Γ ρ A := (sourceGridInterpretation r Γ ρ A).canonicalCandidate
  admissible := sourceModelAdmissible r
  valid Γ ρ A := (sourceGridInterpretation r Γ ρ A).Valid
  apply := sourceGridApply r
  environment := sourceModel_environment r
  point := by
    intro Γ ρ A s hA hρ
    let x : FiniteGridValue (r + 1) := FiniteGridValue.ofTower (r + 1) (TowerFamily.point (carrierGrid (r + 1)))
    exact ⟨(sourceGridInterpretation r Γ ρ A).normalizeValue x,
      (sourceGridInterpretation r Γ ρ A).normalizeValue_valid x⟩
  extend := by
    intro Γ ρ A s x hA hρ hx
    exact sourceModelAdmissible_of_compatible
      ((sourceTransportStage_full r).extend hA (sourceModelAdmissible_compatible hA.wf hρ) hx)
  typed := by
    intro Γ ρ t A h hρ
    exact sourceGridEval_typed_full h (sourceModelAdmissible_compatible h.wf hρ)
  variable_value := by
    intro Γ ρ j A hw hj hρ
    exact hρ j A hj
  sort := sourceGridInterpretation_sort_canonical r
  weaken := by
    intro Γ ρ A s C q x hA hC hρ hx
    have hctx := sourceModelAdmissible_compatible hA.wf hρ
    have hnew := (sourceTransportStage_full r).extend hA hctx hx
    exact (sourceGridInterpretation_rename_full hC (.cons hA.wf hA) (.weaken Γ A) hctx hnew
      (by intro j D hj i hi; rfl)).canonicalCandidate_eq
  product := by
    intro Γ ρ A B s f hPi hρ hf
    exact sourceGridInterpretation_canonical_product r Γ ρ A B f hf
  application := by
    intro Γ ρ f a A B hf ha hρ
    exact sourceGridEval_app_full hf ha (sourceModelAdmissible_compatible hf.wf hρ)
  abstraction := by
    intro Γ ρ A B b s x hPi hb hρ hx
    exact sourceGrid_abstraction_full hPi hb (sourceModelAdmissible_compatible hPi.wf hρ) hx
  substitution := by
    intro Γ ρ A B a sA sB hA hB ha hρ
    exact (sourceGridInterpretation_subst_full hB hA ha
      (sourceModelAdmissible_compatible hA.wf hρ)).canonicalCandidate_eq
  conversion := by
    intro Γ ρ t A B s ht hB hc hρ
    exact (sourceGridInterpretation_conv_full ht.type_expression (.inl ⟨s, hB⟩)
      (sourceModelAdmissible_compatible ht.wf hρ) hc).canonicalCandidate_eq

theorem sourceBoundedModel_fundamental (h : BoundedTyping (r + 2) Γ t A)
    (hρ : sourceModelAdmissible r Γ ρ) (hσ : (sourceBoundedModel r).RealizesContext Γ ρ σ) :
    ((sourceGridInterpretation r Γ ρ A).canonicalCandidate (sourceGridEval r Γ ρ t)).contains (sub σ t) :=
  bounded_model_fundamental (sourceBoundedModel r) h hρ hσ

theorem sourceBoundedModel_normalization (h : BoundedTyping (r + 2) Γ t A) : SN t :=
  bounded_model_normalization (sourceBoundedModel r) h

end Submission.Helpers
