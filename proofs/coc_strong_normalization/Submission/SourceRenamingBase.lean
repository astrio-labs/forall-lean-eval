import Submission.SourceRenamingStep

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem chosenProduct_arity_components (h : BoundedTyping n Γ f (.pi A B))
    (hq : sortRank q + 1 = n) :
    arityAt q (chosenProduct n Γ f).1 = arityAt q A ∧
      arityAt q (chosenProduct n Γ f).2 = arityAt q B := by
  obtain ⟨s, hPi⟩ := h.pi_type
  obtain ⟨s', hPi'⟩ := (chosenProduct_typing h).pi_type
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  obtain ⟨sA', hA', _⟩ := hPi'.pi_domain
  obtain ⟨sB', hB', _⟩ := hPi'.pi_codomain
  exact ⟨arityAt_conv (hA'.goodAt hq) (hA.goodAt hq) (chosenProduct_conv h).1,
    arityAt_conv (hB'.goodAt hq) (hB.goodAt hq) (chosenProduct_conv h).2⟩

/-- The first source renaming frontier is constructed uniformly. Its
admissibility predicate is True because coordinate zero reads only arities. -/
def sourceRenamingBase (r : Nat) : SourceRenamingFrontier r 1 where
  admissible _ _ := True
  depth := by omega
  extend := by intros; trivial
  inferred := by
    intro Γ Δ t T ι ρ δ h hw hr hρ hδ he j hj hjd v hv
    have hjz : j = 0 := by omega
    subst j
    rw [sourceGridInterpretation_zero, sourceGridInterpretation_zero]
    exact inferredArityAt_ren h hw hr rfl
  types := by
    intro Γ Δ A s ι ρ δ h hw hr hρ hδ he j hj hjd v hv
    have hjz : j = 0 := by omega
    subst j
    rw [sourceGridInterpretation_zero, sourceGridInterpretation_zero]
    exact arityAt_ren _ _ _
  domain := by
    intro Γ Δ f A B ι ρ δ h hw hr hρ hδ he j hj hjd v hv
    have hjz : j = 0 := by omega
    subst j
    rw [sourceGridInterpretation_zero, sourceGridInterpretation_zero]
    exact ((chosenProduct_arity_components (h.rename hw hr) rfl).1).trans
      ((arityAt_ren _ _ _).trans (chosenProduct_arity_components h rfl).1.symm)
  codomain := by
    intro Γ Δ f A B ι ρ δ h hw hr hρ hδ he x hx j hj hjd v hv
    have hjz : j = 0 := by omega
    subst j
    rw [sourceGridInterpretation_zero, sourceGridInterpretation_zero]
    exact ((chosenProduct_arity_components (h.rename hw hr) rfl).2).trans
      ((arityAt_ren _ _ _).trans (chosenProduct_arity_components h rfl).2.symm)

/-- Actual typed renaming of the first value coordinate, at every finite
source bound. No interpretation or normalization premise remains. -/
theorem sourceGridEval_rename_zero (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (he : GridEnvironment.RenamedBelow 1 Γ ι ρ δ) :
    sourceGridEval r Δ δ (ren ι t) ⟨0, by omega⟩ = sourceGridEval r Γ ρ t ⟨0, by omega⟩ :=
  (sourceGrid_rename_stage (sourceRenamingBase r) h hw hr trivial trivial he).1 ⟨0, by omega⟩ (Nat.zero_lt_succ 0)

/-- Typed renaming preserves the first two type-carrier coordinates. This
is the first concrete successor instance of the uniform transport theorem. -/
theorem sourceGridInterpretation_rename_prefix (h : BoundedTyping (r + 2) Γ A (.srt s))
    (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    {ρ δ : GridEnvironment (r + 1)} (he : GridEnvironment.RenamedBelow 1 Γ ι ρ δ) :
    FiniteGridCodeEqBelow 2 (sourceGridInterpretation r Δ δ (ren ι A))
      (sourceGridInterpretation r Γ ρ A) :=
  ((sourceGrid_rename_stage (sourceRenamingBase r) h hw hr trivial trivial he).2 s h).code

end Submission.Helpers
