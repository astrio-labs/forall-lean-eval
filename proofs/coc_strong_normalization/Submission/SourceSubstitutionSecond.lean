import Submission.SourceSubstitutionStep

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem GridEnvironment.SubstitutedFirst.up_arity (he : SubstitutedFirst r Γ Δ σ ρ δ)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (x : FiniteGridValue (r + 1))
    (hx : (x ⟨0, by omega⟩).code = arityAt (.type r) (sub σ A)) :
    SubstitutedFirst r (A :: Γ) (sub σ A :: Δ) (upSub σ) (push x ρ) (push x δ) := by
  have hA' := hA.substitute hw hσ
  intro j C hj
  apply FiniteGridValue.agree_one
  cases j with
  | zero => exact sourceGridEval_variable_zero (.cons hw hA') (j := 0) rfl (push x ρ) hx
  | succ j =>
    have hh := sourceGridEval_rename_zero (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A))
      (ρ := ρ) (δ := push x ρ) (by intro i D hi; exact FiniteGridValue.agree_one rfl)
    exact hh.trans (he j C hj ⟨0, by omega⟩ (Nat.zero_lt_succ 0))

theorem sourceGrid_type_substitute_first (h : FiberTypeExpression (r + 2) Γ A)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    {ρ δ : GridEnvironment (r + 1)} (he : GridEnvironment.SubstitutedFirst r Γ Δ σ δ ρ) :
    SourceTypeEqPrefix 1 (sourceGridInterpretation r Δ δ (sub σ A)) (sourceGridInterpretation r Γ ρ A) := by
  rcases h with ⟨s, hA⟩ | ⟨s, rfl⟩
  · exact (sourceGrid_substitute_first hA hw hσ hk he).2 s hA
  · apply SourceTypeEqPrefix.of_eq
    change sourceGridInterpretation r Δ δ (.srt s) = _
    rw [sourceGridInterpretation_sort, sourceGridInterpretation_sort]

theorem sourceGridInferred_substitute_second (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    {ρ δ : GridEnvironment (r + 1)} (hδ : SourceGridContextFirst r Δ δ)
    (he : GridEnvironment.SubstitutedFirst r Γ Δ σ δ ρ) :
    FiniteGridCodeEqBelow 2 (sourceGridInterpretation r Δ δ (chosenType (r + 2) Δ (sub σ t)))
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t)) := by
  have hOld := chosenType_typing h
  have hRen := hOld.substitute hw hσ
  have hNew := chosenType_typing (h.substitute hw hσ)
  have hConv := sourceGrid_type_conv_first hNew.type_expression hRen.type_expression hδ
    (typing_unique hNew.forget hRen.forget)
  exact (hConv.trans (sourceGrid_type_substitute_first hOld.type_expression hw hσ hk he)).code

theorem sourceGridProduct_substitute_second (h : BoundedTyping (r + 2) Γ f (.pi A B))
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    {ρ δ : GridEnvironment (r + 1)} (hδ : SourceGridContextFirst r Δ δ)
    (he : GridEnvironment.SubstitutedFirst r Γ Δ σ δ ρ) :
    FiniteGridCodeEqBelow 2
      (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (sub σ f)).1)
      (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1) ∧
    (∀ x, (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (sub σ f)).1).Valid x →
      FiniteGridCodeEqBelow 2
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
  have hDom := sourceGrid_type_conv_first (.inl ⟨sD', hD'⟩) (.inl ⟨sD, hDRen⟩) hδ hConv.1
  refine ⟨(hDom.trans (sourceGrid_type_substitute_first (.inl ⟨sD, hD⟩) hw hσ hk he)).code, ?_⟩
  intro x hx
  have hctx : SourceGridContextFirst r (D' :: Δ) (push x δ) := hδ.up (sourceGridValid_arity hx)
  have hCTrans := hCRen.context_conv hDRen hD' hDRen.sort_bound (conv_symm hConv.1)
  have hCod := sourceGrid_type_conv_first (.inl ⟨sC', hC'⟩) (.inl ⟨sC, hCTrans⟩) hctx hConv.2
  have hCtx := (sourceGrid_context_conversion_first hCRen hDRen hD' (conv_symm hConv.1) hctx).2 sC hCRen
  have hDarity : arityAt (.type r) D' = arityAt (.type r) (sub σ D) :=
    arityAt_conv (hD'.goodAt (q := .type r) rfl) (hDRen.goodAt (q := .type r) rfl) hConv.1
  have hRen := sourceGrid_type_substitute_first (.inl ⟨sC, hC⟩) (.cons hw hDRen) (hσ.up hw hDRen) (upSub_not_kindAt hk)
    (he.up_arity hw hσ hD x ((sourceGridValid_arity hx).trans hDarity))
  exact ((hCod.trans hCtx).trans hRen).code

/-- Every premise of the second substitution frontier follows from the
proved first conversion/substitution stage and the proved second renaming. -/
def sourceSubstitutionSecond (r : Nat) : SourceSubstitutionFrontier r 2 where
  admissible := SourceGridContextFirst r
  conversion := sourceCarrierConversionFirst r
  extend := by
    intro Γ ρ A s x hA hρ hx
    apply hρ.up
    have hc := hx 0 (Nat.zero_lt_succ _)
    rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hc
    exact hc
  rename_stage := fun h hw hr hρ hδ he => sourceGrid_rename_second h hw hr hρ hδ he
  inferred := by
    intro Γ Δ t T σ ρ δ h hw hσ hk hδ hρ he
    exact sourceGridInferred_substitute_second h hw hσ hk hρ (he.mono (by omega))
  types := by
    intro Γ Δ A s σ ρ δ h hw hσ hk hδ hρ he
    exact ((sourceGrid_substitute_first h hw hσ hk (he.mono (by omega))).2 s h).code
  domain := by
    intro Γ Δ f A B σ ρ δ h hw hσ hk hδ hρ he
    exact (sourceGridProduct_substitute_second h hw hσ hk hρ (he.mono (by omega))).1
  codomain := by
    intro Γ Δ f A B σ ρ δ h hw hσ hk hδ hρ he
    exact (sourceGridProduct_substitute_second h hw hσ hk hρ (he.mono (by omega))).2

/-- Simultaneous substitution preserves two value coordinates and three
carrier coordinates uniformly in the finite source bound. -/
theorem sourceGrid_substitute_second (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    (hδ : SourceGridContextFirst r Γ δ) (hρ : SourceGridContextFirst r Δ ρ)
    (he : GridEnvironment.SubstitutedBelow r 2 Γ Δ σ ρ δ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Δ ρ (sub σ t)) (sourceGridEval r Γ δ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix 2 (sourceGridInterpretation r Δ ρ (sub σ t)) (sourceGridInterpretation r Γ δ t)) :=
  sourceGrid_substitute_stage (sourceSubstitutionSecond r) h hw hσ hk hδ hρ he

end Submission.Helpers
