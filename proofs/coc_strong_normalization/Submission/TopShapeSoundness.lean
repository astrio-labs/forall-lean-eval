import Submission.TopShapeSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem shapeEval_beta (hPi : BoundedTyping n Γ (.pi A B) (.srt s))
    (hb : BoundedTyping n (A :: Γ) b B) (ha : BoundedTyping n Γ a A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    shapeEval n i Γ ρ (.app (.lam A b) a) = shapeEval n i Γ ρ (subst 0 a b) := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [shapeEval_subst hb ha hA hq]
  simp only [shapeEval]
  have hca := shapeEval_typed_code ha hq hρ
  apply ShapeValue.lambda_apply _ _ _ _ hca
  exact shapeEval_code hb hq (hρ.up hca)

/-- Well-typed beta reduction preserves the next-level shape interpretation. -/
theorem shapeEval_step (h : BoundedTyping n Γ t C)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hs : Step t u) : shapeEval n i Γ ρ t = shapeEval n i Γ ρ u := by
  induction hs generalizing Γ C ρ with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, hc⟩ := h.generation
    obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping n Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hconv).1) hsA
    exact shapeEval_beta hPi hb ha' hq hρ
  | appFun a hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    simp only [shapeEval, ih hf hρ]
  | appArg f hs ih =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    simp only [shapeEval, ih ha hρ]
  | @lamTy A A' b hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have hA' := hA.preservation hs
    have hconv : Conv A A' := .fwd (.refl _) hs
    have hb' := hb.context_conv hA hA' hsA hconv
    have hi := (inferredArityAt_eq hb' hq).trans (inferredArityAt_eq hb hq).symm
    have heA := (hA.goodAt hq).arity_step hs
    have heB (x : ShapeValue) := shapeEval_context_conversion (ρ := push x ρ)
      hb hA hA' hsA hconv hq
    simp only [shapeEval, hi, heA, heB]
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
    have hi := inferredArityAt_step hb hs hq
    simp only [shapeEval, hi]
    apply ShapeValue.lambda_congr
    intro x hx
    exact ih hb (hρ.up hx)
  | @piDom A A' B hs ih =>
    obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have hA' := hA.preservation hs
    have hi := inferredArityAt_step h (.piDom B hs) hq
    have heB := shapeEval_context_conversion (ρ := push .unit ρ)
      hB hA hA' hs₁ (.fwd (.refl _) hs) hq
    simp only [shapeEval, hi, ih hA hρ, heB]
  | @piCod A B B' hs ih =>
    obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have hi := inferredArityAt_step h (.piCod A hs) hq
    rw [shapeEval, shapeEval, hi]
    by_cases hp : inferredArityAt n (.type i) Γ (.pi A B) = .prop
    · have hPi := h.pi_of_base_arity hq hp
      have heA := hPi.top_pi_domain_unit hq
      have hx : ShapeValue.unit.code = arityAt (.type i) A := heA.symm
      rw [ih hB (hρ.up hx)]
    · simp only [ShapeValue.atBase, if_neg hp]

theorem shapeEval_steps (h : BoundedTyping n Γ t A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hs : Steps t u) : shapeEval n i Γ ρ t = shapeEval n i Γ ρ u := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact (shapeEval_step h hq hρ hs).trans (ih (h.preservation hs))

def ShapeTypedOrSort (n : Nat) (Γ : List Tm) (t : Tm) : Prop :=
  (∃ A, BoundedTyping n Γ t A) ∨ ∃ s, t = .srt s

theorem ShapeTypedOrSort.shapeEval_red (h : ShapeTypedOrSort n Γ t)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hr : Red t u) : shapeEval n i Γ ρ t = shapeEval n i Γ ρ u := by
  rcases h with ⟨A, ht⟩ | ⟨s, he⟩
  · exact shapeEval_steps ht hq hρ hr.steps
  · have he' := red_srt hr s he
    rw [he, he']

theorem shapeEval_conv (ht : ShapeTypedOrSort n Γ t) (hu : ShapeTypedOrSort n Γ u)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hc : Conv t u) : shapeEval n i Γ ρ t = shapeEval n i Γ ρ u := by
  obtain ⟨v, hv, hv'⟩ := conv_join hc
  exact (ht.shapeEval_red hq hρ hv).trans (hu.shapeEval_red hq hρ hv').symm

theorem type_shapeEval_conv (ht : BoundedTyping n Γ t A)
    (hB : BoundedTyping n Γ B (.srt s)) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) (hc : Conv A B) :
    shapeEval n i Γ ρ A = shapeEval n i Γ ρ B := by
  apply shapeEval_conv ?_ (.inl ⟨_, hB⟩) hq hρ hc
  rcases ht.regularity with hs | ⟨s, hA⟩
  · exact .inr hs
  · exact .inl ⟨_, hA⟩

/-- A conversion-invariant arity for the types one universe below the top. -/
noncomputable def nextArity (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue) (A : Tm) : Arity :=
  (shapeEval n i Γ ρ A).asArity

theorem nextArity_conv (ht : ShapeTypedOrSort n Γ A) (hu : ShapeTypedOrSort n Γ B)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hc : Conv A B) : nextArity n i Γ ρ A = nextArity n i Γ ρ B :=
  congrArg ShapeValue.asArity (shapeEval_conv ht hu hq hρ hc)

theorem nextArity_subst (hB : BoundedTyping n (A :: Γ) B C)
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt s))
    (hq : sortRank (.type i) + 1 = n) :
    nextArity n i Γ ρ (subst 0 a B) =
      nextArity n i (A :: Γ) (push (shapeEval n i Γ ρ a) ρ) B :=
  congrArg ShapeValue.asArity (shapeEval_subst hB ha hA hq)

theorem nextArity_pi (h : BoundedTyping n Γ (.pi A B) (.srt (.type i)))
    (hq : sortRank (.type i) + 1 = n) :
    nextArity n i Γ ρ (.pi A B) =
      (nextArity n i Γ ρ A).arrow (nextArity n i (A :: Γ) (push .unit ρ) B) := by
  have he : inferredArityAt n (.type i) Γ (.pi A B) = .prop := by
    rw [inferredArityAt_eq h hq]
    simp only [arityAt, ↓reduceIte]
  change (ShapeValue.atBase (inferredArityAt n (.type i) Γ (.pi A B))
    ((nextArity n i Γ ρ A).arrow
      (nextArity n i (A :: Γ) (push .unit ρ) B))).asArity = _
  rw [he]
  rfl

theorem nextArity_lower (h : BoundedTyping n Γ A (.srt s))
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hs : s ≠ .type i) : nextArity n i Γ ρ A = .unit := by
  have he := shapeEval_typed_code h hq hρ
  simp only [arityAt, if_neg hs] at he
  rw [nextArity, ShapeValue.eq_unit _ he]
  rfl

/-- Substitution into a product at this universe preserves the codomain's next arity. -/
theorem nextArity_small_subst (hPi : BoundedTyping n Γ (.pi A B) (.srt (.type i)))
    (ha : BoundedTyping n Γ a A) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) :
    nextArity n i Γ ρ (subst 0 a B) =
      nextArity n i (A :: Γ) (push .unit ρ) B := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  have hcode := (shapeEval_typed_code ha hq hρ).trans (hPi.top_pi_domain_unit hq)
  rw [nextArity_subst hB ha hA hq, ShapeValue.eq_unit _ hcode]

theorem nextArity_predecessor (hw : BoundedWf n Γ) (hs : Ax s (.type i))
    (hq : sortRank (.type i) + 1 = n) : nextArity n i Γ ρ (.srt s) = .prop := by
  have ht : BoundedTyping n Γ (.srt s) (.srt (.type i)) :=
    .srt hw hs (by have hh := ax_rank hs; omega) (by omega)
  have he : inferredArityAt n (.type i) Γ (.srt s) = .prop := by
    rw [inferredArityAt_eq ht hq]
    simp only [arityAt, ↓reduceIte]
  change (ShapeValue.atBase (inferredArityAt n (.type i) Γ (.srt s)) .prop).asArity = .prop
  rw [he]
  rfl

end Submission.Helpers
