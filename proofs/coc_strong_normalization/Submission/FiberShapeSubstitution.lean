import Submission.FiberShape

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem fiberShape_ren (h : BoundedTyping n Γ A (.srt s)) (hw : BoundedWf n Δ)
    (hr : RenCtx Γ Δ r) (hq : sortRank (.type i) + 1 = n)
    (hρ : ∀ j, δ (r j) = ρ j) :
    fiberShape n i Δ δ (ren r A) v = fiberShape n i Γ ρ A v := by
  induction A generalizing Γ s Δ r ρ δ v
  all_goals
    have h' := h.rename hw hr
    apply fiberShape_compare h' h hq
      (congrArg ShapeValue.asArity (shapeEval_ren h hw hr hq hρ))
    intro hs
    rw [fiberShape_top h' hs hq, fiberShape_top h hs hq]
    try rfl
  case pi A B ihA ihB =>
    obtain ⟨sA, sB, sC, hA, hB, hrule, hsA, hsB, hsC, hc⟩ := h.generation
    have hA' := hA.rename hw hr
    apply fiberProduct_congr (arityAt_ren _ _ _)
    · intro x hx
      exact ihA hA hw hr hρ
    · intro x hx y
      apply ihB hB (.cons hw hA') (hr.up A)
      intro j
      cases j with
      | zero => rfl
      | succ j => exact hρ j

theorem fiberShape_env (h : BoundedTyping n Γ A (.srt s))
    (hq : sortRank (.type i) + 1 = n)
    (he : ∀ j B, Γ[j]? = some B → ρ j = δ j) :
    fiberShape n i Γ ρ A v = fiberShape n i Γ δ A v := by
  induction A generalizing Γ s ρ δ v
  all_goals
    apply fiberShape_compare h h hq
      (congrArg ShapeValue.asArity (shapeEval_env h he))
    intro hs
    rw [fiberShape_top h hs hq, fiberShape_top h hs hq]
    try rfl
  case pi A B ihA ihB =>
    obtain ⟨sA, sB, sC, hA, hB, hrule, hsA, hsB, hsC, hc⟩ := h.generation
    apply fiberProduct_congr rfl
    · intro x hx
      exact ihA hA he
    · intro x hx y
      apply ihB hB
      intro j C hj
      cases j with
      | zero => rfl
      | succ j => exact he j C hj

/-- Substituting a typed term also substitutes its upper semantic value in the fibre. -/
theorem fiberShape_substitute (h : BoundedTyping n Γ A (.srt s)) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ σ) (hk : ∀ j, kindAt (.type i) (σ j) = false)
    (hq : sortRank (.type i) + 1 = n) :
    fiberShape n i Δ ρ (sub σ A) v =
      fiberShape n i Γ (shapeSub n i Δ ρ σ) A v := by
  have hup {σ : Nat → Tm} (hk : ∀ j, kindAt (.type i) (σ j) = false) :
      ∀ j, kindAt (.type i) (upSub σ j) = false := by
    intro j
    cases j with
    | zero => rfl
    | succ j => exact (kindAt_ren _ _ _).trans (hk j)
  induction A generalizing Γ s Δ σ ρ v
  all_goals
    have h' := h.substitute hw hσ
    apply fiberShape_compare h' h hq
      (congrArg ShapeValue.asArity (shapeEval_substitute h hw hσ hk hq))
    intro hs
    rw [fiberShape_top h' hs hq, fiberShape_top h hs hq]
    try rfl
  case var j =>
    have hh := h.var_below_top
    omega
  case pi A B ihA ihB =>
    obtain ⟨sA, sB, sC, hA, hB, hrule, hsA, hsB, hsC, hc⟩ := h.generation
    have hA' := hA.substitute hw hσ
    apply fiberProduct_congr (arityAt_sub hk A)
    · intro x hx
      exact ihA hA hw hσ hk
    · intro x hx y
      rw [ihB hB (.cons hw hA') (hσ.up hw hA') (hup hk)]
      apply fiberShape_env hB hq
      intro j C hj
      exact shapeSub_up hw hσ hA hq j ⟨C, hj⟩

theorem fiberShape_subst (hB : BoundedTyping n (A :: Γ) B (.srt sB))
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt sA))
    (hq : sortRank (.type i) + 1 = n) :
    fiberShape n i Γ ρ (subst 0 a B) v =
      fiberShape n i (A :: Γ) (push (shapeEval n i Γ ρ a) ρ) B v := by
  rw [subst_eq_sub, fiberShape_substitute hB ha.wf (.single ha) ?_ hq, shapeSub_single]
  intro j
  cases j with
  | zero => exact ha.not_kindAt hA hq
  | succ => rfl

theorem fiberShape_context (h : BoundedTyping n Γ A (.srt s)) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ Tm.var) (hq : sortRank (.type i) + 1 = n) :
    fiberShape n i Δ ρ A v = fiberShape n i Γ ρ A v := by
  have he := fiberShape_substitute (ρ := ρ) (v := v) h hw hσ (fun _ => rfl) hq
  rw [sub_var] at he
  exact he

theorem fiberShape_context_conversion (hB : BoundedTyping n (A :: Γ) B (.srt sB))
    (hA : BoundedTyping n Γ A (.srt sA)) (hA' : BoundedTyping n Γ A' (.srt sA'))
    (hsA : sortRank sA ≤ n) (hc : Conv A A') (hq : sortRank (.type i) + 1 = n) :
    fiberShape n i (A' :: Γ) ρ B v = fiberShape n i (A :: Γ) ρ B v :=
  fiberShape_context hB (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hsA hc) hq

end Submission.Helpers
