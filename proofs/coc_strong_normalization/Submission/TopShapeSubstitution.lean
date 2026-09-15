import Submission.TopShapeSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Interpretation commutes with every bounded, well-typed substitution. -/
theorem shapeEval_substitute (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ σ) (hk : ∀ j, kindAt (.type i) (σ j) = false)
    (hq : sortRank (.type i) + 1 = n) :
    shapeEval n i Δ ρ (sub σ t) = shapeEval n i Γ (shapeSub n i Δ ρ σ) t := by
  have hup {σ : Nat → Tm} (hk : ∀ j, kindAt (.type i) (σ j) = false) :
      ∀ j, kindAt (.type i) (upSub σ j) = false := by
    intro j
    cases j with
    | zero => rfl
    | succ j => exact (kindAt_ren _ _ _).trans (hk j)
  induction t generalizing Γ A Δ σ ρ with
  | var j => rfl
  | srt s =>
    have hi := inferredArityAt_substitute h hw hσ hk hq
    simp only [sub] at hi
    simp only [sub, shapeEval, hi]
  | app f a ihf iha =>
    obtain ⟨B, C, hf, ha, hc⟩ := h.generation
    simp only [sub, shapeEval, ihf hf hw hσ hk, iha ha hw hσ hk]
  | lam B b ihB ihb =>
    obtain ⟨C, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sB, hB, _⟩ := hPi.pi_domain
    have hB' := hB.substitute hw hσ
    have hbc := inferredArityAt_substitute hb (.cons hw hB')
      (hσ.up hw hB') (hup hk) hq
    have hbe (x : ShapeValue) :
        shapeEval n i (sub σ B :: Δ) (push x ρ) (sub (upSub σ) b) =
          shapeEval n i (B :: Γ) (push x (shapeSub n i Δ ρ σ)) b := by
      rw [ihb hb (.cons hw hB') (hσ.up hw hB') (hup hk)]
      apply shapeEval_env hb
      intro j C hj
      exact shapeSub_up hw hσ hB hq j ⟨C, hj⟩
    simp only [sub, shapeEval, arityAt_sub hk, hbc]
    apply ShapeValue.lambda_congr
    intro x hx
    exact hbe x
  | pi B C ihB ihC =>
    obtain ⟨s₁, s₂, s₃, hB, hC, hrule, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have hB' := hB.substitute hw hσ
    have hi := inferredArityAt_substitute h hw hσ hk hq
    have hCe :
        shapeEval n i (sub σ B :: Δ) (push .unit ρ) (sub (upSub σ) C) =
          shapeEval n i (B :: Γ) (push .unit (shapeSub n i Δ ρ σ)) C := by
      rw [ihC hC (.cons hw hB') (hσ.up hw hB') (hup hk)]
      apply shapeEval_env hC
      intro j D hj
      exact shapeSub_up hw hσ hB hq j ⟨D, hj⟩
    simp only [sub] at hi ⊢
    rw [shapeEval, shapeEval, hi, ihB hB hw hσ hk, hCe]

theorem ShapeContext.substitute (hρ : ShapeContext (.type i) Δ ρ)
    (hσ : BoundedSubCtx n Γ Δ σ)
    (hk : ∀ j, kindAt (.type i) (σ j) = false) (hq : sortRank (.type i) + 1 = n) :
    ShapeContext (.type i) Γ (shapeSub n i Δ ρ σ) := by
  intro j A hj
  change (shapeEval n i Δ ρ (σ j)).code = arityAt (.type i) A
  rw [shapeEval_typed_code (hσ j A hj) hq hρ, arityAt_sub hk,
    ← ren_shift, arityAt_ren]

theorem shapeSub_single (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue) (a : Tm) :
    shapeSub n i Γ ρ (single a) = push (shapeEval n i Γ ρ a) ρ := by
  funext j
  cases j <;> rfl

theorem shapeEval_subst (hb : BoundedTyping n (A :: Γ) b B)
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt s))
    (hq : sortRank (.type i) + 1 = n) :
    shapeEval n i Γ ρ (subst 0 a b) =
      shapeEval n i (A :: Γ) (push (shapeEval n i Γ ρ a) ρ) b := by
  rw [subst_eq_sub, shapeEval_substitute hb ha.wf (.single ha) ?_ hq, shapeSub_single]
  intro j
  cases j with
  | zero => exact ha.not_kindAt hA hq
  | succ => rfl

theorem shapeEval_context (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ Tm.var) (hq : sortRank (.type i) + 1 = n) :
    shapeEval n i Δ ρ t = shapeEval n i Γ ρ t := by
  have he := shapeEval_substitute (ρ := ρ) h hw hσ (fun _ => rfl) hq
  rw [sub_var] at he
  exact he

theorem inferredArityAt_context (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ Tm.var) (hq : sortRank q + 1 = n) :
    inferredArityAt n q Δ t = inferredArityAt n q Γ t := by
  have h' : BoundedTyping n Δ t A := by simpa only [sub_var] using h.substitute hw hσ
  rw [inferredArityAt_eq h' hq, inferredArityAt_eq h hq]

theorem shapeEval_context_conversion (hb : BoundedTyping n (A :: Γ) b B)
    (hA : BoundedTyping n Γ A (.srt s)) (hA' : BoundedTyping n Γ A' (.srt s'))
    (hs : sortRank s ≤ n) (hc : Conv A A') (hq : sortRank (.type i) + 1 = n) :
    shapeEval n i (A' :: Γ) ρ b = shapeEval n i (A :: Γ) ρ b :=
  shapeEval_context hb (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hs hc) hq

end Submission.Helpers
