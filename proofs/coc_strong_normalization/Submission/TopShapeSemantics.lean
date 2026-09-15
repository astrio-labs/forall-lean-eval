import Submission.TopShapeValues
import Submission.RetentionSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def ShapeValue.atBase (code value : Arity) : ShapeValue :=
  if code = .prop then .base value else .unit

theorem ShapeValue.atBase_code {code : Arity} (h : code = .unit ∨ code = .prop) (value : Arity) :
    (ShapeValue.atBase code value).code = code := by
  rcases h with h | h <;> subst code <;> rfl

theorem arityAt_sort_cases (q s : Srt) :
    arityAt q (.srt s) = .unit ∨ arityAt q (.srt s) = .prop := by
  by_cases h : s = q
  · exact .inr (by simp only [arityAt, h, ↓reduceIte])
  · exact .inl (by simp only [arityAt, if_neg h])

def ShapeContext (q : Srt) (Γ : List Tm) (ρ : Nat → ShapeValue) : Prop :=
  ∀ j A, Γ[j]? = some A → (ρ j).code = arityAt q A

theorem ShapeContext.up (h : ShapeContext q Γ ρ) (hx : x.code = arityAt q A) :
    ShapeContext q (A :: Γ) (push x ρ) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C; exact hx
  | succ j => exact h j C hj

/-- Interpret the shape of types in the next universe below the highest available one. -/
noncomputable def shapeEval (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue) : Tm → ShapeValue
  | .var j => ρ j
  | .srt s => .atBase (inferredArityAt n (.type i) Γ (.srt s)) .prop
  | .app f a => (shapeEval n i Γ ρ f).apply (shapeEval n i Γ ρ a)
  | .lam A b => .lambda (arityAt (.type i) A) (inferredArityAt n (.type i) (A :: Γ) b)
      (fun x => shapeEval n i (A :: Γ) (push x ρ) b)
  | .pi A B => .atBase (inferredArityAt n (.type i) Γ (.pi A B))
      ((shapeEval n i Γ ρ A).asArity.arrow
        (shapeEval n i (A :: Γ) (push .unit ρ) B).asArity)

theorem shapeEval_code (h : BoundedTyping n Γ t A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    (shapeEval n i Γ ρ t).code = inferredArityAt n (.type i) Γ t := by
  induction t generalizing Γ A ρ with
  | var j =>
    obtain ⟨B, hj, hc⟩ := h.generation
    rw [shapeEval, inferredArityAt_var h.wf hj hq]
    exact hρ j B hj
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping n Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    apply ShapeValue.atBase_code
    rw [inferredArityAt_eq ht hq]
    exact arityAt_sort_cases _ _
  | app f a ihf iha =>
    obtain ⟨B, C, hf, ha, hc⟩ := h.generation
    rw [shapeEval, ShapeValue.apply_code, ihf hf hρ, inferredArityAt_app hf ha hq]
  | lam B b ihB ihb =>
    obtain ⟨C, s, hPi, hb, hs, hc⟩ := h.generation
    rw [shapeEval, ShapeValue.lambda_code, inferredArityAt_lam hPi hb hq]
  | pi B C ihB ihC =>
    obtain ⟨s₁, s₂, s₃, hB, hC, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have ht : BoundedTyping n Γ (.pi B C) (.srt s₃) := .pi hB hC hr hs₁ hs₂ hs₃
    apply ShapeValue.atBase_code
    rw [inferredArityAt_eq ht hq]
    exact arityAt_sort_cases _ _

theorem shapeEval_typed_code (h : BoundedTyping n Γ t A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    (shapeEval n i Γ ρ t).code = arityAt (.type i) A :=
  (shapeEval_code h hq hρ).trans (inferredArityAt_eq h hq)

theorem BoundedTyping.pi_of_base_arity (h : BoundedTyping n Γ (.pi A B) C)
    (hq : sortRank q + 1 = n) (he : inferredArityAt n q Γ (.pi A B) = .prop) :
    BoundedTyping n Γ (.pi A B) (.srt q) := by
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
  have ht : BoundedTyping n Γ (.pi A B) (.srt s₃) := .pi hA hB hr hs₁ hs₂ hs₃
  rw [inferredArityAt_eq ht hq] at he
  by_cases hs : s₃ = q
  · subst s₃; exact ht
  · simp only [arityAt, if_neg hs] at he
    cases he

theorem shapeEval_ren (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hr : RenCtx Γ Δ r) (hq : sortRank (.type i) + 1 = n)
    (hρ : ∀ j, δ (r j) = ρ j) :
    shapeEval n i Δ δ (ren r t) = shapeEval n i Γ ρ t := by
  induction t generalizing Γ A Δ r ρ δ with
  | var j => exact hρ j
  | srt s =>
    have hi := inferredArityAt_ren h hw hr hq
    simp only [ren] at hi
    simp only [ren, shapeEval, hi]
  | app f a ihf iha =>
    obtain ⟨B, C, hf, ha, hc⟩ := h.generation
    simp only [ren, shapeEval, ihf hf hw hr hρ, iha ha hw hr hρ]
  | lam B b ihB ihb =>
    obtain ⟨C, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sB, hB, _⟩ := hPi.pi_domain
    have hB' := hB.rename hw hr
    have hbc := inferredArityAt_ren hb (.cons hw hB') (hr.up B) hq
    simp only [ren, shapeEval, arityAt_ren, hbc]
    apply ShapeValue.lambda_congr
    intro x hx
    apply ihb hb (.cons hw hB') (hr.up B)
    intro j
    cases j with
    | zero => rfl
    | succ j => exact hρ j
  | pi B C ihB ihC =>
    obtain ⟨s₁, s₂, s₃, hB, hC, hrule, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have hB' := hB.rename hw hr
    have hi := inferredArityAt_ren h hw hr hq
    simp only [ren] at hi ⊢
    rw [shapeEval, shapeEval, hi, ihB hB hw hr hρ]
    congr 2
    apply congrArg ShapeValue.asArity
    apply ihC hC (.cons hw hB') (hr.up B)
    intro j
    cases j with
    | zero => rfl
    | succ j => exact hρ j

noncomputable def shapeSub (n i : Nat) (Δ : List Tm) (ρ : Nat → ShapeValue)
    (σ : Nat → Tm) : Nat → ShapeValue := fun j => shapeEval n i Δ ρ (σ j)

theorem shapeSub_up (hw : BoundedWf n Δ) (hσ : BoundedSubCtx n Γ Δ σ)
    (hA : BoundedTyping n Γ A (.srt s)) (hq : sortRank (.type i) + 1 = n)
    (j : Nat) (hj : ∃ B, (A :: Γ)[j]? = some B) :
    shapeSub n i (sub σ A :: Δ) (push x ρ) (upSub σ) j =
      push x (shapeSub n i Δ ρ σ) j := by
  have hA' := hA.substitute hw hσ
  cases j with
  | zero => rfl
  | succ j =>
    obtain ⟨B, hj⟩ := hj
    exact shapeEval_ren (hσ j B hj) (.cons hw hA') (.weaken Δ (sub σ A)) hq (fun _ => rfl)

/-- Only variables declared in the source context affect the interpretation. -/
theorem shapeEval_env (h : BoundedTyping n Γ t A)
    (he : ∀ j B, Γ[j]? = some B → ρ j = δ j) :
    shapeEval n i Γ ρ t = shapeEval n i Γ δ t := by
  induction t generalizing Γ A ρ δ with
  | var j =>
    obtain ⟨B, hj, hc⟩ := h.generation
    exact he j B hj
  | srt => rfl
  | app f a ihf iha =>
    obtain ⟨B, C, hf, ha, hc⟩ := h.generation
    simp only [shapeEval, ihf hf he, iha ha he]
  | lam B b ihB ihb =>
    obtain ⟨C, s, hPi, hb, hs, hc⟩ := h.generation
    simp only [shapeEval]
    apply ShapeValue.lambda_congr
    intro x hx
    apply ihb hb
    intro j D hj
    cases j with
    | zero => rfl
    | succ j => exact he j D hj
  | pi B C ihB ihC =>
    obtain ⟨s₁, s₂, s₃, hB, hC, hrule, hs₁, hs₂, hs₃, hc⟩ := h.generation
    rw [shapeEval, shapeEval, ihB hB he]
    congr 2
    apply congrArg ShapeValue.asArity
    apply ihC hC
    intro j D hj
    cases j with
    | zero => rfl
    | succ j => exact he j D hj

end Submission.Helpers
