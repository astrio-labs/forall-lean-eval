import Submission.MiddleShapeSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem middleShape_untypable_sort (hs : n ≤ sortRank s)
    (hq : sortRank (.type i) + 1 = n) :
    middleShape n i Γ ρ (.srt s) v = .small .unit := by
  classical
  have hnone (r : Srt) : typeSort n Γ (.srt s) ≠ some r := by
    intro h
    exact (typeSort_spec h).no_top_sort hs
  have hnl : ¬ ∃ r, typeSort n Γ (.srt s) = some r ∧
      sortRank r < sortRank (.type i) := by
    rintro ⟨r, hr, _⟩
    exact hnone r hr
  have hne : s ≠ .type i := by intro he; subst s; omega
  rw [middleShape_eq, if_neg (hnone _), if_neg hnl]
  exact if_neg hne

theorem inferredMiddle_ren (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hr : RenCtx Γ Δ r) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) (hδ : ShapeContext (.type i) Δ δ)
    (he : ∀ j, δ (r j) = ρ j) :
    inferredMiddle n i Δ δ (ren r t) = inferredMiddle n i Γ ρ t := by
  rw [inferredMiddle_eq (h.rename hw hr) hq hδ, inferredMiddle_eq h hq hρ,
    shapeEval_ren h hw hr hq he]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A
    rw [ren, middleShape_untypable_sort (Nat.le_of_eq hsn.symm) hq,
      middleShape_untypable_sort (Nat.le_of_eq hsn.symm) hq]
  · exact middleShape_ren hA hw hr hq he

theorem inferredMiddle_substitute (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ σ) (hk : ∀ j, kindAt (.type i) (σ j) = false)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Δ ρ) :
    inferredMiddle n i Δ ρ (sub σ t) =
      inferredMiddle n i Γ (shapeSub n i Δ ρ σ) t := by
  rw [inferredMiddle_eq (h.substitute hw hσ) hq hρ,
    inferredMiddle_eq h hq (hρ.substitute hσ hk hq), shapeEval_substitute h hw hσ hk hq]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A
    rw [sub, middleShape_untypable_sort (Nat.le_of_eq hsn.symm) hq,
      middleShape_untypable_sort (Nat.le_of_eq hsn.symm) hq]
  · exact middleShape_substitute hA hw hσ hk hq

theorem inferredMiddle_subst (hb : BoundedTyping n (A :: Γ) b B)
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt sA))
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    inferredMiddle n i Γ ρ (subst 0 a b) =
      inferredMiddle n i (A :: Γ) (push (shapeEval n i Γ ρ a) ρ) b := by
  rw [subst_eq_sub, inferredMiddle_substitute hb ha.wf (.single ha) ?_ hq hρ,
    shapeSub_single]
  intro j
  cases j with
  | zero => exact ha.not_kindAt hA hq
  | succ => rfl

theorem inferredMiddle_step (h : BoundedTyping n Γ t A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hs : Step t t') : inferredMiddle n i Γ ρ t = inferredMiddle n i Γ ρ t' := by
  rw [inferredMiddle_eq h hq hρ, inferredMiddle_eq (h.preservation hs) hq hρ,
    shapeEval_step h hq hρ hs]

theorem inferredMiddle_context (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ Tm.var) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Δ ρ) :
    inferredMiddle n i Δ ρ t = inferredMiddle n i Γ ρ t := by
  have he := inferredMiddle_substitute h hw hσ (fun _ => rfl) hq hρ
  rw [sub_var] at he
  exact he

/-- Lower values are indexed by the upper value of the same context entry. -/
def MiddleContext (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → MiddleValue) : Prop :=
  ∀ j A, Γ[j]? = some A →
    (δ j).code = middleShape n i Γ ρ (lift (j + 1) 0 A) (ρ j)

theorem MiddleContext.up (h : MiddleContext n i Γ ρ δ)
    (hA : BoundedTyping n Γ A (.srt s)) (hq : sortRank (.type i) + 1 = n)
    (hy : y.code = middleShape n i Γ ρ A x) :
    MiddleContext n i (A :: Γ) (push x ρ) (push y δ) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      middleShape_ren hA (.cons hA.wf hA) (.weaken Γ A) hq (fun _ => rfl)] using hy
  | succ j =>
    obtain ⟨r, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1),
      middleShape_ren hC (.cons hA.wf hA) (.weaken Γ A) hq (fun _ => rfl)] using h j C hj

theorem MiddleContext.var_code (h : MiddleContext n i Γ ρ δ)
    (hw : BoundedWf n Γ) (hj : Γ[j]? = some A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    (δ j).code = inferredMiddle n i Γ ρ (.var j) := by
  rw [inferredMiddle_eq (.var hw hj) hq hρ]
  exact h j A hj

end Submission.Helpers
