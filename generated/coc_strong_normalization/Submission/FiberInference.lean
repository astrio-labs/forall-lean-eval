import Submission.FiberShapeSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem fiberShape_untypable_sort (hs : n ≤ sortRank s)
    (hq : sortRank (.type i) + 1 = n) :
    fiberShape n i Γ ρ (.srt s) v = .small .unit := by
  classical
  have hnone (r : Srt) : typeSort n Γ (.srt s) ≠ some r := by
    intro h
    exact (typeSort_spec h).no_top_sort hs
  have hnl : ¬ ∃ r, typeSort n Γ (.srt s) = some r ∧
      sortRank r < sortRank (.type i) := by
    rintro ⟨r, hr, _⟩
    exact hnone r hr
  have hne : s ≠ .type i := by intro he; subst s; omega
  rw [fiberShape_eq, if_neg (hnone _), if_neg hnl]
  exact if_neg hne

theorem inferredFiber_ren (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hr : RenCtx Γ Δ r) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) (hδ : ShapeContext (.type i) Δ δ)
    (he : ∀ j, δ (r j) = ρ j) :
    inferredFiber n i Δ δ (ren r t) = inferredFiber n i Γ ρ t := by
  rw [inferredFiber_eq (h.rename hw hr) hq hδ, inferredFiber_eq h hq hρ,
    shapeEval_ren h hw hr hq he]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A
    rw [ren, fiberShape_untypable_sort (Nat.le_of_eq hsn.symm) hq,
      fiberShape_untypable_sort (Nat.le_of_eq hsn.symm) hq]
  · exact fiberShape_ren hA hw hr hq he

theorem inferredFiber_substitute (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ σ) (hk : ∀ j, kindAt (.type i) (σ j) = false)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Δ ρ) :
    inferredFiber n i Δ ρ (sub σ t) =
      inferredFiber n i Γ (shapeSub n i Δ ρ σ) t := by
  rw [inferredFiber_eq (h.substitute hw hσ) hq hρ,
    inferredFiber_eq h hq (hρ.substitute hσ hk hq), shapeEval_substitute h hw hσ hk hq]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A
    rw [sub, fiberShape_untypable_sort (Nat.le_of_eq hsn.symm) hq,
      fiberShape_untypable_sort (Nat.le_of_eq hsn.symm) hq]
  · exact fiberShape_substitute hA hw hσ hk hq

theorem inferredFiber_subst (hb : BoundedTyping n (A :: Γ) b B)
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt sA))
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    inferredFiber n i Γ ρ (subst 0 a b) =
      inferredFiber n i (A :: Γ) (push (shapeEval n i Γ ρ a) ρ) b := by
  rw [subst_eq_sub, inferredFiber_substitute hb ha.wf (.single ha) ?_ hq hρ,
    shapeSub_single]
  intro j
  cases j with
  | zero => exact ha.not_kindAt hA hq
  | succ => rfl

theorem inferredFiber_step (h : BoundedTyping n Γ t A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ)
    (hs : Step t t') : inferredFiber n i Γ ρ t = inferredFiber n i Γ ρ t' := by
  rw [inferredFiber_eq h hq hρ, inferredFiber_eq (h.preservation hs) hq hρ,
    shapeEval_step h hq hρ hs]

theorem inferredFiber_context (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ Tm.var) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Δ ρ) :
    inferredFiber n i Δ ρ t = inferredFiber n i Γ ρ t := by
  have he := inferredFiber_substitute h hw hσ (fun _ => rfl) hq hρ
  rw [sub_var] at he
  exact he

/-- Lower values are indexed by the upper value of the same context entry. -/
def FiberContext (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → FiberValue) : Prop :=
  ∀ j A, Γ[j]? = some A →
    (δ j).code = fiberShape n i Γ ρ (lift (j + 1) 0 A) (ρ j)

theorem FiberContext.up (h : FiberContext n i Γ ρ δ)
    (hA : BoundedTyping n Γ A (.srt s)) (hq : sortRank (.type i) + 1 = n)
    (hy : y.code = fiberShape n i Γ ρ A x) :
    FiberContext n i (A :: Γ) (push x ρ) (push y δ) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      fiberShape_ren hA (.cons hA.wf hA) (.weaken Γ A) hq (fun _ => rfl)] using hy
  | succ j =>
    obtain ⟨r, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1),
      fiberShape_ren hC (.cons hA.wf hA) (.weaken Γ A) hq (fun _ => rfl)] using h j C hj

theorem FiberContext.var_code (h : FiberContext n i Γ ρ δ)
    (hw : BoundedWf n Γ) (hj : Γ[j]? = some A)
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    (δ j).code = inferredFiber n i Γ ρ (.var j) := by
  rw [inferredFiber_eq (.var hw hj) hq hρ]
  exact h j A hj

end Submission.Helpers
