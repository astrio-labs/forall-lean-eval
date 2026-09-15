import Submission.TopSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Weak-head beta reduction, including reduction along the function spine. -/
inductive HeadStep : Tm → Tm → Prop where
  | beta (A b a : Tm) : HeadStep (.app (.lam A b) a) (subst 0 a b)
  | appFun (a : Tm) : HeadStep f f' → HeadStep (.app f a) (.app f' a)

theorem HeadStep.toStep (h : HeadStep t u) : Step t u := by
  induction h with
  | beta A b a => exact .beta _ _ _
  | appFun a h ih => exact .appFun a ih

/-- Non-singleton computations retain each weak-head step in the two-sort projection. -/
theorem topErase_headStep (h : BoundedTyping n Γ t C) (hs : HeadStep t u)
    (hq : sortRank q + 1 = n) (hne : arityAt q C ≠ .unit) :
    Step (topErase n q Γ t) (topErase n q Γ u) := by
  induction hs generalizing C with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, hc⟩ := h.generation
    obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping n Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hconv).1) hsA
    have hf' : BoundedTyping n Γ (.lam A b) (.pi A B) := .lam hPi hb hbs
    have he : inferredArityAt n q Γ (.app (.lam A b) a) = arityAt q B := by
      rw [inferredArityAt_app hf' ha' hq, inferredArityAt_eq hf' hq,
        arityAt, Arity.codomain_arrow]
    have hBne : arityAt q B ≠ .unit := by
      intro hb
      exact hne ((inferredArityAt_eq h hq).symm.trans (he.trans hb))
    exact topErase_beta hPi hb ha' hq hBne
  | @appFun f f' a hs ih =>
    obtain ⟨D, E, hf, ha, hc⟩ := h.generation
    have hi : inferredArityAt n q Γ (.app f a) ≠ .unit := by
      rw [inferredArityAt_eq h hq]
      exact hne
    have hEne : arityAt q E ≠ .unit := by
      have he := inferredArityAt_app hf ha hq
      rw [inferredArityAt_eq hf hq, arityAt, Arity.codomain_arrow] at he
      exact fun hE => hi (he.trans hE)
    have hFne : arityAt q (.pi D E) ≠ .unit := by
      intro hF
      exact hEne ((Arity.arrow_unit_iff _ _).1 hF)
    have ht' := h.preservation (.appFun a hs.toStep)
    have hi' : inferredArityAt n q Γ (.app f' a) ≠ .unit := by
      rw [inferredArityAt_eq ht' hq]
      exact hne
    rw [topErase_app hi, topErase_app hi']
    exact .appFun _ (ih hf hFne)

/-- The highest nontrivial arity admits no infinite weak-head reduction sequence. -/
theorem top_head_normalization (h : BoundedTyping n Γ t A)
    (hq : sortRank q + 1 = n) (hne : arityAt q A ≠ .unit) :
    Acc (fun u v => HeadStep v u) t := by
  have hsn := topErase_normalization h hq
  generalize he : topErase n q Γ t = v at hsn
  induction hsn generalizing t with
  | intro v hv ih =>
    apply Acc.intro t
    intro u hu
    apply ih (topErase n q Γ u)
    · rw [← he]
      exact topErase_headStep h hu hq hne
    · exact h.preservation hu.toStep
    · rfl

/-- Types at the highest available universe weak-head normalize uniformly in the bound. -/
theorem top_sort_head_normalization (h : BoundedTyping n Γ t (.srt q))
    (hq : sortRank q + 1 = n) : Acc (fun u v => HeadStep v u) t := by
  apply top_head_normalization h hq
  simp only [arityAt, ↓reduceIte]
  intro he
  cases he

end Submission.Helpers
