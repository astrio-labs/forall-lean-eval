import Submission.TopShapeSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Conversion between well-formed types preserves their universe. -/
theorem bounded_sort_conv (hA : BoundedTyping n Γ A (.srt s))
    (hB : BoundedTyping n Γ B (.srt s')) (hc : Conv A B) : s = s' := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact typing_sort_unique (hA.preservation_red hC).forget (hB.preservation_red hC').forget

/-- Classify only terms that have a sort as their type. -/
noncomputable def typeSort (n : Nat) (Γ : List Tm) (t : Tm) : Option Srt := by
  classical
  exact if h : ∃ s, BoundedTyping n Γ t (.srt s) then some (Classical.choose h) else none

theorem typeSort_eq (h : BoundedTyping n Γ t (.srt s)) : typeSort n Γ t = some s := by
  have hex : ∃ r, BoundedTyping n Γ t (.srt r) := ⟨s, h⟩
  simp only [typeSort, dif_pos hex]
  exact congrArg some (typing_sort_unique (Classical.choose_spec hex).forget h.forget)

theorem typeSort_spec (h : typeSort n Γ t = some s) : BoundedTyping n Γ t (.srt s) := by
  classical
  unfold typeSort at h
  split at h
  · rename_i ht
    have he := Option.some.inj h
    rw [← he]
    exact Classical.choose_spec ht
  · cases h

theorem typeSort_conv (hA : BoundedTyping n Γ A (.srt s))
    (hB : BoundedTyping n Γ B (.srt s')) (hc : Conv A B) :
    typeSort n Γ A = typeSort n Γ B := by
  rw [typeSort_eq hA, typeSort_eq hB, bounded_sort_conv hA hB hc]

theorem sortRank_injective (h : sortRank s = sortRank s') : s = s' := by
  cases s with
  | prop => cases s' <;> simp_all [sortRank]
  | type i =>
    cases s' with
    | prop => simp_all [sortRank]
    | type j =>
      have hi : i = j := by simp only [sortRank] at h; omega
      subst j; rfl

/-- Below a finite top sort, a universe is either the preceding one or strictly lower. -/
theorem sort_level_cases (hs : sortRank s ≤ n) (hq : sortRank q + 1 = n) :
    s = q ∨ sortRank s < sortRank q ∨ sortRank s = n := by
  by_cases he : sortRank s = sortRank q
  · exact .inl (sortRank_injective he)
  · by_cases ht : sortRank s = n
    · exact .inr (.inr ht)
    · exact .inr (.inl (by omega))

/-- A variable's type is formed below the highest sort. -/
theorem BoundedTyping.var_below_top (h : BoundedTyping n Γ (.var j) (.srt s)) :
    sortRank s < n := by
  obtain ⟨A, hj, hc⟩ := h.generation
  obtain ⟨sA, hA⟩ := h.wf.lookup hj
  exact hA.sorts_below.conv_sort hc

/-- An application's substituted result type also lies below the highest sort. -/
theorem BoundedTyping.app_below_top (h : BoundedTyping n Γ (.app f a) (.srt s)) :
    sortRank s < n := by
  obtain ⟨A, B, hf, ha, hc⟩ := h.generation
  exact (hf.pi_components.2.subst ha.sorts_below).conv_sort hc

/-- Terms at the untypable top sort are sorts or syntactic products. -/
theorem BoundedTyping.top_sort_form (h : BoundedTyping n Γ t (.srt s))
    (hs : sortRank s = n) :
    (∃ r, t = .srt r) ∨ ∃ A B, t = .pi A B := by
  cases t with
  | var j => have hh := h.var_below_top; omega
  | srt r => exact .inl ⟨r, rfl⟩
  | pi A B => exact .inr ⟨A, B, rfl⟩
  | lam A b =>
    obtain ⟨B, r, hPi, hb, hbnd, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | app f a => have hh := h.app_below_top; omega

theorem BoundedTyping.not_top_type (h : BoundedTyping n Γ t A)
    (hA : BoundedTyping n Γ A (.srt s))
    (h' : BoundedTyping n Γ t (.srt r)) : sortRank r < n := by
  have hc := typing_unique h.forget h'.forget
  exact hA.sorts_below.conv_sort hc

/-- Any chosen type of a term with a formed type is itself formed at the same bound. -/
theorem chosenType_sorted (h : BoundedTyping n Γ t A)
    (hA : BoundedTyping n Γ A (.srt s)) :
    ∃ r, BoundedTyping n Γ (chosenType n Γ t) (.srt r) ∧ sortRank r ≤ n := by
  have ht := chosenType_typing h
  rcases ht.regularity_top with ⟨r, he, hr⟩ | hh
  · have hc := typing_unique h.forget ht.forget
    rw [he] at hc
    have hlt := hA.sorts_below.conv_sort hc
    omega
  · exact hh

end Submission.Helpers
