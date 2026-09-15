import Submission.Typing

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A beta-normal term has no outgoing one-step reduction. -/
def Normal (t : Tm) : Prop := ∀ u, ¬ Step t u

theorem normal_form (hn : SN t) (ht : Typing Γ t A) :
    ∃ u, Typing Γ u A ∧ Normal u := by
  classical
  induction hn with
  | intro t hn ih =>
    by_cases h : ∃ u, Step t u
    · obtain ⟨u, hu⟩ := h
      exact ih u hu (preservation ht hu)
    · exact ⟨t, ht, fun u hu => h ⟨u, hu⟩⟩

/-- Contexts whose variables all have types convertible to sorts. -/
def SortContext (Γ : List Tm) : Prop :=
  ∀ i A, Γ[i]? = some A → ∃ s, Conv (lift (i + 1) 0 A) (.srt s)

theorem SortContext.nil : SortContext [] := by
  intro i A h
  simp at h

theorem SortContext.singleton (h : Conv A (.srt s)) : SortContext [A] := by
  intro i B hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst B
    exact ⟨s, by simpa only [Nat.zero_add, lift_one, ren] using conv_ren h Nat.succ⟩
  | succ i => simp at hi

theorem normal_nonlam_sort (ht : Typing Γ t A) (hn : Normal t)
    (hΓ : SortContext Γ) (hl : ∀ C b, t ≠ .lam C b) :
    ∃ s, Conv A (.srt s) := by
  induction t generalizing Γ A with
  | var i =>
    obtain ⟨B, hi, he⟩ := typing_generation ht
    obtain ⟨s, hs⟩ := hΓ i B hi
    exact ⟨s, conv_trans (conv_symm he) hs⟩
  | srt s =>
    obtain ⟨s', hs, he⟩ := typing_generation ht
    exact ⟨s', conv_symm he⟩
  | pi C D ihC ihD =>
    obtain ⟨s₁, s₂, s₃, _, _, _, he⟩ := typing_generation ht
    exact ⟨s₃, conv_symm he⟩
  | lam C b => exact (hl C b rfl).elim
  | app f a ihf iha =>
    obtain ⟨C, D, hf, ha, he⟩ := typing_generation ht
    have hnf : Normal f := fun f' h => hn _ (.appFun _ h)
    have hlf : ∀ C b, f ≠ .lam C b := by
      intro C b heq
      subst f
      exact hn _ (.beta _ _ _)
    obtain ⟨s, hs⟩ := ihf hf hnf hΓ hlf
    exact (not_conv_pi_srt hs).elim

theorem normal_not_var_type (ht : Typing Γ t A) (hn : Normal t)
    (hΓ : SortContext Γ) (hc : Conv A (.var i)) : False := by
  classical
  by_cases hl : ∃ C b, t = .lam C b
  · obtain ⟨C, b, rfl⟩ := hl
    obtain ⟨B, s, _, _, he⟩ := typing_generation ht
    exact not_conv_pi_var (conv_trans he hc)
  · have hl' : ∀ C b, t ≠ .lam C b := fun C b he => hl ⟨C, b, he⟩
    obtain ⟨s, hs⟩ := normal_nonlam_sort ht hn hΓ hl'
    exact not_conv_var_srt (conv_trans (conv_symm hc) hs)

theorem normal_not_false (ht : Typing [] t (.pi (.srt .prop) (.var 0)))
    (hn : Normal t) : False := by
  classical
  by_cases hl : ∃ C b, t = .lam C b
  · obtain ⟨C, b, rfl⟩ := hl
    obtain ⟨B, s, hPi, hb, he⟩ := typing_generation ht
    obtain ⟨hC, hB⟩ := conv_pi_inj he
    have hnb : Normal b := fun b' h => hn _ (.lamBody _ h)
    exact normal_not_var_type hb hnb (.singleton hC) hB
  · have hl' : ∀ C b, t ≠ .lam C b := fun C b he => hl ⟨C, b, he⟩
    obtain ⟨s, hs⟩ := normal_nonlam_sort ht hn .nil hl'
    exact not_conv_pi_srt hs

theorem consistency_of_normalization
    (hSN : ∀ (Γ : List Tm) (t A : Tm), Typing Γ t A → SN t) :
    ¬ ∃ t : Tm, Typing [] t (.pi (.srt .prop) (.var 0)) := by
  rintro ⟨t, ht⟩
  obtain ⟨u, hu, hn⟩ := normal_form (hSN _ _ _ ht) ht
  exact normal_not_false hu hn

end Submission.Helpers
