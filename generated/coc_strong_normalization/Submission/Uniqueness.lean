import Submission.Typing

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem ax_functional (h : Ax s t) (h' : Ax s t') : t = t' := by
  cases h <;> cases h' <;> rfl

theorem rule_functional (h : Rl s₁ s₂ s₃) (h' : Rl s₁ s₂ s₃') : s₃ = s₃' := by
  cases h <;> cases h' <;> rfl

/-- In this functional PTS, a term's type is unique up to beta conversion. -/
theorem typing_unique (h : Typing Γ t A) (h' : Typing Γ t A') : Conv A A' := by
  induction h using Typing.rec (motive_1 := fun _ _ => True)
      generalizing A' with
  | nil => trivial
  | cons => trivial
  | srt hw hax _ =>
    obtain ⟨s', hs', hc⟩ := typing_generation h'
    have he := ax_functional hax hs'
    subst he
    exact hc
  | var hw hi _ =>
    obtain ⟨B, hi', hc⟩ := typing_generation h'
    have he := Option.some.inj (hi.symm.trans hi')
    subst he
    exact hc
  | pi hA hB hr ihA ihB =>
    obtain ⟨s₁', s₂', s₃', hA', hB', hr', hc⟩ := typing_generation h'
    have he₁ := conv_srt_inj (ihA hA')
    have he₂ := conv_srt_inj (ihB hB')
    subst he₁
    subst he₂
    have he₃ := rule_functional hr hr'
    subst he₃
    exact hc
  | lam hPi hb ihPi ihb =>
    obtain ⟨B', s', hPi', hb', hc⟩ := typing_generation h'
    exact conv_trans (conv_pi (.refl _) (ihb hb')) hc
  | app hf ha ihf iha =>
    obtain ⟨C, D, hf', ha', hc⟩ := typing_generation h'
    have he := (conv_pi_inj (ihf hf')).2
    apply conv_trans _ hc
    simpa only [subst_eq_sub] using conv_sub he (single _)
  | conv ht hB hc iht ihB => exact conv_trans (conv_symm hc) (iht h')

theorem typing_sort_unique (h : Typing Γ t (.srt s))
    (h' : Typing Γ t (.srt s')) : s = s' :=
  conv_srt_inj (typing_unique h h')

theorem pi_rule_inversion (h : Typing Γ (.pi A B) (.srt s)) :
    ∃ s₁ s₂, Typing Γ A (.srt s₁) ∧ Typing (A :: Γ) B (.srt s₂) ∧ Rl s₁ s₂ s := by
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := typing_generation h
  have he := conv_srt_inj hc
  subst he
  exact ⟨s₁, s₂, hA, hB, hr⟩

end Submission.Helpers
