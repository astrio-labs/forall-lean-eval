import Submission.ThirdProduct

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem middleDecode_form (s : Srt) (k : Arity) (v : MiddleValue)
    (u : ShapeValue) (f : MiddleValue) :
    ThirdCode.AtSort s (middleDecode (some s) k v u f) := by
  cases s with
  | prop => rfl
  | type i => cases i with
    | zero => exact ⟨_, rfl⟩
    | succ j => cases j with
      | zero => exact ⟨_, rfl⟩
      | succ j => exact True.intro

/-- The source universe determines how much carrier data is needed. This uses
only the typing derivation and the preceding shape environment. -/
theorem middleSemantics_form (h : BoundedTyping 3 Γ A (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    ThirdCode.AtSort s ((middleSemantics Γ ρ δ A).2 u f) := by
  induction A generalizing Γ s ρ δ u f with
  | var j =>
    change ThirdCode.AtSort s (middleDecode (typeSort 3 Γ (.var j)) _ _ u f)
    rw [typeSort_eq h]
    exact middleDecode_form _ _ _ _ _
  | srt r =>
    obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    cases ha with
    | prop => exact ⟨.prop, rfl⟩
    | type j => cases j with
      | zero => exact ⟨_, rfl⟩
      | succ j => exact True.intro
  | app g a ihg iha =>
    change ThirdCode.AtSort s (middleDecode (typeSort 3 Γ (.app g a)) _ _ u f)
    rw [typeSort_eq h]
    exact middleDecode_form _ _ _ _ _
  | lam D b ihD ihb =>
    obtain ⟨B, r, hPi, hb, hr, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | pi D B ihD ihB =>
    obtain ⟨sD, sB, s', hD, hB, hr, hsD, hsB, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    rw [middleSemantics]
    dsimp only
    unfold middleCanonical
    cases s with
    | prop =>
      have heB : sB = .prop := by cases hr; rfl
      subst sB
      apply thirdProduct_trivial
      intro x hx y hy z w
      exact ihB hB (hρ.up hx)
    | type j =>
      cases j with
      | zero =>
        have hd := rule_predicative_domain hr
        have hb := rule_predicative_codomain hr
        have hda : arityAt (.type 1) D = .unit :=
          hD.below_top_kind rfl (by simp only [sortRank] at hd ⊢; omega)
        change ThirdCode.IsArity _
        rw [hda]
        apply thirdProduct_isArity
        · exact middleShape_lower hD (by simp only [sortRank] at hd ⊢; omega)
        · intro y
          exact ThirdCode.AtSort.arity (ihD hD hρ) hd
        · intro y z w
          exact ThirdCode.AtSort.arity (ihB hB (hρ.up hda.symm)) hb
      | succ j =>
        cases j with
        | zero =>
          have hd := rule_predicative_domain hr
          have hb := rule_predicative_codomain hr
          have hda : arityAt (.type 1) D = .unit :=
            hD.below_top_kind rfl (by simp only [sortRank] at hd ⊢; omega)
          change ThirdCode.IsFiber _
          rw [hda]
          apply thirdProduct_isFiber (k := nextArity 3 1 Γ ρ D)
          · exact middleShape_small hD hd rfl hρ
          · intro y
            exact ThirdCode.AtSort.fiber (ihD hD hρ) hd
          · intro y z w
            exact ThirdCode.AtSort.fiber (ihB hB (hρ.up hda.symm)) hb
        | succ j => exact True.intro

end Submission.Helpers
