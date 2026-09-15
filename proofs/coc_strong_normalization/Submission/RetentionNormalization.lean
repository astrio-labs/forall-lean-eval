import Submission.RetentionReduction

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem Descent.retain_argument (X Y : Arity) (a t : Tm) :
    Descent (retain X Y a t) a := .single (.inr (.appArg _ _))

theorem Descent.retain_result (X Y : Arity) (a t : Tm) :
    Descent (retain X Y a t) t :=
  .head (.inr (.appFun _ _)) (.single (.inr (.appArg _ _)))

/-- The retained translation reduces full normalization to singleton computations. -/
theorem bounded_normalization_of_unit_arity
    (hunit : ∀ Δ u B, BoundedTyping n Δ u B → arityAt q B = .unit → SN u)
    (h : BoundedTyping n Γ t A) (hq : sortRank q + 1 = n) : SN t := by
  have hi := sn_descent (richErase_normalization h hq)
  generalize he : richErase n q Γ t = v at hi
  induction hi generalizing Γ t A with
  | intro v hv ih =>
    have lower {Δ : List Tm} {u B : Tm} (hu : BoundedTyping n Δ u B)
        (hd : Descent v (richErase n q Δ u)) : SN u :=
      ih _ hd hu rfl
    by_cases htunit : inferredArityAt n q Γ t = .unit
    · exact hunit Γ t A h ((inferredArityAt_eq h hq).symm.trans htunit)
    · cases t with
      | var i => exact Candidate.sn.var i
      | srt s => exact .intro _ (by intro u hu; cases hu)
      | lam C b =>
        obtain ⟨B, s, hPi, hb, hbs, hc⟩ := h.generation
        obtain ⟨sC, hC, _⟩ := hPi.pi_domain
        apply sn_lam (lower hC ?_) (lower hb ?_)
        · rw [← he, richErase_lam htunit]
          exact .retain_argument _ _ _ _
        · rw [← he, richErase_lam htunit]
          exact (Descent.retain_result _ _ _ _).trans (.single (.inr (.lamBody _ _)))
      | pi C D =>
        obtain ⟨s₁, s₂, s₃, hC, hD, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
        apply sn_pi (lower hC ?_) (lower hD ?_)
        · rw [← he, richErase_pi htunit]
          exact .retain_argument _ _ _ _
        · rw [← he, richErase_pi htunit]
          exact ((Descent.retain_result _ _ _ _).trans
            (.retain_argument _ _ _ _)).trans (.single (.inr (.lamBody _ _)))
      | app f a =>
        obtain ⟨C, D, hf, ha, hc⟩ := h.generation
        have hfsn : SN f := lower hf (by
          rw [← he, richErase_app htunit]
          exact .single (.inr (.appFun _ _)))
        have hasn : SN a := lower ha (by
          rw [← he, richErase_app htunit]
          exact .single (.inr (.appArg _ _)))
        apply sn_app_of_contracta hfsn hasn
        intro E b a' hff haa
        have hpath := hff.app haa
        have hmid := h.preservation_steps hpath
        have hf' := hf.preservation_steps hff
        have ha' := ha.preservation_steps haa
        obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := hf'.generation
        obtain ⟨sE, hE, hsE⟩ := hPi.pi_domain
        have haE : BoundedTyping n Γ a' E :=
          .conv ha' hE (conv_symm (conv_pi_inj hconv).1) hsE
        have hlf : BoundedTyping n Γ (.lam E b) (.pi E B) := .lam hPi hb hbs
        have heapp : inferredArityAt n q Γ (.app (.lam E b) a') = arityAt q B := by
          rw [inferredArityAt_app hlf haE hq, inferredArityAt_eq hlf hq,
            arityAt, Arity.codomain_arrow]
        have hemid := (inferredArityAt_eq hmid hq).trans (inferredArityAt_eq h hq).symm
        have hBne : arityAt q B ≠ .unit :=
          fun hB => htunit (hemid.symm.trans (heapp.trans hB))
        have hbefore := richErase_steps h hpath hq
        have hafter := richErase_beta hPi hb haE hq hBne
        apply lower (hb.subst haE)
        rw [← he]
        exact .of_stepsPlus (hbefore.trans_plus hafter)

/-- Only the singleton-arity case above the two-sort fragment remains necessary. -/
theorem normalization_of_singleton_cases
    (hunit : ∀ n, 2 ≤ n → ∀ Γ t A, BoundedTyping n Γ t A →
      arityAt (.type (n - 2)) A = .unit → SN t) :
    ∀ {Γ t A}, Typing Γ t A → SN t := by
  intro Γ t A
  apply normalization_of_above_one
  intro n hn Δ u B h
  apply bounded_normalization_of_unit_arity (hunit n hn) h
  simp only [sortRank]
  omega

end Submission.Helpers
