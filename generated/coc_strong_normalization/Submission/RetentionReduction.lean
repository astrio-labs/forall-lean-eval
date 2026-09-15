import Submission.RetentionSubstitution
import Submission.ReductionMeasure

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem Steps.retain (ha : Steps a a') (ht : Steps t t') :
    Steps (retain X Y a t) (retain X Y a' t') :=
  ((Steps.refl _).app ht).app ha

theorem retain_stepsPlus (X Y : Arity) (a t : Tm) : StepsPlus (retain X Y a t) t := by
  have h₁ : Step (retain X Y a t)
      (.app (.lam (arityType X) (ren Nat.succ t)) a) := by
    have h := Step.appFun a (Step.beta (arityType Y) (.lam (arityType X) (.var 1)) t)
    simpa only [retain, subst_eq_sub, sub, arityType_sub, upSub, single] using h
  have h₂ : Step (.app (.lam (arityType X) (ren Nat.succ t)) a) t := by
    have h := Step.beta (arityType X) (ren Nat.succ t) a
    simpa only [subst_eq_sub, single_ren_succ] using h
  exact ⟨_, h₁, .head h₂ (.refl _)⟩

theorem richErase_beta (hPi : BoundedTyping n Γ (.pi A B) (.srt s))
    (hb : BoundedTyping n (A :: Γ) b B) (ha : BoundedTyping n Γ a A)
    (hq : sortRank q + 1 = n) (hne : arityAt q B ≠ .unit) :
    StepsPlus (richErase n q Γ (.app (.lam A b) a)) (richErase n q Γ (subst 0 a b)) := by
  have hf : BoundedTyping n Γ (.lam A b) (.pi A B) := .lam hPi hb hPi.sort_bound
  have hfn : inferredArityAt n q Γ (.lam A b) ≠ .unit := by
    rw [inferredArityAt_eq hf hq, arityAt]
    intro he
    exact hne ((Arity.arrow_unit_iff _ _).1 he)
  have happ : inferredArityAt n q Γ (.app (.lam A b) a) ≠ .unit := by
    rw [inferredArityAt_app hf ha hq, inferredArityAt_eq hf hq,
      arityAt, Arity.codomain_arrow]
    exact hne
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [richErase_app happ, richErase_lam hfn, richErase_subst hb ha hA hq]
  apply (StepsPlus.map (retain_stepsPlus _ _ _ _)
    (fun f => .app f (richErase n q Γ a)) (Step.appFun _)).trans_steps
  exact .head (.beta _ _ _) (.refl _)

theorem richErase_unit_step (h : BoundedTyping n Γ t C) (hs : Step t u)
    (hq : sortRank q + 1 = n) (he : inferredArityAt n q Γ t = .unit) :
    Steps (richErase n q Γ t) (richErase n q Γ u) := by
  rw [richErase_unit he, richErase_unit ((inferredArityAt_step h hs hq).trans he)]
  exact .refl _

/-- Every source reduction is simulated, allowing equality in erased subterms. -/
theorem richErase_step (h : BoundedTyping n Γ t C) (hs : Step t u)
    (hq : sortRank q + 1 = n) : Steps (richErase n q Γ t) (richErase n q Γ u) := by
  induction hs generalizing Γ C with
  | beta A b a =>
    by_cases he : inferredArityAt n q Γ (.app (.lam A b) a) = .unit
    · exact richErase_unit_step h (.beta _ _ _) hq he
    · obtain ⟨D, E, hf, ha, hc⟩ := h.generation
      obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := hf.generation
      obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
      have ha' : BoundedTyping n Γ a A :=
        .conv ha hA (conv_symm (conv_pi_inj hconv).1) hsA
      have hf' : BoundedTyping n Γ (.lam A b) (.pi A B) := .lam hPi hb hbs
      have hBne : arityAt q B ≠ .unit := by
        rw [inferredArityAt_app hf' ha' hq, inferredArityAt_eq hf' hq,
          arityAt, Arity.codomain_arrow] at he
        exact he
      exact (richErase_beta hPi hb ha' hq hBne).steps
  | @appFun f f' a hs ih =>
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · exact richErase_unit_step h (.appFun a hs) hq he
    · obtain ⟨D, E, hf, ha, hc⟩ := h.generation
      have hi := inferredArityAt_step h (.appFun a hs) hq
      rw [richErase_app he, richErase_app (fun he' => he (hi.symm.trans he'))]
      exact (ih hf).app (.refl _)
  | @appArg f a a' hs ih =>
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · exact richErase_unit_step h (.appArg f hs) hq he
    · obtain ⟨D, E, hf, ha, hc⟩ := h.generation
      have hi := inferredArityAt_step h (.appArg f hs) hq
      rw [richErase_app he, richErase_app (fun he' => he (hi.symm.trans he'))]
      exact (Steps.refl _).app (ih ha)
  | @lamTy A A' b hs ih =>
    by_cases he : inferredArityAt n q Γ (.lam A b) = .unit
    · exact richErase_unit_step h (.lamTy b hs) hq he
    · obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := h.generation
      obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
      have hA' := hA.preservation hs
      have hi := inferredArityAt_step h (.lamTy b hs) hq
      have hc : Conv A A' := .fwd (.refl _) hs
      have heA := (hA.goodAt hq).arity_step hs
      have heB := richErase_context_conversion hb hA hA' hsA hc hq
      rw [richErase_lam he, richErase_lam (fun he' => he (hi.symm.trans he')),
        hi, heA, heB]
      exact (ih hA).retain (.refl _)
  | @lamBody A b b' hs ih =>
    by_cases he : inferredArityAt n q Γ (.lam A b) = .unit
    · exact richErase_unit_step h (.lamBody A hs) hq he
    · obtain ⟨B, s, hPi, hb, hbs, hconv⟩ := h.generation
      have hi := inferredArityAt_step h (.lamBody A hs) hq
      rw [richErase_lam he, richErase_lam (fun he' => he (hi.symm.trans he')), hi]
      exact (Steps.refl _).retain ((Steps.refl _).lam (ih hb))
  | @piDom A A' B hs ih =>
    by_cases he : inferredArityAt n q Γ (.pi A B) = .unit
    · exact richErase_unit_step h (.piDom B hs) hq he
    · obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
      have hA' := hA.preservation hs
      have hi := inferredArityAt_step h (.piDom B hs) hq
      have heA := (hA.goodAt hq).arity_step hs
      have heB := richErase_context_conversion hB hA hA' hs₁ (.fwd (.refl _) hs) hq
      rw [richErase_pi he, richErase_pi (fun he' => he (hi.symm.trans he')), heA, heB]
      exact (ih hA).retain (.refl _)
  | @piCod A B B' hs ih =>
    by_cases he : inferredArityAt n q Γ (.pi A B) = .unit
    · exact richErase_unit_step h (.piCod A hs) hq he
    · obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
      have hi := inferredArityAt_step h (.piCod A hs) hq
      rw [richErase_pi he, richErase_pi (fun he' => he (hi.symm.trans he'))]
      exact (Steps.refl _).retain (((Steps.refl _).lam (ih hB)).retain (.refl _))

theorem richErase_steps (h : BoundedTyping n Γ t C) (hs : Steps t u)
    (hq : sortRank q + 1 = n) : Steps (richErase n q Γ t) (richErase n q Γ u) := by
  induction hs with
  | refl => exact .refl _
  | head hs hr ih => exact (richErase_step h hs hq).trans (ih (h.preservation hs))

end Submission.Helpers
