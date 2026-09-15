import Submission.Reducibility

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A nonempty finite reduction sequence. -/
def StepsPlus (t u : Tm) : Prop := ∃ v, Step t v ∧ Steps v u

theorem StepsPlus.steps (h : StepsPlus t u) : Steps t u := by
  obtain ⟨v, hs, hr⟩ := h
  exact .head hs hr

theorem StepsPlus.map (h : StepsPlus t u) (F : Tm → Tm)
    (hF : ∀ {t u}, Step t u → Step (F t) (F u)) : StepsPlus (F t) (F u) := by
  obtain ⟨v, hs, hr⟩ := h
  exact ⟨F v, hF hs, hr.map F hF⟩

theorem StepsPlus.trans_steps (h : StepsPlus t u) (hr : Steps u v) : StepsPlus t v := by
  obtain ⟨w, hs, hr'⟩ := h
  exact ⟨w, hs, hr'.trans hr⟩

theorem Steps.trans_plus (h : Steps t u) (hr : StepsPlus u v) : StepsPlus t v := by
  induction h with
  | refl => exact hr
  | head hs hr' ih => exact ⟨_, hs, hr'.trans hr.steps⟩

/-- Moving to an immediate syntactic component. -/
inductive ImmediateSubterm : Tm → Tm → Prop where
  | appFun (f a : Tm) : ImmediateSubterm (.app f a) f
  | appArg (f a : Tm) : ImmediateSubterm (.app f a) a
  | lamTy (A b : Tm) : ImmediateSubterm (.lam A b) A
  | lamBody (A b : Tm) : ImmediateSubterm (.lam A b) b
  | piDom (A B : Tm) : ImmediateSubterm (.pi A B) A
  | piCod (A B : Tm) : ImmediateSubterm (.pi A B) B

def InsideStep (t u : Tm) : Prop := Step t u ∨ ImmediateSubterm t u

/-- Nonempty paths combining beta reduction with passage to subterms. -/
inductive Descent : Tm → Tm → Prop where
  | single : InsideStep t u → Descent t u
  | head : InsideStep t u → Descent u v → Descent t v

theorem Descent.trans (h : Descent t u) (h' : Descent u v) : Descent t v := by
  induction h with
  | single hs => exact .head hs h'
  | head hs hr ih => exact .head hs (ih h')

theorem Steps.eq_or_descent (h : Steps t u) : t = u ∨ Descent t u := by
  induction h with
  | refl => exact .inl rfl
  | head hs hr ih =>
    rcases ih with he | hd
    · subst he; exact .inr (.single (.inl hs))
    · exact .inr (.head (.inl hs) hd)

theorem Descent.of_stepsPlus (h : StepsPlus t u) : Descent t u := by
  obtain ⟨v, hs, hr⟩ := h
  rcases hr.eq_or_descent with he | hd
  · subst he; exact .single (.inl hs)
  · exact .head (.inl hs) hd

theorem inside_accessible_of_reducts
    (h : ∀ u, Step t u → Acc (fun u v => InsideStep v u) u) :
    Acc (fun u v => InsideStep v u) t := by
  induction t with
  | var i =>
    apply Acc.intro
    intro u hu
    rcases hu with hs | hs <;> cases hs
  | srt s =>
    apply Acc.intro
    intro u hu
    rcases hu with hs | hs <;> cases hs
  | app f a ihf iha =>
    apply Acc.intro
    intro u hu
    rcases hu with hs | hs
    · exact h u hs
    · cases hs with
      | appFun =>
        apply ihf
        intro f' hf
        exact (h _ (.appFun a hf)).inv (.inr (.appFun _ _))
      | appArg =>
        apply iha
        intro a' ha
        exact (h _ (.appArg f ha)).inv (.inr (.appArg _ _))
  | lam A b ihA ihb =>
    apply Acc.intro
    intro u hu
    rcases hu with hs | hs
    · exact h u hs
    · cases hs with
      | lamTy =>
        apply ihA
        intro A' hA
        exact (h _ (.lamTy b hA)).inv (.inr (.lamTy _ _))
      | lamBody =>
        apply ihb
        intro b' hb
        exact (h _ (.lamBody A hb)).inv (.inr (.lamBody _ _))
  | pi A B ihA ihB =>
    apply Acc.intro
    intro u hu
    rcases hu with hs | hs
    · exact h u hs
    · cases hs with
      | piDom =>
        apply ihA
        intro A' hA
        exact (h _ (.piDom B hA)).inv (.inr (.piDom _ _))
      | piCod =>
        apply ihB
        intro B' hB
        exact (h _ (.piCod A hB)).inv (.inr (.piCod _ _))

theorem sn_inside (h : SN t) : Acc (fun u v => InsideStep v u) t := by
  induction h with
  | intro t ht ih => exact inside_accessible_of_reducts ih

theorem sn_descent (h : SN t) : Acc (fun u v => Descent v u) t := by
  have hi := sn_inside h
  clear h
  induction hi with
  | intro t ht ih =>
    apply Acc.intro
    intro u hu
    cases hu with
    | single hs => exact ih _ hs
    | head hs hr => exact (ih _ hs).inv hr

/-- An application normalizes if its components and every exposed beta contractum do. -/
theorem sn_app_of_contracta (hf : SN f) (ha : SN a)
    (hβ : ∀ A b a', Steps f (.lam A b) → Steps a a' → SN (subst 0 a' b)) :
    SN (.app f a) := by
  induction hf generalizing a with
  | intro f hf ihf =>
    induction ha with
    | intro a ha iha =>
      apply Acc.intro
      intro u hu
      cases hu with
      | beta A b a => exact hβ A b a (.refl _) (.refl _)
      | appFun a hs =>
        apply ihf _ hs (.intro _ ha)
        intro A b a' hff haa
        exact hβ A b a' (.head hs hff) haa
      | appArg f hs =>
        apply iha _ hs
        intro A b a' hff haa
        exact hβ A b a' hff (.head hs haa)

end Submission.Helpers
