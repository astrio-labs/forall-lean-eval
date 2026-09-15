import Submission.Reducibility

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem Candidate.ext {A B : Candidate} (h : ∀ t, A.contains t ↔ B.contains t) : A = B := by
  have he : A.contains = B.contains := funext (fun t => propext (h t))
  cases A
  cases B
  cases he
  rfl

/-- A family whose interpretation is unchanged when a valid argument reduces. -/
def StableFamily (A : Candidate) (B : Tm → Candidate) : Prop :=
  ∀ a a', A.contains a → Step a a' → B a = B a'

theorem StableFamily.steps (h : StableFamily A B) (ha : A.contains a)
    (hs : Steps a a') : B a = B a' := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact (h _ _ ha hs).trans (ih (A.reduce ha hs))

theorem StableFamily.conv (h : StableFamily A B) (ha : A.contains a)
    (ha' : A.contains a') (hc : Conv a a') : B a = B a' := by
  have red_steps {t u : Tm} (h : Red t u) : Steps t u := by
    induction h with
    | refl => exact .refl _
    | head hp hr ih => exact hp.steps.trans ih
  obtain ⟨w, hw, hw'⟩ := conv_join hc
  exact (h.steps ha (red_steps hw)).trans (h.steps ha' (red_steps hw')).symm

theorem dependent_arrow_expand (A : Candidate) (B : Tm → Candidate)
    (hB : StableFamily A B) (hn : Neutral t)
    (h : ∀ u, Step t u → ∀ a, A.contains a → (B a).contains (.app u a))
    (ha : A.contains a) : (B a).contains (.app t a) := by
  have hsn := A.normalizes ha
  revert ha
  induction hsn with
  | intro a hs ih =>
    intro ha
    apply (B a).expand
    · intro D c he; cases he
    · intro v hv
      cases hv with
      | beta D b _a => exact (hn D b rfl).elim
      | appFun a ht => exact h _ ht a ha
      | appArg t haa' =>
        rw [hB _ _ ha haa']
        exact ih _ haa' (A.reduce ha haa')

/-- The candidate for a dependent product. -/
def Candidate.dependentArrow (A : Candidate) (B : Tm → Candidate)
    (hB : StableFamily A B) : Candidate where
  contains t := SN t ∧ ∀ a, A.contains a → (B a).contains (.app t a)
  normalizes h := h.1
  reduce h hs := ⟨sn_step h.1 hs,
    fun a ha => (B a).reduce (h.2 a ha) (.appFun _ hs)⟩
  expand hn h := ⟨.intro _ (fun u hu => (h u hu).1),
    fun a ha => dependent_arrow_expand (a := a) A B hB hn (fun u hu => (h u hu).2) ha⟩

theorem Candidate.dependent_apply (A : Candidate) (B : Tm → Candidate)
    (hB : StableFamily A B) (hf : (A.dependentArrow B hB).contains f)
    (ha : A.contains a) : (B a).contains (.app f a) := hf.2 a ha

theorem Candidate.dependent_lambda (A : Candidate) (B : Tm → Candidate)
    (hB : StableFamily A B) (hD : SN D)
    (h : ∀ a, A.contains a → (B a).contains (subst 0 a b)) :
    (A.dependentArrow B hB).contains (.lam D b) := by
  have hb : SN b := by
    apply sn_of_sub (single (.var 0))
    simpa only [subst_eq_sub] using (B (.var 0)).normalizes (h (.var 0) (A.var 0))
  exact ⟨sn_lam hD hb, fun a ha => (B a).beta hD hb (A.normalizes ha) (h a ha)⟩

theorem Candidate.dependentArrow_congr (A : Candidate) (B C : Tm → Candidate)
    (hB : StableFamily A B) (hC : StableFamily A C)
    (he : ∀ a, A.contains a → B a = C a) :
    A.dependentArrow B hB = A.dependentArrow C hC := by
  apply Candidate.ext
  intro t
  constructor
  · rintro ⟨hn, ht⟩
    refine ⟨hn, fun a ha => ?_⟩
    rw [← he a ha]
    exact ht a ha
  · rintro ⟨hn, ht⟩
    refine ⟨hn, fun a ha => ?_⟩
    rw [he a ha]
    exact ht a ha

theorem Candidate.dependentArrow_const (A B : Candidate) :
    A.dependentArrow (fun _ => B) (fun _ _ _ _ => rfl) = A.arrow B := by
  apply Candidate.ext
  intro t
  rfl

end Submission.Helpers
