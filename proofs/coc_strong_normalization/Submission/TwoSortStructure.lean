import Submission.BoundedPreservation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Terms containing no predicative sort. -/
def NoTypes : Tm → Prop
  | .var _ => True
  | .srt .prop => True
  | .srt (.type _) => False
  | .app f a => NoTypes f ∧ NoTypes a
  | .lam A b => NoTypes A ∧ NoTypes b
  | .pi A B => NoTypes A ∧ NoTypes B

theorem NoTypes.rename (h : NoTypes t) (ρ : Nat → Nat) : NoTypes (ren ρ t) := by
  induction t generalizing ρ with
  | var => trivial
  | srt s => exact h
  | app f a ihf iha => exact ⟨ihf h.1 _, iha h.2 _⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 _, ihb h.2 _⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 _, ihB h.2 _⟩

theorem NoTypes.substitute (h : NoTypes t) (hσ : ∀ i, NoTypes (σ i)) :
    NoTypes (sub σ t) := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, NoTypes (σ i)) : ∀ i, NoTypes (upSub σ i) := by
    intro i
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).rename _
  induction t generalizing σ with
  | var i => exact hσ i
  | srt s => exact h
  | app f a ihf iha => exact ⟨ihf h.1 hσ, iha h.2 hσ⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 hσ, ihb h.2 (hup hσ)⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 hσ, ihB h.2 (hup hσ)⟩

theorem NoTypes.subst (hb : NoTypes b) (ha : NoTypes a) : NoTypes (subst 0 a b) := by
  rw [subst_eq_sub]
  apply hb.substitute
  intro i
  cases i with
  | zero => exact ha
  | succ => trivial

theorem NoTypes.parallel (h : NoTypes t) (hs : Par t u) : NoTypes u := by
  induction hs with
  | var => trivial
  | srt => exact h
  | app _ _ ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | pi _ _ ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | beta A _ _ ihb iha => exact (ihb h.1.2).subst (iha h.2)

theorem NoTypes.reduction (h : NoTypes t) (hs : Red t u) : NoTypes u := by
  induction hs with
  | refl => exact h
  | head hs hr ih => exact ih (h.parallel hs)

theorem NoTypes.not_conv_type (h : NoTypes t) : ¬ Conv t (.srt (.type i)) := by
  intro hc
  obtain ⟨u, hu, hu'⟩ := conv_join hc
  have he := red_srt hu' _ rfl
  subst u
  exact h.reduction hu

/-- In the two-sort fragment, a kind has a product spine ending in `Prop`. -/
def isKind : Tm → Bool
  | .srt .prop => true
  | .pi _ B => isKind B
  | _ => false

@[simp] theorem isKind_ren (ρ : Nat → Nat) (t : Tm) : isKind (ren ρ t) = isKind t := by
  induction t generalizing ρ with
  | var => rfl
  | srt s => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => exact ihB _

theorem isKind_sub (hσ : ∀ i, isKind (σ i) = false) (t : Tm) :
    isKind (sub σ t) = isKind t := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, isKind (σ i) = false) :
      ∀ i, isKind (upSub σ i) = false := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (isKind_ren _ _).trans (hσ i)
  induction t generalizing σ with
  | var i => exact hσ i
  | srt s => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => exact ihB (hup hσ)

theorem isKind_subst (ha : isKind a = false) (b : Tm) :
    isKind (subst 0 a b) = isKind b := by
  rw [subst_eq_sub]
  apply isKind_sub
  intro i
  cases i with
  | zero => exact ha
  | succ => rfl

/-- Arguments and abstraction bodies cannot themselves be kinds in this fragment. -/
def Good : Tm → Prop
  | .var _ => True
  | .srt _ => True
  | .app f a => Good f ∧ Good a ∧ isKind a = false
  | .lam A b => Good A ∧ Good b ∧ isKind b = false
  | .pi A B => Good A ∧ Good B

theorem Good.rename (h : Good t) (ρ : Nat → Nat) : Good (ren ρ t) := by
  induction t generalizing ρ with
  | var => trivial
  | srt => trivial
  | app f a ihf iha => exact ⟨ihf h.1 _, iha h.2.1 _, (isKind_ren _ _).trans h.2.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 _, ihb h.2.1 _, (isKind_ren _ _).trans h.2.2⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 _, ihB h.2 _⟩

theorem Good.substitute (h : Good t)
    (hσ : ∀ i, Good (σ i) ∧ isKind (σ i) = false) : Good (sub σ t) := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, Good (σ i) ∧ isKind (σ i) = false) :
      ∀ i, Good (upSub σ i) ∧ isKind (upSub σ i) = false := by
    intro i
    cases i with
    | zero => exact ⟨True.intro, rfl⟩
    | succ i => exact ⟨(hσ i).1.rename _, (isKind_ren _ _).trans (hσ i).2⟩
  induction t generalizing σ with
  | var i => exact (hσ i).1
  | srt => trivial
  | app f a ihf iha =>
    exact ⟨ihf h.1 hσ, iha h.2.1 hσ, (isKind_sub (fun i => (hσ i).2) _).trans h.2.2⟩
  | lam A b ihA ihb =>
    exact ⟨ihA h.1 hσ, ihb h.2.1 (hup hσ),
      (isKind_sub (fun i => (hup hσ i).2) _).trans h.2.2⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 hσ, ihB h.2 (hup hσ)⟩

theorem Good.subst (hb : Good b) (ha : Good a) (hka : isKind a = false) :
    Good (subst 0 a b) := by
  rw [subst_eq_sub]
  apply hb.substitute
  intro i
  cases i with
  | zero => exact ⟨ha, hka⟩
  | succ => exact ⟨True.intro, rfl⟩

theorem Good.step (ht : Good t) (h : Step t u) : Good u ∧ isKind u = isKind t := by
  induction h with
  | beta A b a =>
    exact ⟨ht.1.2.1.subst ht.2.1 ht.2.2, (isKind_subst ht.2.2 _).trans ht.1.2.2⟩
  | appFun a h ih => exact ⟨⟨(ih ht.1).1, ht.2⟩, rfl⟩
  | appArg f h ih =>
    obtain ⟨ha, he⟩ := ih ht.2.1
    exact ⟨⟨ht.1, ha, he.trans ht.2.2⟩, rfl⟩
  | lamTy b h ih => exact ⟨⟨(ih ht.1).1, ht.2⟩, rfl⟩
  | lamBody A h ih =>
    obtain ⟨hb, he⟩ := ih ht.2.1
    exact ⟨⟨ht.1, hb, he.trans ht.2.2⟩, rfl⟩
  | piDom B h ih => exact ⟨⟨(ih ht.1).1, ht.2⟩, rfl⟩
  | piCod A h ih => exact ⟨⟨ht.1, (ih ht.2).1⟩, (ih ht.2).2⟩

def TwoSortClass (t A : Tm) : Prop :=
  NoTypes t ∧ Good t ∧ if isKind t then A = .srt (.type 0) else NoTypes A

theorem TwoSortClass.type_of_kind (h : TwoSortClass t A) (hk : isKind t = true) :
    A = .srt (.type 0) := by
  simpa only [hk, Bool.true_eq, ↓reduceIte] using h.2.2

theorem TwoSortClass.nonkind (h : TwoSortClass t A) (hA : NoTypes A) :
    isKind t = false := by
  cases hk : isKind t with
  | false => rfl
  | true =>
    rw [h.type_of_kind hk] at hA
    exact hA.elim

theorem two_sort_classification (h : BoundedTyping 1 Γ t A) : TwoSortClass t A := by
  induction h using BoundedTyping.rec
      (motive_1 := fun Γ _ => ∀ (i : Nat) (A : Tm), Γ[i]? = some A → NoTypes A) with
  | nil i A hi => simp at hi
  | cons hw hA ihw ihA i C hi =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst C
      exact ihA.1
    | succ i => exact ihw i C hi
  | srt hw ha hs hs' ihw =>
    cases ha with
    | prop => exact ⟨True.intro, True.intro, rfl⟩
    | type i => simp only [sortRank] at hs'; omega
  | var hw hi ihw =>
    refine ⟨True.intro, True.intro, ?_⟩
    rw [← ren_shift]
    exact (ihw _ _ hi).rename _
  | @pi Γ A s₁ B s₂ s₃ hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    refine ⟨⟨ihA.1, ihB.1⟩, ⟨ihA.2.1, ihB.2.1⟩, ?_⟩
    cases hr with
    | prop s =>
      have hk := ihB.nonkind (by trivial)
      simp only [isKind, hk, Bool.false_eq_true, ↓reduceIte]
      trivial
    | type i j =>
      have hi : i = 0 := by simp only [sortRank] at hs₁; omega
      have hj : j = 0 := by simp only [sortRank] at hs₂; omega
      subst i; subst j
      cases hk : isKind B with
      | false =>
        have hf : False := by simpa only [hk, Bool.false_eq_true, ↓reduceIte, NoTypes] using ihB.2.2
        exact hf.elim
      | true => simp only [isKind, hk, ↓reduceIte] <;> rfl
    | propType i =>
      have hi : i = 0 := by simp only [sortRank] at hs₂; omega
      subst i
      cases hk : isKind B with
      | false =>
        have hf : False := by simpa only [hk, Bool.false_eq_true, ↓reduceIte, NoTypes] using ihB.2.2
        exact hf.elim
      | true => simp only [isKind, hk, ↓reduceIte] <;> rfl
  | lam hPi hb hs ihPi ihb =>
    exact ⟨⟨ihPi.1.1, ihb.1⟩, ⟨ihPi.2.1.1, ihb.2.1, ihb.nonkind ihPi.1.2⟩, ihPi.1⟩
  | @app Γ f A B a hf ha ihf iha =>
    have hPi' : NoTypes (.pi A B) := by
      cases hk : isKind f with
      | false => simpa only [hk, Bool.false_eq_true, ↓reduceIte] using ihf.2.2
      | true => have he := ihf.type_of_kind hk; cases he
    exact ⟨⟨ihf.1, iha.1⟩, ⟨ihf.2.1, iha.2.1, iha.nonkind hPi'.1⟩,
      hPi'.2.subst iha.1⟩
  | @conv Γ t A B s ht hB hc hs iht ihB =>
    refine ⟨iht.1, iht.2.1, ?_⟩
    cases hk : isKind t with
    | false => simpa only [hk, Bool.false_eq_true, ↓reduceIte] using ihB.1
    | true =>
      have he := iht.type_of_kind hk
      rw [he] at hc
      exact (ihB.1.not_conv_type (conv_symm hc)).elim

theorem BoundedTyping.one_noTypes (h : BoundedTyping 1 Γ t A) : NoTypes t :=
  (two_sort_classification h).1

theorem BoundedTyping.one_good (h : BoundedTyping 1 Γ t A) : Good t :=
  (two_sort_classification h).2.1

theorem BoundedTyping.one_kind_iff (h : BoundedTyping 1 Γ t A) :
    isKind t = true ↔ A = .srt (.type 0) := by
  constructor
  · exact (two_sort_classification h).type_of_kind
  · intro he
    have hh := (two_sort_classification h).2.2
    cases hk : isKind t with
    | true => rfl
    | false =>
      have hA : NoTypes A := by simpa only [hk, Bool.false_eq_true, ↓reduceIte] using hh
      rw [he] at hA
      exact hA.elim

end Submission.Helpers
