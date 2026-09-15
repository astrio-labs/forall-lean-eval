import Submission.BoundedPreservation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Every sort occurring in the syntax has rank strictly below the given bound. -/
def SortsBelow (n : Nat) : Tm → Prop
  | .var _ => True
  | .srt s => sortRank s < n
  | .app f a => SortsBelow n f ∧ SortsBelow n a
  | .lam A b => SortsBelow n A ∧ SortsBelow n b
  | .pi A B => SortsBelow n A ∧ SortsBelow n B

theorem ax_rank (h : Ax s s') : sortRank s' = sortRank s + 1 := by
  cases h <;> rfl

theorem SortsBelow.rename (h : SortsBelow n t) (ρ : Nat → Nat) :
    SortsBelow n (ren ρ t) := by
  induction t generalizing ρ with
  | var => trivial
  | srt => exact h
  | app f a ihf iha => exact ⟨ihf h.1 _, iha h.2 _⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 _, ihb h.2 _⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 _, ihB h.2 _⟩

theorem SortsBelow.substitute (h : SortsBelow n t)
    (hσ : ∀ i, SortsBelow n (σ i)) : SortsBelow n (sub σ t) := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, SortsBelow n (σ i)) :
      ∀ i, SortsBelow n (upSub σ i) := by
    intro i
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).rename _
  induction t generalizing σ with
  | var i => exact hσ i
  | srt => exact h
  | app f a ihf iha => exact ⟨ihf h.1 hσ, iha h.2 hσ⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 hσ, ihb h.2 (hup hσ)⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 hσ, ihB h.2 (hup hσ)⟩

theorem SortsBelow.subst (hb : SortsBelow n b) (ha : SortsBelow n a) :
    SortsBelow n (subst 0 a b) := by
  rw [subst_eq_sub]
  apply hb.substitute
  intro i
  cases i with
  | zero => exact ha
  | succ => trivial

theorem SortsBelow.parallel (h : SortsBelow n t) (hs : Par t u) : SortsBelow n u := by
  induction hs with
  | var => trivial
  | srt => exact h
  | app _ _ ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | pi _ _ ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | beta A _ _ ihb iha => exact (ihb h.1.2).subst (iha h.2)

theorem SortsBelow.reduction (h : SortsBelow n t) (hs : Red t u) : SortsBelow n u := by
  induction hs with
  | refl => exact h
  | head hs hr ih => exact ih (h.parallel hs)

theorem SortsBelow.conv_sort (h : SortsBelow n t) (hc : Conv t (.srt s)) :
    sortRank s < n := by
  obtain ⟨u, hu, hu'⟩ := conv_join hc
  have he := red_srt hu' s rfl
  subst u
  exact h.reduction hu

/-- The top sort of a bounded system cannot occur inside one of its typable terms. -/
theorem BoundedTyping.sorts_below (h : BoundedTyping n Γ t A) : SortsBelow n t := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw ha hs hs' ihw =>
    change sortRank _ < n
    have he := ax_rank ha
    omega
  | var => trivial
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB => exact ⟨ihA, ihB⟩
  | lam hPi hb hs ihPi ihb => exact ⟨ihPi.1, ihb⟩
  | app hf ha ihf iha => exact ⟨ihf, iha⟩
  | conv ht hB hc hs iht ihB => exact iht

theorem BoundedWf.lookup_sorts_below {i : Nat} (h : BoundedWf n Γ) (hi : Γ[i]? = some A) :
    SortsBelow n A := by
  induction Γ generalizing i with
  | nil => simp at hi
  | cons C Γ ih =>
    cases h with
    | cons hw hC =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst A
        exact hC.sorts_below
      | succ i => exact ih hw hi

theorem BoundedTyping.sort_bound (h : BoundedTyping n Γ t (.srt s)) :
    sortRank s ≤ n := by
  cases t with
  | var i =>
    obtain ⟨A, hi, hc⟩ := h.generation
    have hb := (h.wf.lookup_sorts_below hi).rename (shift (i + 1) 0)
    rw [ren_shift] at hb
    exact Nat.le_of_lt (hb.conv_sort hc)
  | srt s₀ =>
    obtain ⟨s', ha, hs₀, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    cases he
    exact hs'
  | pi A B =>
    obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have he := conv_srt_inj hc
    cases he
    exact hs₃
  | lam A b =>
    obtain ⟨B, s', hPi, hb, hs', hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | app f a =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    obtain ⟨s', hPi⟩ := hf.pi_type
    have hb := hPi.sorts_below.2.subst ha.sorts_below
    exact Nat.le_of_lt (hb.conv_sort hc)

/-- A type is either a sort within the bound, or contains only strictly lower sorts. -/
theorem BoundedTyping.type_sorts (h : BoundedTyping n Γ t A) :
    SortsBelow n A ∨ ∃ s, A = .srt s ∧ sortRank s ≤ n := by
  rcases h.regularity with ⟨s, he⟩ | ⟨s, hA⟩
  · subst A
    exact .inr ⟨s, rfl, h.sort_bound⟩
  · exact .inl hA.sorts_below

theorem BoundedTyping.pi_components (h : BoundedTyping n Γ f (.pi A B)) :
    SortsBelow n A ∧ SortsBelow n B := by
  obtain ⟨s, hPi⟩ := h.pi_type
  exact hPi.sorts_below

/-- A sort at or above the bound is not typable at that bound. -/
theorem BoundedTyping.no_top_sort (h : BoundedTyping n Γ (.srt s) A)
    (hs : n ≤ sortRank s) : False :=
  Nat.not_lt_of_ge hs h.sorts_below

theorem BoundedWf.sort_typing (hw : BoundedWf n Γ) (hs : sortRank s < n) :
    ∃ s', BoundedTyping n Γ (.srt s) (.srt s') ∧ sortRank s' ≤ n := by
  cases s with
  | prop =>
    refine ⟨.type 0, .srt hw .prop (by simp [sortRank]) ?_, ?_⟩ <;>
      simp only [sortRank] at * <;> omega
  | type i =>
    refine ⟨.type (i + 1), .srt hw (.type i) (Nat.le_of_lt hs) ?_, ?_⟩ <;>
      simp only [sortRank] at * <;> omega

/-- Every type is well typed at the same bound unless it is the top sort itself. -/
theorem BoundedTyping.regularity_top (h : BoundedTyping n Γ t A) :
    (∃ s, A = .srt s ∧ sortRank s = n) ∨
      ∃ s, BoundedTyping n Γ A (.srt s) ∧ sortRank s ≤ n := by
  rcases h.regularity with ⟨s, he⟩ | ⟨s, hA⟩
  · subst A
    by_cases hs : sortRank s < n
    · exact .inr (h.wf.sort_typing hs)
    · exact .inl ⟨s, rfl, Nat.le_antisymm h.sort_bound (Nat.le_of_not_gt hs)⟩
  · exact .inr ⟨s, hA, hA.sort_bound⟩

/-- Reducing a type is admissible even when the system has a top sort. -/
theorem BoundedTyping.reduce_type (h : BoundedTyping n Γ t A) (hr : Red A B) :
    BoundedTyping n Γ t B := by
  rcases h.regularity with ⟨s, he⟩ | ⟨s, hA⟩
  · have he' := red_srt hr s he
    rw [he', ← he]
    exact h
  · exact .conv h (hA.preservation_red hr) hr.conv hA.sort_bound

/-- The part of a kind's syntax that can end in a specified sort. -/
def kindAt (q : Srt) : Tm → Bool
  | .srt s => decide (s = q)
  | .pi _ B => kindAt q B
  | _ => false

theorem kindAt_ren (q : Srt) (r : Nat → Nat) (t : Tm) :
    kindAt q (ren r t) = kindAt q t := by
  induction t generalizing r with
  | var => rfl
  | srt => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => exact ihB _

theorem kindAt_sub (hσ : ∀ i, kindAt q (σ i) = false) (t : Tm) :
    kindAt q (sub σ t) = kindAt q t := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, kindAt q (σ i) = false) :
      ∀ i, kindAt q (upSub σ i) = false := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (kindAt_ren _ _ _).trans (hσ i)
  induction t generalizing σ with
  | var i => exact hσ i
  | srt => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => exact ihB (hup hσ)

theorem kindAt_subst (ha : kindAt q a = false) (b : Tm) :
    kindAt q (subst 0 a b) = kindAt q b := by
  rw [subst_eq_sub]
  apply kindAt_sub
  intro i
  cases i with
  | zero => exact ha
  | succ => rfl

/-- A kind ending in the highest available sort has the untypable top sort as its type.
The converse need not hold for predicative products. -/
theorem BoundedTyping.kindAt_top (h : BoundedTyping n Γ t A)
    (hq : sortRank q + 1 = n) (hk : kindAt q t = true) :
    ∃ s, A = .srt s ∧ sortRank s = n := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | @srt Γ s s' hw ha hs hs' ihw =>
    have he : s = q := of_decide_eq_true hk
    subst s
    exact ⟨s', rfl, (ax_rank ha).trans hq⟩
  | var => cases hk
  | @pi Γ A s₁ B s₂ s₃ hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    obtain ⟨s, he, hs⟩ := ihB hk
    cases he
    refine ⟨s₃, rfl, ?_⟩
    cases hr with
    | prop s₁ => simp only [sortRank] at hs; omega
    | type i j =>
      simp only [sortRank] at hs hs₁ ⊢
      rw [Nat.max_eq_right (by omega)]
      exact hs
    | propType i => exact hs
  | lam => cases hk
  | app => cases hk
  | conv ht hB hc hs iht ihB =>
    obtain ⟨s, he, hs⟩ := iht hk
    have hc' := conv_symm hc
    rw [he] at hc'
    have hlt := hB.sorts_below.conv_sort hc'
    omega

/-- A well-typed argument can never itself be a top kind. -/
theorem BoundedTyping.not_kindAt (h : BoundedTyping n Γ t A)
    (hA : BoundedTyping n Γ A (.srt s)) (hq : sortRank q + 1 = n) :
    kindAt q t = false := by
  cases hk : kindAt q t with
  | false => rfl
  | true =>
    obtain ⟨s', he, hs'⟩ := h.kindAt_top hq hk
    have hb := hA.sorts_below
    rw [he] at hb
    have hlt : sortRank s' < n := hb
    omega

/-- Applications and abstractions exclude top kinds in the substitutable positions. -/
def GoodAt (q : Srt) : Tm → Prop
  | .var _ | .srt _ => True
  | .app f a => GoodAt q f ∧ GoodAt q a ∧ kindAt q a = false
  | .lam A b => GoodAt q A ∧ GoodAt q b ∧ kindAt q b = false
  | .pi A B => GoodAt q A ∧ GoodAt q B

theorem BoundedTyping.goodAt (h : BoundedTyping n Γ t A)
    (hq : sortRank q + 1 = n) : GoodAt q t := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt => trivial
  | var => trivial
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB => exact ⟨ihA, ihB⟩
  | lam hPi hb hs ihPi ihb =>
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    exact ⟨ihPi.1, ihb, hb.not_kindAt hB hq⟩
  | app hf ha ihf iha =>
    obtain ⟨sPi, hPi⟩ := hf.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    exact ⟨ihf, iha, ha.not_kindAt hA hq⟩
  | conv ht hB hc hs iht ihB => exact iht

theorem GoodAt.rename (h : GoodAt q t) (r : Nat → Nat) : GoodAt q (ren r t) := by
  induction t generalizing r with
  | var => trivial
  | srt => trivial
  | app f a ihf iha =>
    exact ⟨ihf h.1 _, iha h.2.1 _, (kindAt_ren _ _ _).trans h.2.2⟩
  | lam A b ihA ihb =>
    exact ⟨ihA h.1 _, ihb h.2.1 _, (kindAt_ren _ _ _).trans h.2.2⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 _, ihB h.2 _⟩

theorem GoodAt.substitute (h : GoodAt q t)
    (hσ : ∀ i, GoodAt q (σ i) ∧ kindAt q (σ i) = false) : GoodAt q (sub σ t) := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, GoodAt q (σ i) ∧ kindAt q (σ i) = false) :
      ∀ i, GoodAt q (upSub σ i) ∧ kindAt q (upSub σ i) = false := by
    intro i
    cases i with
    | zero => exact ⟨True.intro, rfl⟩
    | succ i => exact ⟨(hσ i).1.rename _, (kindAt_ren _ _ _).trans (hσ i).2⟩
  induction t generalizing σ with
  | var i => exact (hσ i).1
  | srt => trivial
  | app f a ihf iha =>
    exact ⟨ihf h.1 hσ, iha h.2.1 hσ,
      (kindAt_sub (fun i => (hσ i).2) _).trans h.2.2⟩
  | lam A b ihA ihb =>
    exact ⟨ihA h.1 hσ, ihb h.2.1 (hup hσ),
      (kindAt_sub (fun i => (hup hσ i).2) _).trans h.2.2⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 hσ, ihB h.2 (hup hσ)⟩

theorem GoodAt.subst (hb : GoodAt q b) (ha : GoodAt q a) (hka : kindAt q a = false) :
    GoodAt q (subst 0 a b) := by
  rw [subst_eq_sub]
  apply hb.substitute
  intro i
  cases i with
  | zero => exact ⟨ha, hka⟩
  | succ => exact ⟨True.intro, rfl⟩

theorem GoodAt.step (ht : GoodAt q t) (h : Step t u) :
    GoodAt q u ∧ kindAt q u = kindAt q t := by
  induction h with
  | beta A b a =>
    exact ⟨ht.1.2.1.subst ht.2.1 ht.2.2,
      (kindAt_subst ht.2.2 _).trans ht.1.2.2⟩
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

theorem GoodAt.steps (ht : GoodAt q t) (h : Steps t u) :
    GoodAt q u ∧ kindAt q u = kindAt q t := by
  induction h with
  | refl => exact ⟨ht, rfl⟩
  | head hs hr ih =>
    obtain ⟨hu, he⟩ := ht.step hs
    obtain ⟨hv, he'⟩ := ih hu
    exact ⟨hv, he'.trans he⟩

theorem GoodAt.reduction (ht : GoodAt q t) (h : Red t u) :
    GoodAt q u ∧ kindAt q u = kindAt q t := by
  induction h with
  | refl => exact ⟨ht, rfl⟩
  | head hs hr ih =>
    obtain ⟨hu, he⟩ := ht.steps hs.steps
    obtain ⟨hv, he'⟩ := ih hu
    exact ⟨hv, he'.trans he⟩

/-- Top-kind classification is invariant under conversion between well-typed terms. -/
theorem BoundedTyping.kindAt_conv (ht : BoundedTyping n Γ t A)
    (hu : BoundedTyping n Δ u B) (hq : sortRank q + 1 = n) (hc : Conv t u) :
    kindAt q t = kindAt q u := by
  obtain ⟨v, htv, huv⟩ := conv_join hc
  exact ((ht.goodAt hq).reduction htv).2.symm.trans ((hu.goodAt hq).reduction huv).2

end Submission.Helpers
