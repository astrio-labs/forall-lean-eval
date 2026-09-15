import Submission.TwoSortStructure

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def push {α : Sort u} (x : α) (ρ : Nat → α) : Nat → α
  | 0 => x
  | i + 1 => ρ i

/-- The semantic carriers needed for the two-sort calculus. -/
inductive Arity where
  | unit
  | prop
  | fn (A B : Arity)
  deriving DecidableEq

def Arity.El : Arity → Type
  | .unit => Unit
  | .prop => Candidate
  | .fn A B => A.El → B.El

def Arity.point : (A : Arity) → A.El
  | .unit => ()
  | .prop => Candidate.sn
  | .fn _ B => fun _ => B.point

/-- Functions into the proof carrier are represented by its unique value. -/
def Arity.arrow (A : Arity) : Arity → Arity
  | .unit => .unit
  | B => .fn A B

def Arity.codomain : Arity → Arity
  | .fn _ B => B
  | _ => .unit

@[simp] theorem Arity.codomain_arrow (A B : Arity) : (A.arrow B).codomain = B := by
  cases B <;> rfl

@[simp] theorem Arity.arrow_unit_iff (A B : Arity) : A.arrow B = .unit ↔ B = .unit := by
  cases B <;> simp [Arity.arrow]

def arity : Tm → Arity
  | .srt .prop => .prop
  | .pi A B => (arity A).arrow (arity B)
  | _ => .unit

@[simp] theorem arity_unit_iff (t : Tm) : arity t = .unit ↔ isKind t = false := by
  induction t with
  | var => simp [arity, isKind]
  | srt s => cases s <;> simp [arity, isKind]
  | app => simp [arity, isKind]
  | lam => simp [arity, isKind]
  | pi A B ihA ihB => simpa only [arity, isKind, Arity.arrow_unit_iff] using ihB

@[simp] theorem arity_ren (ρ : Nat → Nat) (t : Tm) : arity (ren ρ t) = arity t := by
  induction t generalizing ρ with
  | var => rfl
  | srt s => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => simp only [ren, arity, ihA, ihB]

theorem arity_sub (hσ : ∀ i, isKind (σ i) = false) (t : Tm) :
    arity (sub σ t) = arity t := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, isKind (σ i) = false) :
      ∀ i, isKind (upSub σ i) = false := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (isKind_ren _ _).trans (hσ i)
  induction t generalizing σ with
  | var i => exact (arity_unit_iff _).2 (hσ i)
  | srt s => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => simp only [sub, arity, ihA hσ, ihB (hup hσ)]

theorem arity_subst (ha : isKind a = false) (b : Tm) :
    arity (subst 0 a b) = arity b := by
  rw [subst_eq_sub]
  apply arity_sub
  intro i
  cases i with
  | zero => exact ha
  | succ => rfl

theorem Good.arity_step (ht : Good t) (h : Step t u) : arity u = arity t := by
  induction h with
  | beta A b a =>
    exact (arity_subst ht.2.2 _).trans ((arity_unit_iff _).2 ht.1.2.2)
  | appFun => rfl
  | appArg => rfl
  | lamTy => rfl
  | lamBody => rfl
  | piDom B h ih => exact congrArg (fun A => A.arrow (arity B)) (ih ht.1)
  | piCod A h ih => exact congrArg (Arity.arrow (arity A)) (ih ht.2)

theorem Good.arity_steps (ht : Good t) (h : Steps t u) : Good u ∧ arity u = arity t := by
  induction h with
  | refl => exact ⟨ht, rfl⟩
  | head hs hr ih =>
    obtain ⟨hu, he⟩ := ih (ht.step hs).1
    exact ⟨hu, he.trans (ht.arity_step hs)⟩

theorem Red.steps (h : Red t u) : Steps t u := by
  induction h with
  | refl => exact .refl _
  | head hp hr ih => exact hp.steps.trans ih

theorem arity_conv (ht : Good t) (hu : Good u) (hc : Conv t u) : arity t = arity u := by
  obtain ⟨v, hv, hv'⟩ := conv_join hc
  exact (ht.arity_steps hv.steps).2.symm.trans (hu.arity_steps hv'.steps).2

theorem BoundedTyping.one_type_good (h : BoundedTyping 1 Γ t A) : Good A := by
  rcases h.regularity with ⟨s, he⟩ | ⟨s, hA⟩
  · rw [he]; trivial
  · exact hA.one_good

theorem BoundedTyping.one_nonkind (h : BoundedTyping 1 Γ t A)
    (hA : BoundedTyping 1 Γ A (.srt s)) : isKind t = false :=
  (two_sort_classification h).nonkind hA.one_noTypes

def ctxArity (Γ : List Tm) (i : Nat) : Arity :=
  match Γ[i]? with
  | some A => arity A
  | none => .unit

@[simp] theorem ctxArity_cons (Γ : List Tm) (A : Tm) :
    ctxArity (A :: Γ) = push (arity A) (ctxArity Γ) := by
  funext i
  cases i <;> rfl

def inferArity (γ : Nat → Arity) : Tm → Arity
  | .var i => γ i
  | .srt _ => .unit
  | .app f _ => (inferArity γ f).codomain
  | .lam A b => (arity A).arrow (inferArity (push (arity A) γ) b)
  | .pi _ B => if arity B = .unit then .prop else .unit

theorem inferArity_ren (γ δ : Nat → Arity) (ρ : Nat → Nat)
    (hρ : ∀ i, δ (ρ i) = γ i) (t : Tm) :
    inferArity δ (ren ρ t) = inferArity γ t := by
  have hup {γ δ : Nat → Arity} {ρ : Nat → Nat}
      (hρ : ∀ i, δ (ρ i) = γ i) (A : Arity) :
      ∀ i, push A δ (upRen ρ i) = push A γ i := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact hρ i
  induction t generalizing γ δ ρ with
  | var i => exact hρ i
  | srt => rfl
  | app f a ihf iha => exact congrArg Arity.codomain (ihf _ _ _ hρ)
  | lam A b ihA ihb =>
    simp only [ren, inferArity, arity_ren]
    rw [ihb _ _ _ (hup hρ _)]
  | pi A B ihA ihB => simp only [ren, inferArity, arity_ren]

theorem two_sort_infer_arity (h : BoundedTyping 1 Γ t A) :
    inferArity (ctxArity Γ) t = arity A := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw ha hs hs' ihw =>
    cases ha with
    | prop => rfl
    | type i => simp only [sortRank] at hs'; omega
  | var hw hi ihw => simp only [inferArity, ctxArity, hi, ← ren_shift, arity_ren]
  | @pi Γ A s₁ B s₂ s₃ hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    cases hr with
    | prop s =>
      have hk : isKind B = false := (two_sort_classification hB).nonkind True.intro
      simp only [inferArity, (arity_unit_iff _).2 hk, ↓reduceIte, arity]
    | type i j =>
      have hj : j = 0 := by simp only [sortRank] at hs₂; omega
      subst j
      have hk : isKind B = true := hB.one_kind_iff.mpr rfl
      have hne : arity B ≠ .unit := by
        intro he
        have := (arity_unit_iff _).1 he
        simp only [hk, Bool.true_eq_false] at this
      simp only [inferArity, hne, ↓reduceIte, arity]
    | propType i =>
      have hi : i = 0 := by simp only [sortRank] at hs₂; omega
      subst i
      have hk : isKind B = true := hB.one_kind_iff.mpr rfl
      have hne : arity B ≠ .unit := by
        intro he
        have := (arity_unit_iff _).1 he
        simp only [hk, Bool.true_eq_false] at this
      simp only [inferArity, hne, ↓reduceIte, arity]
  | lam hPi hb hs ihPi ihb =>
    simp only [ctxArity_cons] at ihb
    simpa only [inferArity, arity] using congrArg (Arity.arrow _) ihb
  | app hf ha ihf iha =>
    obtain ⟨sPi, hPi⟩ := hf.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    simp only [inferArity, ihf, arity, Arity.codomain_arrow, arity_subst (ha.one_nonkind hA)]
  | conv ht hB hc hs iht ihB =>
    exact iht.trans (arity_conv ht.one_type_good hB.one_good hc)

end Submission.Helpers
