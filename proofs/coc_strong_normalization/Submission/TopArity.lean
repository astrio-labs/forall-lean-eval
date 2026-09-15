import Submission.TwoSortArity
import Submission.UniverseSyntax

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The simple arity at the highest available sort of a finite fragment. -/
def arityAt (q : Srt) : Tm → Arity
  | .srt s => if s = q then .prop else .unit
  | .pi A B => (arityAt q A).arrow (arityAt q B)
  | _ => .unit

theorem arityAt_unit_iff (q : Srt) (t : Tm) :
    arityAt q t = .unit ↔ kindAt q t = false := by
  induction t with
  | var => simp [arityAt, kindAt]
  | srt s => by_cases h : s = q <;> simp [arityAt, kindAt, h]
  | app => simp [arityAt, kindAt]
  | lam => simp [arityAt, kindAt]
  | pi A B ihA ihB => simpa only [arityAt, kindAt, Arity.arrow_unit_iff] using ihB

theorem arityAt_ren (q : Srt) (r : Nat → Nat) (t : Tm) :
    arityAt q (ren r t) = arityAt q t := by
  induction t generalizing r with
  | var => rfl
  | srt => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => simp only [ren, arityAt, ihA, ihB]

theorem arityAt_sub (hσ : ∀ i, kindAt q (σ i) = false) (t : Tm) :
    arityAt q (sub σ t) = arityAt q t := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, kindAt q (σ i) = false) :
      ∀ i, kindAt q (upSub σ i) = false := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (kindAt_ren _ _ _).trans (hσ i)
  induction t generalizing σ with
  | var i => exact (arityAt_unit_iff _ _).2 (hσ i)
  | srt => rfl
  | app => rfl
  | lam => rfl
  | pi A B ihA ihB => simp only [sub, arityAt, ihA hσ, ihB (hup hσ)]

theorem arityAt_subst (ha : kindAt q a = false) (b : Tm) :
    arityAt q (subst 0 a b) = arityAt q b := by
  rw [subst_eq_sub]
  apply arityAt_sub
  intro i
  cases i with
  | zero => exact ha
  | succ => rfl

theorem GoodAt.arity_step (ht : GoodAt q t) (h : Step t u) :
    arityAt q u = arityAt q t := by
  induction h with
  | beta A b a =>
    exact (arityAt_subst ht.2.2 _).trans ((arityAt_unit_iff _ _).2 ht.1.2.2)
  | appFun => rfl
  | appArg => rfl
  | lamTy => rfl
  | lamBody => rfl
  | piDom B h ih => exact congrArg (fun A => A.arrow (arityAt q B)) (ih ht.1)
  | piCod A h ih => exact congrArg (Arity.arrow (arityAt q A)) (ih ht.2)

theorem GoodAt.arity_steps (ht : GoodAt q t) (h : Steps t u) :
    GoodAt q u ∧ arityAt q u = arityAt q t := by
  induction h with
  | refl => exact ⟨ht, rfl⟩
  | head hs hr ih =>
    obtain ⟨hu, he⟩ := ih (ht.step hs).1
    exact ⟨hu, he.trans (ht.arity_step hs)⟩

theorem arityAt_conv (ht : GoodAt q t) (hu : GoodAt q u) (hc : Conv t u) :
    arityAt q t = arityAt q u := by
  obtain ⟨v, hv, hv'⟩ := conv_join hc
  exact (ht.arity_steps hv.steps).2.symm.trans (hu.arity_steps hv'.steps).2

theorem BoundedTyping.type_goodAt (h : BoundedTyping n Γ t A)
    (hq : sortRank q + 1 = n) : GoodAt q A := by
  rcases h.regularity with ⟨s, he⟩ | ⟨s, hA⟩
  · rw [he]; trivial
  · exact hA.goodAt hq

/-- Choosing a type is only used for its conversion-invariant arity. -/
noncomputable def chosenType (n : Nat) (Γ : List Tm) (t : Tm) : Tm := by
  classical
  exact if h : ∃ A, BoundedTyping n Γ t A then Classical.choose h else .srt .prop

theorem chosenType_typing (h : BoundedTyping n Γ t A) :
    BoundedTyping n Γ t (chosenType n Γ t) := by
  have hex : ∃ A, BoundedTyping n Γ t A := ⟨A, h⟩
  simp only [chosenType, dif_pos hex]
  exact Classical.choose_spec hex

noncomputable def inferredArityAt (n : Nat) (q : Srt) (Γ : List Tm) (t : Tm) : Arity :=
  arityAt q (chosenType n Γ t)

theorem inferredArityAt_eq (h : BoundedTyping n Γ t A) (hq : sortRank q + 1 = n) :
    inferredArityAt n q Γ t = arityAt q A := by
  have h' := chosenType_typing h
  exact arityAt_conv (h'.type_goodAt hq) (h.type_goodAt hq)
    (typing_unique h'.forget h.forget)

theorem inferredArityAt_var (hw : BoundedWf n Γ) (hi : Γ[i]? = some A)
    (hq : sortRank q + 1 = n) : inferredArityAt n q Γ (.var i) = arityAt q A := by
  rw [inferredArityAt_eq (.var hw hi) hq, ← ren_shift, arityAt_ren]

theorem inferredArityAt_lam (hPi : BoundedTyping n Γ (.pi A B) (.srt s))
    (hb : BoundedTyping n (A :: Γ) b B) (hq : sortRank q + 1 = n) :
    inferredArityAt n q Γ (.lam A b) =
      (arityAt q A).arrow (inferredArityAt n q (A :: Γ) b) := by
  rw [inferredArityAt_eq (.lam hPi hb hPi.sort_bound) hq, inferredArityAt_eq hb hq]
  rfl

theorem inferredArityAt_app (hf : BoundedTyping n Γ f (.pi A B))
    (ha : BoundedTyping n Γ a A) (hq : sortRank q + 1 = n) :
    inferredArityAt n q Γ (.app f a) = (inferredArityAt n q Γ f).codomain := by
  obtain ⟨sPi, hPi⟩ := hf.pi_type
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [inferredArityAt_eq (.app hf ha) hq, inferredArityAt_eq hf hq,
    arityAt, Arity.codomain_arrow]
  exact arityAt_subst (ha.not_kindAt hA hq) B

theorem inferredArityAt_ren (h : BoundedTyping n Γ t A)
    (hw : BoundedWf n Δ) (hr : RenCtx Γ Δ r) (hq : sortRank q + 1 = n) :
    inferredArityAt n q Δ (ren r t) = inferredArityAt n q Γ t := by
  rw [inferredArityAt_eq (h.rename hw hr) hq, inferredArityAt_eq h hq, arityAt_ren]

theorem inferredArityAt_subst (hb : BoundedTyping n (A :: Γ) b B)
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt s))
    (hq : sortRank q + 1 = n) :
    inferredArityAt n q Γ (subst 0 a b) = inferredArityAt n q (A :: Γ) b := by
  rw [inferredArityAt_eq (hb.subst ha) hq, inferredArityAt_eq hb hq]
  exact arityAt_subst (ha.not_kindAt hA hq) B

theorem inferredArityAt_substitute (h : BoundedTyping n Γ t A)
    (hw : BoundedWf n Δ) (hσ : BoundedSubCtx n Γ Δ σ)
    (hk : ∀ i, kindAt q (σ i) = false) (hq : sortRank q + 1 = n) :
    inferredArityAt n q Δ (sub σ t) = inferredArityAt n q Γ t := by
  rw [inferredArityAt_eq (h.substitute hw hσ) hq, inferredArityAt_eq h hq]
  exact arityAt_sub hk A

theorem inferredArityAt_step (h : BoundedTyping n Γ t A)
    (hs : Step t u) (hq : sortRank q + 1 = n) :
    inferredArityAt n q Γ u = inferredArityAt n q Γ t := by
  rw [inferredArityAt_eq (h.preservation hs) hq, inferredArityAt_eq h hq]

end Submission.Helpers
