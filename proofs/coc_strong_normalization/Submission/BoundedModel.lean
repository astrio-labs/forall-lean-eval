import Submission.TowerCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-!
A source-facing interface for the semantic tower. Its assumptions are carrier
compatibility and equations for evaluation, products, weakening, substitution,
and conversion. In particular, it does not assume a fundamental lemma or that
any source term normalizes. The theorem below works for the original bounded
typing relation at every bound.
-/

structure BoundedModel (n : Nat) where
  Value : Type
  eval : List Tm → (Nat → Value) → Tm → Value
  candidate : List Tm → (Nat → Value) → Tm → Value → Candidate
  admissible : List Tm → (Nat → Value) → Prop
  valid : List Tm → (Nat → Value) → Tm → Value → Prop
  apply : List Tm → (Nat → Value) → Tm → Tm → Value → Value → Value
  environment : ∀ Γ, ∃ ρ, admissible Γ ρ
  point : ∀ {Γ ρ A s}, BoundedTyping n Γ A (.srt s) → admissible Γ ρ →
    ∃ x, valid Γ ρ A x
  extend : ∀ {Γ ρ A s x}, BoundedTyping n Γ A (.srt s) → admissible Γ ρ →
    valid Γ ρ A x → admissible (A :: Γ) (push x ρ)
  typed : ∀ {Γ ρ t A}, BoundedTyping n Γ t A → admissible Γ ρ →
    valid Γ ρ A (eval Γ ρ t)
  variable_value : ∀ {Γ ρ j A}, BoundedWf n Γ → Γ[j]? = some A → admissible Γ ρ →
    eval Γ ρ (.var j) = ρ j
  sort : ∀ Γ ρ s x, candidate Γ ρ (.srt s) x = Candidate.sn
  weaken : ∀ {Γ ρ A s C r x}, BoundedTyping n Γ A (.srt s) →
    BoundedTyping n Γ C (.srt r) → admissible Γ ρ → valid Γ ρ A x →
    candidate (A :: Γ) (push x ρ) (ren Nat.succ C) = candidate Γ ρ C
  product : ∀ {Γ ρ A B s f}, BoundedTyping n Γ (.pi A B) (.srt s) →
    admissible Γ ρ → valid Γ ρ (.pi A B) f →
    candidate Γ ρ (.pi A B) f =
      Candidate.inter (fun x : {x : Value // valid Γ ρ A x} =>
        (candidate Γ ρ A x.1).arrow
          (candidate (A :: Γ) (push x.1 ρ) B (apply Γ ρ A B f x.1)))
  application : ∀ {Γ ρ f a A B}, BoundedTyping n Γ f (.pi A B) →
    BoundedTyping n Γ a A → admissible Γ ρ →
    eval Γ ρ (.app f a) = apply Γ ρ A B (eval Γ ρ f) (eval Γ ρ a)
  abstraction : ∀ {Γ ρ A B b s x}, BoundedTyping n Γ (.pi A B) (.srt s) →
    BoundedTyping n (A :: Γ) b B → admissible Γ ρ → valid Γ ρ A x →
    apply Γ ρ A B (eval Γ ρ (.lam A b)) x = eval (A :: Γ) (push x ρ) b
  substitution : ∀ {Γ ρ A B a sA sB}, BoundedTyping n Γ A (.srt sA) →
    BoundedTyping n (A :: Γ) B (.srt sB) → BoundedTyping n Γ a A →
    admissible Γ ρ → candidate Γ ρ (subst 0 a B) =
      candidate (A :: Γ) (push (eval Γ ρ a) ρ) B
  conversion : ∀ {Γ ρ t A B s}, BoundedTyping n Γ t A →
    BoundedTyping n Γ B (.srt s) → Conv A B → admissible Γ ρ →
    candidate Γ ρ A = candidate Γ ρ B

def BoundedModel.RealizesContext (M : BoundedModel n) (Γ : List Tm)
    (ρ : Nat → M.Value) (σ : Nat → Tm) : Prop :=
  ∀ j A, Γ[j]? = some A →
    (M.candidate Γ ρ (lift (j + 1) 0 A) (ρ j)).contains (σ j)

theorem BoundedModel.RealizesContext.identity (M : BoundedModel n) (Γ : List Tm)
    (ρ : Nat → M.Value) : M.RealizesContext Γ ρ Tm.var := by
  intro j A hj
  exact (M.candidate Γ ρ (lift (j + 1) 0 A) (ρ j)).var j

theorem BoundedModel.RealizesContext.up {M : BoundedModel n}
    {Γ : List Tm} {ρ : Nat → M.Value} {σ : Nat → Tm} {x : M.Value}
    (hσ : M.RealizesContext Γ ρ σ) (hA : BoundedTyping n Γ A (.srt s))
    (hρ : M.admissible Γ ρ) (hx : M.valid Γ ρ A x)
    (ha : (M.candidate Γ ρ A x).contains a) :
    M.RealizesContext (A :: Γ) (push x ρ) (push a σ) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one, M.weaken hA hA hρ hx] using ha
  | succ j =>
    obtain ⟨r, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1), M.weaken hA hC hρ hx] using hσ j C hj

/-- The full fundamental lemma is uniform in the source bound and the semantic
value representation. All hypotheses of `BoundedModel` are interpretation laws. -/
theorem bounded_model_fundamental (M : BoundedModel n)
    {ρ : Nat → M.Value} {σ : Nat → Tm} (h : BoundedTyping n Γ t A)
    (hρ : M.admissible Γ ρ) (hσ : M.RealizesContext Γ ρ σ) :
    (M.candidate Γ ρ A (M.eval Γ ρ t)).contains (sub σ t) := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True)
      generalizing ρ σ with
  | nil => trivial
  | cons => trivial
  | srt hw ha hs hs' ihw =>
    rw [M.sort]
    exact Acc.intro _ (by intro u hu; cases hu)
  | var hw hi ihw =>
    rw [M.variable_value hw hi hρ]
    exact hσ _ _ hi
  | @pi Γ A sA B sB s hA hB hr hsA hsB hs ihA ihB =>
    rw [M.sort]
    have ha := ihA hρ hσ
    rw [M.sort] at ha
    obtain ⟨x, hx⟩ := M.point hA hρ
    have hb := ihB (M.extend hA hρ hx)
      (hσ.up hA hρ hx ((M.candidate Γ ρ A x).var 0))
    rw [M.sort] at hb
    exact sn_pi ha (sn_under_binder σ B hb)
  | @lam Γ A B s b hPi hb hs ihPi ihb =>
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    have hsn := ihPi hρ hσ
    rw [M.sort] at hsn
    have hD : SN (sub σ A) := sn_pi_domain hsn
    have ht : BoundedTyping n Γ (.lam A b) (.pi A B) := .lam hPi hb hs
    rw [M.product hPi hρ (M.typed ht hρ)]
    have hh (x : {x : M.Value // M.valid Γ ρ A x}) :
        ((M.candidate Γ ρ A x.1).arrow
          (M.candidate (A :: Γ) (push x.1 ρ) B
            (M.apply Γ ρ A B (M.eval Γ ρ (.lam A b)) x.1))).contains
              (.lam (sub σ A) (sub (upSub σ) b)) := by
      rw [M.abstraction hPi hb hρ x.2]
      apply Candidate.lambda _ _ hD
      intro a ha
      rw [sub_push_beta]
      exact ihb (M.extend hA hρ x.2) (hσ.up hA hρ x.2 ha)
    obtain ⟨x, hx⟩ := M.point hA hρ
    exact ⟨(hh ⟨x, hx⟩).1, hh⟩
  | @app Γ f A B a hf ha ihf iha =>
    obtain ⟨sPi, hPi⟩ := hf.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hh := ihf hρ hσ
    rw [M.product hPi hρ (M.typed hf hρ)] at hh
    rw [M.substitution hA hB ha hρ, M.application hf ha hρ]
    exact (hh.2 ⟨M.eval Γ ρ a, M.typed ha hρ⟩).2 _ (iha hρ hσ)
  | conv ht hB hc hs iht ihB =>
    rw [← M.conversion ht hB hc hρ]
    exact iht hρ hσ

/-- An actual model gives unconditional normalization at its source bound. -/
theorem bounded_model_normalization (M : BoundedModel n)
    (h : BoundedTyping n Γ t A) : SN t := by
  obtain ⟨ρ, hρ⟩ := M.environment Γ
  have hc := bounded_model_fundamental M h hρ (BoundedModel.RealizesContext.identity M Γ ρ)
  simpa only [sub_var] using (M.candidate Γ ρ A (M.eval Γ ρ t)).normalizes hc

/-- Construction of source models at every finite bound suffices for CCω. -/
theorem normalization_of_bounded_models (models : ∀ n, Nonempty (BoundedModel n))
    (h : Typing Γ t A) : SN t := by
  apply normalization_of_bounded ?_ h
  intro n Δ u B hu
  obtain ⟨M⟩ := models n
  exact bounded_model_normalization M hu

/-- The checked bound-two theorem discharges every smaller bound. What remains
is construction of source models at bounds three and above. -/
theorem normalization_of_successor_models
    (models : ∀ n, 3 ≤ n → Nonempty (BoundedModel n)) (h : Typing Γ t A) : SN t := by
  apply normalization_of_bounded ?_ h
  intro n Δ u B hu
  by_cases hn : n ≤ 2
  · exact bound_two_normalization (hu.mono hn)
  · obtain ⟨M⟩ := models n (by omega)
    exact bounded_model_normalization M hu

/-
`ThirdModel.lean` now constructs `BoundedModel 3`, including source product
factorization and stability under typed substitution and conversion. The
remaining obligation is a uniform successor construction. The carrier tower
alone is not a source model, and singleton top arity does not imply a smaller
source universe bound.
-/

end Submission.Helpers
