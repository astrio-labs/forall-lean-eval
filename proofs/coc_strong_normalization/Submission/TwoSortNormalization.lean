import Submission.TwoSortSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def RealizesContext (Γ : List Tm) (ρ : Nat → Value) (σ : Nat → Tm) : Prop :=
  ∀ i A, Γ[i]? = some A →
    ((semantics ρ (lift (i + 1) 0 A)).2 (ρ i)).contains (σ i)

theorem RealizesContext.up (h : RealizesContext Γ ρ σ)
    (ha : ((semantics ρ A).2 x).contains a) :
    RealizesContext (A :: Γ) (push x ρ) (push a σ) := by
  intro i C hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      semantics_ren ρ (push x ρ) Nat.succ (fun _ => rfl)] using ha
  | succ i =>
    simpa only [push, ← ren_succ_lift (i + 1),
      semantics_ren ρ (push x ρ) Nat.succ (fun _ => rfl)] using h i C hi

theorem sub_push_beta (σ : Nat → Tm) (a b : Tm) :
    subst 0 a (sub (upSub σ) b) = sub (push a σ) b := by
  rw [subst_eq_sub, sub_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact single_ren_succ a (σ i)

theorem sn_under_binder (σ : Nat → Tm) (b : Tm)
    (h : SN (sub (push (.var 0) σ) b)) : SN (sub (upSub σ) b) := by
  apply sn_of_sub (single (.var 0))
  simpa only [← subst_eq_sub, sub_push_beta] using h

theorem sn_reflect (F : Tm → Tm) (hF : ∀ {t u}, Step t u → Step (F t) (F u))
    (h : SN (F t)) : SN t := by
  generalize he : F t = v at h
  induction h generalizing t with
  | intro v hv ih =>
    apply Acc.intro
    intro u hu
    apply ih (F u)
    · rw [← he]
      exact hF hu
    · rfl

theorem sn_pi_domain (h : SN (.pi A B)) : SN A :=
  sn_reflect (fun A => .pi A B) (Step.piDom B) h

/-- Fundamental lemma for all substitutions realizing a two-sort context. -/
theorem two_sort_fundamental (h : BoundedTyping 1 Γ t A)
    (hρ : ValueContext Γ ρ) (hσ : RealizesContext Γ ρ σ) :
    ((semantics ρ A).2 (semantics ρ t).1).contains (sub σ t) := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True)
      generalizing ρ σ with
  | nil => trivial
  | cons => trivial
  | srt hw ha hs hs' ihw =>
    change SN (.srt _)
    apply Acc.intro
    intro u hu
    cases hu
  | var hw hi ihw => exact hσ _ _ hi
  | @pi Γ A s₁ B s₂ s₃ hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    have ha : SN (sub σ A) := ihA hρ hσ
    let x : Value := ⟨arity A, (arity A).point⟩
    have hx : x.code = arity A := rfl
    have hb : SN (sub (push (.var 0) σ) B) :=
      ihB (hρ.up hx) (hσ.up (((semantics ρ A).2 x).var 0))
    exact sn_pi ha (sn_under_binder σ B hb)
  | @lam Γ A B s b hPi hb hs ihPi ihb =>
    have hD : SN (sub σ A) := sn_pi_domain (ihPi hρ hσ)
    have hcode := semantics_typed_code (BoundedTyping.lam hPi hb hs) hρ
    rw [semantics_pi ρ hcode]
    have hh (x : (arity A).El) :
        (((semantics ρ A).2 ⟨arity A, x⟩).arrow
          ((semantics (push ⟨arity A, x⟩ ρ) B).2
            ((semantics ρ (.lam A b)).1.apply ⟨arity A, x⟩))).contains
          (.lam (sub σ A) (sub (upSub σ) b)) := by
      rw [semantics_lambda_apply ρ A b rfl]
      apply Candidate.lambda _ _ hD
      intro a ha
      rw [sub_push_beta]
      exact ihb (hρ.up rfl) (hσ.up ha)
    exact ⟨(hh (arity A).point).1, hh⟩
  | @app Γ f A B a hf ha ihf iha =>
    obtain ⟨sPi, hPi⟩ := hf.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    have hf' := ihf hρ hσ
    rw [semantics_pi ρ (semantics_typed_code hf hρ)] at hf'
    have hcode := semantics_typed_code ha hρ
    have hx := (semantics ρ a).1.mk_cast hcode
    have hh := (hf'.2 ((semantics ρ a).1.cast (arity A))).2 (sub σ a)
    simp only [hx] at hh
    change ((semantics ρ (subst 0 a B)).2
      ((semantics ρ f).1.apply (semantics ρ a).1)).contains (.app (sub σ f) (sub σ a))
    rw [semantics_subst ρ (ha.one_nonkind hA)]
    exact hh (iha hρ hσ)
  | conv ht hB hc hs iht ihB =>
    rw [← type_semantics_conv ht hB hρ hc]
    exact iht hρ hσ

/-- Strong normalization for the first nonempty finite bound. -/
theorem two_sort_normalization (h : BoundedTyping 1 Γ t A) : SN t := by
  let ρ : Nat → Value := fun i => ⟨ctxArity Γ i, (ctxArity Γ i).point⟩
  have hρ : ValueContext Γ ρ := rfl
  have hσ : RealizesContext Γ ρ Tm.var := by
    intro i B hi
    exact ((semantics ρ (lift (i + 1) 0 B)).2 (ρ i)).var i
  have hc := two_sort_fundamental h hρ hσ
  simpa only [sub_var] using ((semantics ρ A).2 (semantics ρ t).1).normalizes hc

theorem BoundedTyping.normalize_le_one (h : BoundedTyping n Γ t A) (hn : n ≤ 1) : SN t :=
  two_sort_normalization (h.mono hn)

/-- Only bounds above the two-sort fragment remain for the full hierarchy. -/
theorem normalization_of_above_one
    (hSN : ∀ n, 2 ≤ n → ∀ Γ t A, BoundedTyping n Γ t A → SN t)
    (h : Typing Γ t A) : SN t := by
  obtain ⟨n, hn⟩ := typing_bounded h
  by_cases hs : n ≤ 1
  · exact hn.normalize_le_one hs
  · exact hSN n (by omega) Γ t A hn

end Submission.Helpers
