import Submission.TwoSortSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def ValueContext (Γ : List Tm) (ρ : Nat → Value) : Prop := valueCodes ρ = ctxArity Γ

theorem ValueContext.up {x : Value} (h : ValueContext Γ ρ) (hx : x.code = arity A) :
    ValueContext (A :: Γ) (push x ρ) := by
  change valueCodes ρ = ctxArity Γ at h
  simp only [ValueContext, valueCodes_push, hx, h, ctxArity_cons]

theorem semantics_typed_code (h : BoundedTyping 1 Γ t A) (hρ : ValueContext Γ ρ) :
    (semantics ρ t).1.code = arity A := by
  rw [semantics_code, hρ, two_sort_infer_arity h]

theorem candidatePi_congr (A : Arity) (d : Value → Candidate)
    (c c' : Value → Value → Candidate) (hc : ∀ x, x.code = A → c x = c' x) :
    candidatePi A d c = candidatePi A d c' := by
  funext f
  unfold candidatePi
  congr 1
  funext x
  rw [hc ⟨A, x⟩ rfl]

theorem piSemantics_congr (A B : Arity) (d : Value → Candidate)
    (c c' : Value → Value → Candidate) (hc : ∀ x, x.code = A → c x = c' x) :
    piSemantics A B d c = piSemantics A B d c' := by
  simp only [piSemantics, candidatePi_congr A d c c' hc]

theorem semantics_step (h : BoundedTyping 1 Γ t T) (hρ : ValueContext Γ ρ)
    (hs : Step t u) : semantics ρ t = semantics ρ u := by
  induction hs generalizing Γ T ρ with
  | beta A b a =>
    obtain ⟨C, D, hf, ha, _⟩ := h.generation
    obtain ⟨B, s, hPi, hb, _, hc⟩ := hf.generation
    obtain ⟨hAC, _⟩ := conv_pi_inj hc
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sPi, hPi'⟩ := hf.pi_type
    obtain ⟨sC, hC, _⟩ := hPi'.pi_domain
    apply semantics_beta ρ (ha.one_nonkind hC) hf.one_good.2.2
    rw [hρ, two_sort_infer_arity ha]
    exact arity_conv hC.one_good hA.one_good (conv_symm hAC)
  | appFun a hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    simp only [semantics, ih hf hρ]
  | appArg f hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    simp only [semantics, ih ha hρ]
  | lamTy b hs ih =>
    have he := h.one_good.1.arity_step hs
    simp only [semantics, he]
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    have hb' := hb.preservation hs
    have hc : inferArity (push (arity A) (valueCodes ρ)) b' =
        inferArity (push (arity A) (valueCodes ρ)) b := by
      rw [hρ, ← ctxArity_cons, two_sort_infer_arity hb, two_sort_infer_arity hb']
    simp only [semantics, hc]
    apply congrArg (fun v : Value => (v, fun _ : Value => v.asCandidate))
    apply Value.lambda_congr
    intro x hx
    exact congrArg Prod.fst (ih hb (hρ.up hx))
  | piDom B hs ih =>
    obtain ⟨s₁, s₂, s₃, hA, hB, _, _, _, _, _⟩ := h.generation
    have hk := hA.one_good.arity_step hs
    simp only [semantics, hk, ih hA hρ]
  | @piCod A B B' hs ih =>
    obtain ⟨s₁, s₂, s₃, hA, hB, _, _, _, _, _⟩ := h.generation
    have hk := hB.one_good.arity_step hs
    simp only [semantics, hk]
    apply piSemantics_congr
    intro x hx
    exact congrArg Prod.snd (ih hB (hρ.up hx))

theorem semantics_steps (h : BoundedTyping 1 Γ t A) (hρ : ValueContext Γ ρ)
    (hs : Steps t u) : semantics ρ t = semantics ρ u := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact (semantics_step h hρ hs).trans (ih (h.preservation hs))

def TypedOrSort (Γ : List Tm) (t : Tm) : Prop :=
  (∃ A, BoundedTyping 1 Γ t A) ∨ ∃ s, t = .srt s

theorem TypedOrSort.semantics_red (h : TypedOrSort Γ t) (hρ : ValueContext Γ ρ)
    (hs : Red t u) : semantics ρ t = semantics ρ u := by
  rcases h with ⟨A, ht⟩ | ⟨s, he⟩
  · exact semantics_steps ht hρ hs.steps
  · have he' := red_srt hs s he
    rw [he, he']

theorem semantics_conv (ht : TypedOrSort Γ t) (hu : TypedOrSort Γ u)
    (hρ : ValueContext Γ ρ) (hc : Conv t u) : semantics ρ t = semantics ρ u := by
  obtain ⟨v, hv, hv'⟩ := conv_join hc
  exact (ht.semantics_red hρ hv).trans (hu.semantics_red hρ hv').symm

theorem type_semantics_conv (ht : BoundedTyping 1 Γ t A)
    (hB : BoundedTyping 1 Γ B (.srt s)) (hρ : ValueContext Γ ρ) (hc : Conv A B) :
    semantics ρ A = semantics ρ B := by
  apply semantics_conv ?_ (.inl ⟨_, hB⟩) hρ hc
  rcases ht.regularity with hs | ⟨s, hA⟩
  · exact .inr hs
  · exact .inl ⟨_, hA⟩

theorem semantics_pi {v : Value} (ρ : Nat → Value) (hv : v.code = arity (.pi A B)) :
    (semantics ρ (.pi A B)).2 v =
      candidatePi (arity A) (semantics ρ A).2
        (fun x => (semantics (push x ρ) B).2) v := by
  change (piSemantics _ _ _ _).2 v = _
  unfold piSemantics
  split
  · rename_i hb
    have hc : v.code = .unit := by simpa only [arity, hb, Arity.arrow] using hv
    rw [v.eq_unit hc]
  · rfl

theorem semantics_lambda_apply {x : Value} (ρ : Nat → Value) (A b : Tm)
    (hx : x.code = arity A) :
    (semantics ρ (.lam A b)).1.apply x = (semantics (push x ρ) b).1 := by
  simp only [semantics]
  apply Value.lambda_apply _ _ _ x hx
  rw [semantics_code, valueCodes_push, hx]

end Submission.Helpers
