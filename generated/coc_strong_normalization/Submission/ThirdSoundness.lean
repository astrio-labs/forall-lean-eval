import Submission.ThirdSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem middleSemantics_lam_apply (hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 3 (A :: Γ) b B) (hρ : ShapeContext (.type 1) Γ ρ)
    (hx : x.code = arityAt (.type 1) A) (hy : y.code = middleShape 3 1 Γ ρ A x) :
    middleApply (arityAt (.type 1) A) (fun x => middleShape 3 1 Γ ρ A x)
      (fun x z => middleShape 3 1 (A :: Γ) (push x ρ) B z)
      (shapeEval 3 1 Γ ρ (.lam A b)) (middleSemantics Γ ρ δ (.lam A b)).1 x y =
        (middleSemantics (A :: Γ) (push x ρ) (push y δ) b).1 := by
  rw [middleSemantics_lam hPi hb hρ]
  apply middleBeta _ _ _ _ _ _ _ hx hy
  rw [middleShapeEval_lam_apply hb hρ hx]
  exact middleSemantics_typed_code hb (hρ.up hx)

theorem thirdSemantics_below_compare
    (h : BoundedTyping 3 Γ t (.srt s)) (h' : BoundedTyping 3 Δ t' (.srt s)) (hs : sortRank s < 3)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (hk : nextArity 3 1 Γ ρ t = nextArity 3 1 Δ ρ' t')
    (hm : (middleSemantics Γ ρ δ t).1 = (middleSemantics Δ ρ' δ' t').1)
    (hv : (thirdSemantics Γ ρ δ ε t).1 = (thirdSemantics Δ ρ' δ' ε' t').1) :
    (thirdSemantics Γ ρ δ ε t).2 = (thirdSemantics Δ ρ' δ' ε' t').2 := by
  funext u f g
  rw [thirdSemantics_decode h hs hρ hδ, thirdSemantics_decode h' hs hρ' hδ', hk, hm, hv]

theorem thirdSemantics_context (h : BoundedTyping 3 Γ t T)
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ Tm.var)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ)
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ δ)
    (hε : ThirdContext Γ ρ δ ε) (hε' : ThirdContext Δ ρ δ ε) :
    (thirdSemantics Δ ρ δ ε t).1 = (thirdSemantics Γ ρ δ ε t).1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (thirdSemantics Δ ρ δ ε t).2 = (thirdSemantics Γ ρ δ ε t).2) := by
  have he := thirdSemantics_substitute_related h hw hσ (fun _ => rfl)
    hρ hρ' hδ hδ' hε hε' (fun _ _ _ => rfl) (by
      intro j C hj
      obtain ⟨D, hD, _⟩ := (hσ j C hj).generation
      exact middleSemantics_var hδ' hw hD hρ') (by
      intro j C hj
      obtain ⟨D, hD, _⟩ := (hσ j C hj).generation
      exact thirdSemantics_var hε' hw hD hρ' hδ')
  simpa only [sub_var] using he

theorem thirdSemantics_context_conversion (hb : BoundedTyping 3 (A :: Γ) b B)
    (hA : BoundedTyping 3 Γ A (.srt sA)) (hA' : BoundedTyping 3 Γ A' (.srt sA'))
    (hc : Conv A A') (hρ : ShapeContext (.type 1) Γ ρ)
    (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε)
    (hx : x.code = arityAt (.type 1) A) (hy : y.code = middleShape 3 1 Γ ρ A x)
    (hz : z.code = thirdShape Γ ρ δ A x y) :
    (thirdSemantics (A' :: Γ) (push x ρ) (push y δ) (push z ε) b).1 =
        (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1 ∧
    (∀ s, BoundedTyping 3 (A :: Γ) b (.srt s) →
      (thirdSemantics (A' :: Γ) (push x ρ) (push y δ) (push z ε) b).2 =
        (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) b).2) := by
  have hx' := hx.trans (arityAt_conv (hA.goodAt rfl) (hA'.goodAt rfl) hc)
  have hy' := hy.trans (middleShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) rfl hρ hc)
  have hz' := hz.trans (congrFun (congrFun
    (thirdShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hρ hδ hc) x) y)
  exact thirdSemantics_context hb (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hA.sort_bound hc)
    (hρ.up hx) (hρ.up hx') (hδ.up hA rfl hy) (hδ.up hA' rfl hy')
    (hε.up hA hρ hx hz) (hε.up hA' hρ hx' hz')

theorem thirdSemantics_beta_value (hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 3 (A :: Γ) b B) (ha : BoundedTyping 3 Γ a A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε) :
    (thirdSemantics Γ ρ δ ε (.app (.lam A b) a)).1 =
      (thirdSemantics Γ ρ δ ε (subst 0 a b)).1 := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [thirdSemantics_app (.lam hPi hb hPi.sort_bound) ha hρ hδ,
    thirdSemantics_lam hPi hb hρ hδ, thirdSemantics_subst_value hb ha hA hρ hδ hε]
  apply thirdBeta _ _ _ _ _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ)
    (middleSemantics_typed_code ha hρ) (thirdSemantics_typed_code ha hρ hδ)
  rw [middleShapeEval_lam_apply hb hρ (shapeEval_typed_code ha rfl hρ),
    middleSemantics_lam_apply hPi hb hρ (shapeEval_typed_code ha rfl hρ) (middleSemantics_typed_code ha hρ)]
  exact thirdSemantics_typed_code hb (hρ.up (shapeEval_typed_code ha rfl hρ))
    (hδ.up hA rfl (middleSemantics_typed_code ha hρ))

theorem thirdSemantics_step (h : BoundedTyping 3 Γ t T)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε)
    (hs : Step t t') :
    (thirdSemantics Γ ρ δ ε t).1 = (thirdSemantics Γ ρ δ ε t').1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (thirdSemantics Γ ρ δ ε t).2 = (thirdSemantics Γ ρ δ ε t').2) := by
  induction hs generalizing Γ T ρ δ ε with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, _⟩ := h.generation
    obtain ⟨B, s, hPi, hb, _, hc⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping 3 Γ a A := .conv ha hA (conv_symm (conv_pi_inj hc).1) hsA
    have hv := thirdSemantics_beta_value hPi hb ha' hρ hδ hε
    refine ⟨hv, ?_⟩
    intro s hs
    exact thirdSemantics_below_compare hs (hs.preservation (.beta A b a))
      hs.app_below_top hρ hρ hδ hδ
      (congrArg ShapeValue.asArity (shapeEval_step hs rfl hρ (.beta A b a)))
      (middleSemantics_step hs hρ hδ (.beta A b a)).1 hv
  | @appFun f f' a hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (thirdSemantics Γ ρ δ ε (.app f a)).1 = (thirdSemantics Γ ρ δ ε (.app f' a)).1 := by
      rw [thirdSemantics_app hf ha hρ hδ, thirdSemantics_app (hf.preservation hs) ha hρ hδ,
        shapeEval_step hf rfl hρ hs, (middleSemantics_step hf hρ hδ hs).1, (ih hf hρ hδ hε).1]
    refine ⟨hv, ?_⟩
    intro s ht
    exact thirdSemantics_below_compare ht (ht.preservation (.appFun a hs)) ht.app_below_top hρ hρ hδ hδ
      (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.appFun a hs)))
      (middleSemantics_step ht hρ hδ (.appFun a hs)).1 hv
  | @appArg f a a' hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (thirdSemantics Γ ρ δ ε (.app f a)).1 = (thirdSemantics Γ ρ δ ε (.app f a')).1 := by
      rw [thirdSemantics_app hf ha hρ hδ, thirdSemantics_app hf (ha.preservation hs) hρ hδ,
        shapeEval_step ha rfl hρ hs, (middleSemantics_step ha hρ hδ hs).1, (ih ha hρ hδ hε).1]
    refine ⟨hv, ?_⟩
    intro s ht
    exact thirdSemantics_below_compare ht (ht.preservation (.appArg f hs)) ht.app_below_top hρ hρ hδ hδ
      (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.appArg f hs)))
      (middleSemantics_step ht hρ hδ (.appArg f hs)).1 hv
  | @lamTy A A' b hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have hb' := hb.context_conv hA hA' hsA hc
    refine ⟨?_, fun _ _ => rfl⟩
    rw [thirdSemantics_lam hPi hb hρ hδ,
      thirdSemantics_lam (hPi.preservation (.piDom B hs)) hb' hρ hδ,
      ← shapeEval_step h rfl hρ (.lamTy b hs), ← (middleSemantics_step h hρ hδ (.lamTy b hs)).1]
    apply thirdLambda_congr ((hA.goodAt rfl).arity_step hs).symm
    · intro x hx; exact middleShape_step hA rfl hρ hs
    · intro x hx z; exact (middleShape_context_conversion hB hA hA' hsA hc rfl).symm
    · intro x hx y hy
      exact congrFun (congrFun ((middleSemantics_step hA hρ hδ hs).2 sA hA) x) y
    · intro x hx y hy z w
      exact congrFun (congrFun
        ((middleSemantics_context_conversion hB hA hA' hc hρ hδ hx hy).2 sB hB).symm z) w
    · intro x hx y hy z hz
      exact (thirdSemantics_context_conversion hb hA hA' hc hρ hδ hε hx hy hz).1.symm
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    refine ⟨?_, fun _ _ => rfl⟩
    rw [thirdSemantics_lam hPi hb hρ hδ, thirdSemantics_lam hPi (hb.preservation hs) hρ hδ,
      ← shapeEval_step h rfl hρ (.lamBody A hs), ← (middleSemantics_step h hρ hδ (.lamBody A hs)).1]
    apply thirdLambda_congr rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    intro x hx y hy z hz
    exact (ih hb (hρ.up hx) (hδ.up hA rfl hy) (hε.up hA hρ hx hz)).1
  | @piDom A A' B hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have hm := middleSemantics_step ht hρ hδ (.piDom B hs)
    have he : thirdSemantics Γ ρ δ ε (.pi A B) = thirdSemantics Γ ρ δ ε (.pi A' B) := by
      apply thirdSemantics_pi_compare ht (ht.preservation (.piDom B hs)) hρ hρ hδ hδ
        ((hA.goodAt rfl).arity_step hs).symm ((ht.goodAt rfl).arity_step (.piDom B hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piDom B hs))) (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; exact middleShape_step hA rfl hρ hs
      · intro x hx z; exact (middleShape_context_conversion hB hA hA' hsA hc rfl).symm
      · intro x hx y hy
        exact congrFun (congrFun ((middleSemantics_step hA hρ hδ hs).2 sA hA) x) y
      · intro x hx y hy
        exact ((middleSemantics_context_conversion hB hA hA' hc hρ hδ hx hy).2 sB hB).symm
      · intro x hx y hy z hz
        exact congrFun (congrFun (congrFun ((ih hA hρ hδ hε).2 sA hA) x) y) z
      · intro x hx y hy z hz
        exact ((thirdSemantics_context_conversion hB hA hA' hc hρ hδ hε hx hy hz).2 sB hB).symm
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have hm := middleSemantics_step ht hρ hδ (.piCod A hs)
    have he : thirdSemantics Γ ρ δ ε (.pi A B) = thirdSemantics Γ ρ δ ε (.pi A B') := by
      apply thirdSemantics_pi_compare ht (ht.preservation (.piCod A hs)) hρ hρ hδ hδ rfl
        ((ht.goodAt rfl).arity_step (.piCod A hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piCod A hs))) (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; rfl
      · intro x hx z; exact middleShape_step hB rfl (hρ.up hx) hs
      · intro x hx y hy; rfl
      · intro x hx y hy; exact (middleSemantics_step hB (hρ.up hx) (hδ.up hA rfl hy) hs).2 sB hB
      · intro x hx y hy z hz; rfl
      · intro x hx y hy z hz
        exact (ih hB (hρ.up hx) (hδ.up hA rfl hy) (hε.up hA hρ hx hz)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

theorem thirdSemantics_steps_value (h : BoundedTyping 3 Γ t T)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε)
    (hs : Steps t t') : (thirdSemantics Γ ρ δ ε t).1 = (thirdSemantics Γ ρ δ ε t').1 := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact (thirdSemantics_step h hρ hδ hε hs).1.trans (ih (h.preservation hs))

theorem thirdSemantics_steps_candidate (h : BoundedTyping 3 Γ A (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε)
    (hs : Steps A A') : (thirdSemantics Γ ρ δ ε A).2 = (thirdSemantics Γ ρ δ ε A').2 := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact ((thirdSemantics_step h hρ hδ hε hs).2 s h).trans (ih (h.preservation hs))

theorem FiberTypeExpression.thirdSemantics_candidate_red (h : FiberTypeExpression 3 Γ A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε)
    (hr : Red A A') : (thirdSemantics Γ ρ δ ε A).2 = (thirdSemantics Γ ρ δ ε A').2 := by
  rcases h with ⟨s, hA⟩ | ⟨s, he⟩
  · exact thirdSemantics_steps_candidate hA hρ hδ hε hr.steps
  · rw [he, red_srt hr s he]

theorem thirdSemantics_candidate_conv (hA : FiberTypeExpression 3 Γ A) (hB : FiberTypeExpression 3 Γ B)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε)
    (hc : Conv A B) : (thirdSemantics Γ ρ δ ε A).2 = (thirdSemantics Γ ρ δ ε B).2 := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (hA.thirdSemantics_candidate_red hρ hδ hε hC).trans
    (hB.thirdSemantics_candidate_red hρ hδ hε hC').symm

theorem type_thirdSemantics_conv (ht : BoundedTyping 3 Γ t A) (hB : BoundedTyping 3 Γ B (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε)
    (hc : Conv A B) : (thirdSemantics Γ ρ δ ε A).2 = (thirdSemantics Γ ρ δ ε B).2 :=
  thirdSemantics_candidate_conv ht.type_expression (.inl ⟨s, hB⟩) hρ hδ hε hc

end Submission.Helpers
