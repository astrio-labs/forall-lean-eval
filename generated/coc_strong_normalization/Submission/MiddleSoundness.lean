import Submission.MiddleSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Upper abstraction evaluates at every compatible argument, also under an
arbitrary admissible environment. -/
theorem middleShapeEval_lam_apply (hb : BoundedTyping 3 (A :: Γ) b B)
    (hρ : ShapeContext (.type 1) Γ ρ) (hx : x.code = arityAt (.type 1) A) :
    (shapeEval 3 1 Γ ρ (.lam A b)).apply x =
      shapeEval 3 1 (A :: Γ) (push x ρ) b := by
  rw [shapeEval]
  exact ShapeValue.lambda_apply _ _ _ _ hx (shapeEval_code hb rfl (hρ.up hx))

/-- Below the top sort a value, together with its upper arity, determines the
whole carrier family. -/
theorem middleSemantics_below_compare
    (h : BoundedTyping 3 Γ t (.srt s)) (h' : BoundedTyping 3 Δ t' (.srt s))
    (hs : sortRank s < 3)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hk : nextArity 3 1 Γ ρ t = nextArity 3 1 Δ ρ' t')
    (hv : (middleSemantics Γ ρ δ t).1 = (middleSemantics Δ ρ' δ' t').1) :
    (middleSemantics Γ ρ δ t).2 = (middleSemantics Δ ρ' δ' t').2 := by
  funext u f
  rw [middleSemantics_decode h hs hρ, middleSemantics_decode h' hs hρ', hk, hv]

/-- Identity substitutions transport semantics between compatible contexts.
Both environment conditions concern only codes, never normalization. -/
theorem middleSemantics_context (h : BoundedTyping 3 Γ t T)
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ Tm.var)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ)
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ δ) :
    (middleSemantics Δ ρ δ t).1 = (middleSemantics Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (middleSemantics Δ ρ δ t).2 = (middleSemantics Γ ρ δ t).2) := by
  have he := middleSemantics_substitute_related h hw hσ (fun _ => rfl)
    hρ hρ' hδ hδ' (fun _ _ _ => rfl) (by
      intro j C hj
      obtain ⟨D, hD, _⟩ := (hσ j C hj).generation
      exact middleSemantics_var hδ' hw hD hρ')
  simpa only [sub_var] using he

theorem middleSemantics_context_conversion (hb : BoundedTyping 3 (A :: Γ) b B)
    (hA : BoundedTyping 3 Γ A (.srt sA)) (hA' : BoundedTyping 3 Γ A' (.srt sA'))
    (hc : Conv A A') (hρ : ShapeContext (.type 1) Γ ρ)
    (hδ : MiddleContext 3 1 Γ ρ δ)
    (hx : x.code = arityAt (.type 1) A)
    (hy : y.code = middleShape 3 1 Γ ρ A x) :
    (middleSemantics (A' :: Γ) (push x ρ) (push y δ) b).1 =
        (middleSemantics (A :: Γ) (push x ρ) (push y δ) b).1 ∧
    (∀ s, BoundedTyping 3 (A :: Γ) b (.srt s) →
      (middleSemantics (A' :: Γ) (push x ρ) (push y δ) b).2 =
        (middleSemantics (A :: Γ) (push x ρ) (push y δ) b).2) := by
  have hx' := hx.trans (arityAt_conv (hA.goodAt rfl) (hA'.goodAt rfl) hc)
  have hy' := hy.trans (middleShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) rfl hρ hc)
  exact middleSemantics_context hb (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hA.sort_bound hc)
    (hρ.up hx) (hρ.up hx') (hδ.up hA rfl hy) (hδ.up hA' rfl hy')

/-- The lower value satisfies beta equality without a reducibility premise. -/
theorem middleSemantics_beta_value (hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 3 (A :: Γ) b B) (ha : BoundedTyping 3 Γ a A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (middleSemantics Γ ρ δ (.app (.lam A b) a)).1 =
      (middleSemantics Γ ρ δ (subst 0 a b)).1 := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [middleSemantics_app (.lam hPi hb hPi.sort_bound) ha hρ,
    middleSemantics_lam hPi hb hρ, middleSemantics_subst_value hb ha hA hρ hδ]
  apply middleBeta _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ)
    (middleSemantics_typed_code ha hρ)
  rw [middleShapeEval_lam_apply hb hρ (shapeEval_typed_code ha rfl hρ)]
  exact middleSemantics_typed_code hb (hρ.up (shapeEval_typed_code ha rfl hρ))

/-- Every reduction preserves a typed lower value. If the reduced term is a
formed type, it also preserves its entire carrier family, including at the
top sort. Annotation reductions use context conversion explicitly. -/
theorem middleSemantics_step (h : BoundedTyping 3 Γ t T)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hs : Step t t') :
    (middleSemantics Γ ρ δ t).1 = (middleSemantics Γ ρ δ t').1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (middleSemantics Γ ρ δ t).2 = (middleSemantics Γ ρ δ t').2) := by
  induction hs generalizing Γ T ρ δ with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, _⟩ := h.generation
    obtain ⟨B, s, hPi, hb, _, hc⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping 3 Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hc).1) hsA
    have hv := middleSemantics_beta_value hPi hb ha' hρ hδ
    refine ⟨hv, ?_⟩
    intro s hs
    exact middleSemantics_below_compare hs (hs.preservation (.beta A b a))
      hs.app_below_top hρ hρ
      (congrArg ShapeValue.asArity (shapeEval_step hs rfl hρ (.beta A b a))) hv
  | @appFun f f' a hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (middleSemantics Γ ρ δ (.app f a)).1 =
        (middleSemantics Γ ρ δ (.app f' a)).1 := by
      rw [middleSemantics_app hf ha hρ, middleSemantics_app (hf.preservation hs) ha hρ,
        shapeEval_step hf rfl hρ hs, (ih hf hρ hδ).1]
    refine ⟨hv, ?_⟩
    intro s hsort
    exact middleSemantics_below_compare hsort (hsort.preservation (.appFun a hs))
      hsort.app_below_top hρ hρ
      (congrArg ShapeValue.asArity (shapeEval_step hsort rfl hρ (.appFun a hs))) hv
  | @appArg f a a' hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (middleSemantics Γ ρ δ (.app f a)).1 =
        (middleSemantics Γ ρ δ (.app f a')).1 := by
      rw [middleSemantics_app hf ha hρ, middleSemantics_app hf (ha.preservation hs) hρ,
        shapeEval_step ha rfl hρ hs, (ih ha hρ hδ).1]
    refine ⟨hv, ?_⟩
    intro s hsort
    exact middleSemantics_below_compare hsort (hsort.preservation (.appArg f hs))
      hsort.app_below_top hρ hρ
      (congrArg ShapeValue.asArity (shapeEval_step hsort rfl hρ (.appArg f hs))) hv
  | @lamTy A A' b hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have hb' := hb.context_conv hA hA' hsA hc
    refine ⟨?_, fun _ _ => rfl⟩
    rw [middleSemantics_lam hPi hb hρ,
      middleSemantics_lam (hPi.preservation (.piDom B hs)) hb' hρ,
      ← shapeEval_step h rfl hρ (.lamTy b hs)]
    apply middleLambda_congr ((hA.goodAt rfl).arity_step hs).symm
    · intro x hx
      exact middleShape_step hA rfl hρ hs
    · intro x hx z
      exact (middleShape_context_conversion hB hA hA' hsA hc rfl).symm
    · intro x hx y hy
      exact (middleSemantics_context_conversion hb hA hA' hc hρ hδ hx hy).1.symm
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    refine ⟨?_, fun _ _ => rfl⟩
    rw [middleSemantics_lam hPi hb hρ,
      middleSemantics_lam hPi (hb.preservation hs) hρ,
      ← shapeEval_step h rfl hρ (.lamBody A hs)]
    apply middleLambda_congr rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    intro x hx y hy
    exact (ih hb (hρ.up hx) (hδ.up hA rfl hy)).1
  | @piDom A A' B hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have he : middleSemantics Γ ρ δ (.pi A B) = middleSemantics Γ ρ δ (.pi A' B) := by
      apply middleSemantics_pi_compare ht (ht.preservation (.piDom B hs)) hρ hρ
        ((hA.goodAt rfl).arity_step hs).symm
        ((ht.goodAt rfl).arity_step (.piDom B hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piDom B hs)))
      · intro x hx
        exact middleShape_step hA rfl hρ hs
      · intro x hx z
        exact (middleShape_context_conversion hB hA hA' hsA hc rfl).symm
      · intro x hx y hy
        exact congrFun (congrFun ((ih hA hρ hδ).2 sA hA) x) y
      · intro x hx y hy
        exact ((middleSemantics_context_conversion hB hA hA' hc hρ hδ hx hy).2 sB hB).symm
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have he : middleSemantics Γ ρ δ (.pi A B) = middleSemantics Γ ρ δ (.pi A B') := by
      apply middleSemantics_pi_compare ht (ht.preservation (.piCod A hs)) hρ hρ rfl
        ((ht.goodAt rfl).arity_step (.piCod A hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piCod A hs)))
      · intro x hx
        rfl
      · intro x hx z
        exact middleShape_step hB rfl (hρ.up hx) hs
      · intro x hx y hy
        rfl
      · intro x hx y hy
        exact (ih hB (hρ.up hx) (hδ.up hA rfl hy)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

theorem middleSemantics_steps_value (h : BoundedTyping 3 Γ t T)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hs : Steps t t') :
    (middleSemantics Γ ρ δ t).1 = (middleSemantics Γ ρ δ t').1 := by
  induction hs with
  | refl => rfl
  | head hs hr ih =>
    exact (middleSemantics_step h hρ hδ hs).1.trans (ih (h.preservation hs))

theorem middleSemantics_steps_carrier (h : BoundedTyping 3 Γ A (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hs : Steps A A') :
    (middleSemantics Γ ρ δ A).2 = (middleSemantics Γ ρ δ A').2 := by
  induction hs with
  | refl => rfl
  | head hs hr ih =>
    exact ((middleSemantics_step h hρ hδ hs).2 s h).trans (ih (h.preservation hs))

theorem ShapeTypedOrSort.middleSemantics_value_red (h : ShapeTypedOrSort 3 Γ t)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hr : Red t t') :
    (middleSemantics Γ ρ δ t).1 = (middleSemantics Γ ρ δ t').1 := by
  rcases h with ⟨T, ht⟩ | ⟨s, he⟩
  · exact middleSemantics_steps_value ht hρ hδ hr.steps
  · rw [he, red_srt hr s he]

theorem FiberTypeExpression.middleSemantics_carrier_red (h : FiberTypeExpression 3 Γ A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hr : Red A A') :
    (middleSemantics Γ ρ δ A).2 = (middleSemantics Γ ρ δ A').2 := by
  rcases h with ⟨s, hA⟩ | ⟨s, he⟩
  · exact middleSemantics_steps_carrier hA hρ hδ hr.steps
  · rw [he, red_srt hr s he]

/-- Typed lower values are invariant under conversion. Untypable sorts may
occur as type expressions, and reduce only to themselves. -/
theorem middleSemantics_value_conv (ht : ShapeTypedOrSort 3 Γ t)
    (ht' : ShapeTypedOrSort 3 Γ t')
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hc : Conv t t') :
    (middleSemantics Γ ρ δ t).1 = (middleSemantics Γ ρ δ t').1 := by
  obtain ⟨u, hu, hu'⟩ := conv_join hc
  exact (ht.middleSemantics_value_red hρ hδ hu).trans
    (ht'.middleSemantics_value_red hρ hδ hu').symm

/-- Carrier conversion invariance for every formed type at bound three,
including `Type 2`; no normalization assumption is used. -/
theorem middleSemantics_carrier_conv (hA : FiberTypeExpression 3 Γ A)
    (hB : FiberTypeExpression 3 Γ B)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hc : Conv A B) :
    (middleSemantics Γ ρ δ A).2 = (middleSemantics Γ ρ δ B).2 := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (hA.middleSemantics_carrier_red hρ hδ hC).trans
    (hB.middleSemantics_carrier_red hρ hδ hC').symm

theorem type_middleSemantics_conv (ht : BoundedTyping 3 Γ t A)
    (hB : BoundedTyping 3 Γ B (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (hc : Conv A B) :
    (middleSemantics Γ ρ δ A).2 = (middleSemantics Γ ρ δ B).2 :=
  middleSemantics_carrier_conv ht.type_expression (.inl ⟨s, hB⟩) hρ hδ hc

end Submission.Helpers
