import Submission.FiberApplication

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Upper abstraction evaluates at every compatible argument, also under an
arbitrary admissible environment. -/
theorem shapeEval_lam_apply (hb : BoundedTyping 2 (A :: Γ) b B)
    (hρ : ShapeContext (.type 0) Γ ρ) (hx : x.code = arityAt (.type 0) A) :
    (shapeEval 2 0 Γ ρ (.lam A b)).apply x =
      shapeEval 2 0 (A :: Γ) (push x ρ) b := by
  rw [shapeEval]
  exact ShapeValue.lambda_apply _ _ _ _ hx (shapeEval_code hb rfl (hρ.up hx))

/-- Below the top sort a value, together with its upper arity, determines the
whole candidate family. -/
theorem fiberSemantics_below_compare
    (h : BoundedTyping 2 Γ t (.srt s)) (h' : BoundedTyping 2 Δ t' (.srt s))
    (hs : sortRank s < 2)
    (hρ : ShapeContext (.type 0) Γ ρ) (hρ' : ShapeContext (.type 0) Δ ρ')
    (hk : nextArity 2 0 Γ ρ t = nextArity 2 0 Δ ρ' t')
    (hv : (fiberSemantics Γ ρ δ t).1 = (fiberSemantics Δ ρ' δ' t').1) :
    (fiberSemantics Γ ρ δ t).2 = (fiberSemantics Δ ρ' δ' t').2 := by
  funext u f
  rw [fiberSemantics_decode h hs hρ, fiberSemantics_decode h' hs hρ', hk, hv]

/-- Identity substitutions transport semantics between compatible contexts.
Both environment conditions concern only codes, never normalization. -/
theorem fiberSemantics_context (h : BoundedTyping 2 Γ t T)
    (hw : BoundedWf 2 Δ) (hσ : BoundedSubCtx 2 Γ Δ Tm.var)
    (hρ : ShapeContext (.type 0) Γ ρ) (hρ' : ShapeContext (.type 0) Δ ρ)
    (hδ : FiberContext 2 0 Γ ρ δ) (hδ' : FiberContext 2 0 Δ ρ δ) :
    (fiberSemantics Δ ρ δ t).1 = (fiberSemantics Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping 2 Γ t (.srt s) →
      (fiberSemantics Δ ρ δ t).2 = (fiberSemantics Γ ρ δ t).2) := by
  have he := fiberSemantics_substitute_related h hw hσ (fun _ => rfl)
    hρ hρ' hδ hδ' (fun _ _ _ => rfl) (by
      intro j C hj
      obtain ⟨D, hD, _⟩ := (hσ j C hj).generation
      exact fiberSemantics_var hδ' hw hD hρ')
  simpa only [sub_var] using he

theorem fiberSemantics_context_conversion (hb : BoundedTyping 2 (A :: Γ) b B)
    (hA : BoundedTyping 2 Γ A (.srt sA)) (hA' : BoundedTyping 2 Γ A' (.srt sA'))
    (hc : Conv A A') (hρ : ShapeContext (.type 0) Γ ρ)
    (hδ : FiberContext 2 0 Γ ρ δ)
    (hx : x.code = arityAt (.type 0) A)
    (hy : y.code = fiberShape 2 0 Γ ρ A x) :
    (fiberSemantics (A' :: Γ) (push x ρ) (push y δ) b).1 =
        (fiberSemantics (A :: Γ) (push x ρ) (push y δ) b).1 ∧
    (∀ s, BoundedTyping 2 (A :: Γ) b (.srt s) →
      (fiberSemantics (A' :: Γ) (push x ρ) (push y δ) b).2 =
        (fiberSemantics (A :: Γ) (push x ρ) (push y δ) b).2) := by
  have hx' := hx.trans (arityAt_conv (hA.goodAt rfl) (hA'.goodAt rfl) hc)
  have hy' := hy.trans (fiberShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) rfl hρ hc)
  exact fiberSemantics_context hb (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hA.sort_bound hc)
    (hρ.up hx) (hρ.up hx') (hδ.up hA rfl hy) (hδ.up hA' rfl hy')

/-- The lower value satisfies beta equality without a reducibility premise. -/
theorem fiberSemantics_beta_value (hPi : BoundedTyping 2 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 2 (A :: Γ) b B) (ha : BoundedTyping 2 Γ a A)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ) :
    (fiberSemantics Γ ρ δ (.app (.lam A b) a)).1 =
      (fiberSemantics Γ ρ δ (subst 0 a b)).1 := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [fiberSemantics_app (.lam hPi hb hPi.sort_bound) ha hρ,
    fiberSemantics_lam hPi hb hρ, fiberSemantics_subst_value hb ha hA hρ hδ]
  apply fiberBeta _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ)
    (fiberSemantics_typed_code ha hρ)
  rw [shapeEval_lam_apply hb hρ (shapeEval_typed_code ha rfl hρ)]
  exact fiberSemantics_typed_code hb (hρ.up (shapeEval_typed_code ha rfl hρ))

/-- Every reduction preserves a typed lower value. If the reduced term is a
formed type, it also preserves its entire candidate family, including at the
top sort. Annotation reductions use context conversion explicitly. -/
theorem fiberSemantics_step (h : BoundedTyping 2 Γ t T)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hs : Step t t') :
    (fiberSemantics Γ ρ δ t).1 = (fiberSemantics Γ ρ δ t').1 ∧
    (∀ s, BoundedTyping 2 Γ t (.srt s) →
      (fiberSemantics Γ ρ δ t).2 = (fiberSemantics Γ ρ δ t').2) := by
  induction hs generalizing Γ T ρ δ with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, _⟩ := h.generation
    obtain ⟨B, s, hPi, hb, _, hc⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping 2 Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hc).1) hsA
    have hv := fiberSemantics_beta_value hPi hb ha' hρ hδ
    refine ⟨hv, ?_⟩
    intro s hs
    exact fiberSemantics_below_compare hs (hs.preservation (.beta A b a))
      hs.app_below_top hρ hρ
      (congrArg ShapeValue.asArity (shapeEval_step hs rfl hρ (.beta A b a))) hv
  | @appFun f f' a hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (fiberSemantics Γ ρ δ (.app f a)).1 =
        (fiberSemantics Γ ρ δ (.app f' a)).1 := by
      rw [fiberSemantics_app hf ha hρ, fiberSemantics_app (hf.preservation hs) ha hρ,
        shapeEval_step hf rfl hρ hs, (ih hf hρ hδ).1]
    refine ⟨hv, ?_⟩
    intro s hsort
    exact fiberSemantics_below_compare hsort (hsort.preservation (.appFun a hs))
      hsort.app_below_top hρ hρ
      (congrArg ShapeValue.asArity (shapeEval_step hsort rfl hρ (.appFun a hs))) hv
  | @appArg f a a' hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (fiberSemantics Γ ρ δ (.app f a)).1 =
        (fiberSemantics Γ ρ δ (.app f a')).1 := by
      rw [fiberSemantics_app hf ha hρ, fiberSemantics_app hf (ha.preservation hs) hρ,
        shapeEval_step ha rfl hρ hs, (ih ha hρ hδ).1]
    refine ⟨hv, ?_⟩
    intro s hsort
    exact fiberSemantics_below_compare hsort (hsort.preservation (.appArg f hs))
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
    rw [fiberSemantics_lam hPi hb hρ,
      fiberSemantics_lam (hPi.preservation (.piDom B hs)) hb' hρ,
      ← shapeEval_step h rfl hρ (.lamTy b hs)]
    apply fiberLambda_congr ((hA.goodAt rfl).arity_step hs).symm
    · intro x hx
      exact fiberShape_step hA rfl hρ hs
    · intro x hx z
      exact (fiberShape_context_conversion hB hA hA' hsA hc rfl).symm
    · intro x hx y hy
      exact (fiberSemantics_context_conversion hb hA hA' hc hρ hδ hx hy).1.symm
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    refine ⟨?_, fun _ _ => rfl⟩
    rw [fiberSemantics_lam hPi hb hρ,
      fiberSemantics_lam hPi (hb.preservation hs) hρ,
      ← shapeEval_step h rfl hρ (.lamBody A hs)]
    apply fiberLambda_congr rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    intro x hx y hy
    exact (ih hb (hρ.up hx) (hδ.up hA rfl hy)).1
  | @piDom A A' B hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping 2 Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have he : fiberSemantics Γ ρ δ (.pi A B) = fiberSemantics Γ ρ δ (.pi A' B) := by
      apply fiberSemantics_pi_compare ht (ht.preservation (.piDom B hs)) hρ hρ
        ((hA.goodAt rfl).arity_step hs).symm
        ((ht.goodAt rfl).arity_step (.piDom B hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piDom B hs)))
      · intro x hx
        exact fiberShape_step hA rfl hρ hs
      · intro x hx z
        exact (fiberShape_context_conversion hB hA hA' hsA hc rfl).symm
      · intro x hx y hy
        exact congrFun (congrFun ((ih hA hρ hδ).2 sA hA) x) y
      · intro x hx y hy
        exact ((fiberSemantics_context_conversion hB hA hA' hc hρ hδ hx hy).2 sB hB).symm
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping 2 Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have he : fiberSemantics Γ ρ δ (.pi A B) = fiberSemantics Γ ρ δ (.pi A B') := by
      apply fiberSemantics_pi_compare ht (ht.preservation (.piCod A hs)) hρ hρ rfl
        ((ht.goodAt rfl).arity_step (.piCod A hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piCod A hs)))
      · intro x hx
        rfl
      · intro x hx z
        exact fiberShape_step hB rfl (hρ.up hx) hs
      · intro x hx y hy
        rfl
      · intro x hx y hy
        exact (ih hB (hρ.up hx) (hδ.up hA rfl hy)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

theorem fiberSemantics_steps_value (h : BoundedTyping 2 Γ t T)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hs : Steps t t') :
    (fiberSemantics Γ ρ δ t).1 = (fiberSemantics Γ ρ δ t').1 := by
  induction hs with
  | refl => rfl
  | head hs hr ih =>
    exact (fiberSemantics_step h hρ hδ hs).1.trans (ih (h.preservation hs))

theorem fiberSemantics_steps_candidate (h : BoundedTyping 2 Γ A (.srt s))
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hs : Steps A A') :
    (fiberSemantics Γ ρ δ A).2 = (fiberSemantics Γ ρ δ A').2 := by
  induction hs with
  | refl => rfl
  | head hs hr ih =>
    exact ((fiberSemantics_step h hρ hδ hs).2 s h).trans (ih (h.preservation hs))

theorem ShapeTypedOrSort.fiberSemantics_value_red (h : ShapeTypedOrSort 2 Γ t)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hr : Red t t') :
    (fiberSemantics Γ ρ δ t).1 = (fiberSemantics Γ ρ δ t').1 := by
  rcases h with ⟨T, ht⟩ | ⟨s, he⟩
  · exact fiberSemantics_steps_value ht hρ hδ hr.steps
  · rw [he, red_srt hr s he]

theorem FiberTypeExpression.fiberSemantics_candidate_red (h : FiberTypeExpression 2 Γ A)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hr : Red A A') :
    (fiberSemantics Γ ρ δ A).2 = (fiberSemantics Γ ρ δ A').2 := by
  rcases h with ⟨s, hA⟩ | ⟨s, he⟩
  · exact fiberSemantics_steps_candidate hA hρ hδ hr.steps
  · rw [he, red_srt hr s he]

/-- Typed lower values are invariant under conversion. Untypable sorts may
occur as type expressions, and reduce only to themselves. -/
theorem fiberSemantics_value_conv (ht : ShapeTypedOrSort 2 Γ t)
    (ht' : ShapeTypedOrSort 2 Γ t')
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hc : Conv t t') :
    (fiberSemantics Γ ρ δ t).1 = (fiberSemantics Γ ρ δ t').1 := by
  obtain ⟨u, hu, hu'⟩ := conv_join hc
  exact (ht.fiberSemantics_value_red hρ hδ hu).trans
    (ht'.fiberSemantics_value_red hρ hδ hu').symm

/-- Candidate conversion invariance for every formed type at bound two,
including `Type 1`; no normalization assumption is used. -/
theorem fiberSemantics_candidate_conv (hA : FiberTypeExpression 2 Γ A)
    (hB : FiberTypeExpression 2 Γ B)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hc : Conv A B) :
    (fiberSemantics Γ ρ δ A).2 = (fiberSemantics Γ ρ δ B).2 := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (hA.fiberSemantics_candidate_red hρ hδ hC).trans
    (hB.fiberSemantics_candidate_red hρ hδ hC').symm

theorem type_fiberSemantics_conv (ht : BoundedTyping 2 Γ t A)
    (hB : BoundedTyping 2 Γ B (.srt s))
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hc : Conv A B) :
    (fiberSemantics Γ ρ δ A).2 = (fiberSemantics Γ ρ δ B).2 :=
  fiberSemantics_candidate_conv ht.type_expression (.inl ⟨s, hB⟩) hρ hδ hc

end Submission.Helpers
