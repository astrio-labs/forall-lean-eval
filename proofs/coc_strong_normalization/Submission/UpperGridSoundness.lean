import Submission.UpperGridSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
variable {p : Nat} {δ δ' : Nat → UpperGridValue p} {x : ShapeValue} {y : UpperGridValue p}

/-- Upper abstraction evaluates at every compatible argument, also under an
arbitrary admissible environment. -/
theorem upperShapeEval_lam_apply (hb : BoundedTyping (p + 4) (A :: Γ) b B)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hx : x.code = arityAt (.type (p + 2)) A) :
    (shapeEval (p + 4) (p + 2) Γ ρ (.lam A b)).apply x =
      shapeEval (p + 4) (p + 2) (A :: Γ) (push x ρ) b := by
  rw [shapeEval]
  exact ShapeValue.lambda_apply _ _ _ _ hx (shapeEval_code hb rfl (hρ.up hx))

/-- Below the top sort a value, together with its upper arity, determines the
whole carrier family. -/
theorem upperGridSemantics_below_compare
    (h : BoundedTyping (p + 4) Γ t (.srt s)) (h' : BoundedTyping (p + 4) Δ t' (.srt s))
    (hs : sortRank s < p + 4)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ')
    (hk : nextArity (p + 4) (p + 2) Γ ρ t = nextArity (p + 4) (p + 2) Δ ρ' t')
    (hv : (upperGridSemantics p Γ ρ δ t).1 = (upperGridSemantics p Δ ρ' δ' t').1) :
    (upperGridSemantics p Γ ρ δ t).2 = (upperGridSemantics p Δ ρ' δ' t').2 := by
  funext u f
  rw [upperGridSemantics_decode h hs hρ, upperGridSemantics_decode h' hs hρ', hk, hv]

/-- Identity substitutions transport semantics between compatible contexts.
Both environment conditions concern only codes, never normalization. -/
theorem upperGridSemantics_context (h : BoundedTyping (p + 4) Γ t T)
    (hw : BoundedWf (p + 4) Δ) (hσ : BoundedSubCtx (p + 4) Γ Δ Tm.var)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ)
    (hδ : FirstGridContext (p + 1) Γ ρ δ) (hδ' : FirstGridContext (p + 1) Δ ρ δ) :
    (upperGridSemantics p Δ ρ δ t).1 = (upperGridSemantics p Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping (p + 4) Γ t (.srt s) →
      (upperGridSemantics p Δ ρ δ t).2 = (upperGridSemantics p Γ ρ δ t).2) := by
  have he := upperGridSemantics_substitute_related h hw hσ (fun _ => rfl)
    hρ hρ' hδ hδ' (fun _ _ _ => rfl) (by
      intro j C hj
      obtain ⟨D, hD, _⟩ := (hσ j C hj).generation
      exact upperGridSemantics_var hδ' hw hD hρ')
  simpa only [sub_var] using he

theorem upperGridSemantics_context_conversion (hb : BoundedTyping (p + 4) (A :: Γ) b B)
    (hA : BoundedTyping (p + 4) Γ A (.srt sA)) (hA' : BoundedTyping (p + 4) Γ A' (.srt sA'))
    (hc : Conv A A') (hρ : ShapeContext (.type (p + 2)) Γ ρ)
    (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hx : x.code = arityAt (.type (p + 2)) A)
    (hy : y.code = firstGridShape (p + 1) Γ ρ A x) :
    (upperGridSemantics p (A' :: Γ) (push x ρ) (push y δ) b).1 =
        (upperGridSemantics p (A :: Γ) (push x ρ) (push y δ) b).1 ∧
    (∀ s, BoundedTyping (p + 4) (A :: Γ) b (.srt s) →
      (upperGridSemantics p (A' :: Γ) (push x ρ) (push y δ) b).2 =
        (upperGridSemantics p (A :: Γ) (push x ρ) (push y δ) b).2) := by
  have hx' := hx.trans (arityAt_conv (hA.goodAt rfl) (hA'.goodAt rfl) hc)
  have hy' := hy.trans (firstGridShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hρ hc)
  exact upperGridSemantics_context hb (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hA.sort_bound hc)
    (hρ.up hx) (hρ.up hx') (hδ.up hA hy) (hδ.up hA' hy')

/-- The lower value satisfies beta equality without a reducibility premise. -/
theorem upperGridSemantics_beta_value (hPi : BoundedTyping (p + 4) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (p + 4) (A :: Γ) b B) (ha : BoundedTyping (p + 4) Γ a A)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ) :
    (upperGridSemantics p Γ ρ δ (.app (.lam A b) a)).1 =
      (upperGridSemantics p Γ ρ δ (subst 0 a b)).1 := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [upperGridSemantics_app (.lam hPi hb hPi.sort_bound) ha hρ,
    upperGridSemantics_lam hPi hb hρ, upperGridSemantics_subst_value hb ha hA hρ hδ]
  apply firstGridBeta (p + 1) _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ)
    (upperGridSemantics_typed_code ha hρ)
  rw [upperShapeEval_lam_apply hb hρ (shapeEval_typed_code ha rfl hρ)]
  exact upperGridSemantics_typed_code hb (hρ.up (shapeEval_typed_code ha rfl hρ))

/-- Every reduction preserves a typed lower value. If the reduced term is a
formed type, it also preserves its entire carrier family, including at the
top sort. Annotation reductions use context conversion explicitly. -/
theorem upperGridSemantics_step (h : BoundedTyping (p + 4) Γ t T)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hs : Step t t') :
    (upperGridSemantics p Γ ρ δ t).1 = (upperGridSemantics p Γ ρ δ t').1 ∧
    (∀ s, BoundedTyping (p + 4) Γ t (.srt s) →
      (upperGridSemantics p Γ ρ δ t).2 = (upperGridSemantics p Γ ρ δ t').2) := by
  induction hs generalizing Γ T ρ δ with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, _⟩ := h.generation
    obtain ⟨B, s, hPi, hb, _, hc⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping (p + 4) Γ a A :=
      .conv ha hA (conv_symm (conv_pi_inj hc).1) hsA
    have hv := upperGridSemantics_beta_value hPi hb ha' hρ hδ
    refine ⟨hv, ?_⟩
    intro s hs
    exact upperGridSemantics_below_compare hs (hs.preservation (.beta A b a))
      hs.app_below_top hρ hρ
      (congrArg ShapeValue.asArity (shapeEval_step hs rfl hρ (.beta A b a))) hv
  | @appFun f f' a hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (upperGridSemantics p Γ ρ δ (.app f a)).1 =
        (upperGridSemantics p Γ ρ δ (.app f' a)).1 := by
      rw [upperGridSemantics_app hf ha hρ, upperGridSemantics_app (hf.preservation hs) ha hρ,
        shapeEval_step hf rfl hρ hs, (ih hf hρ hδ).1]
    refine ⟨hv, ?_⟩
    intro s hsort
    exact upperGridSemantics_below_compare hsort (hsort.preservation (.appFun a hs))
      hsort.app_below_top hρ hρ
      (congrArg ShapeValue.asArity (shapeEval_step hsort rfl hρ (.appFun a hs))) hv
  | @appArg f a a' hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (upperGridSemantics p Γ ρ δ (.app f a)).1 =
        (upperGridSemantics p Γ ρ δ (.app f a')).1 := by
      rw [upperGridSemantics_app hf ha hρ, upperGridSemantics_app hf (ha.preservation hs) hρ,
        shapeEval_step ha rfl hρ hs, (ih ha hρ hδ).1]
    refine ⟨hv, ?_⟩
    intro s hsort
    exact upperGridSemantics_below_compare hsort (hsort.preservation (.appArg f hs))
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
    rw [upperGridSemantics_lam hPi hb hρ,
      upperGridSemantics_lam (hPi.preservation (.piDom B hs)) hb' hρ,
      ← shapeEval_step h rfl hρ (.lamTy b hs)]
    apply firstGridLambda_congr ((hA.goodAt rfl).arity_step hs).symm
    · intro x hx
      exact firstGridShape_step hA hρ hs
    · intro x hx z
      exact (firstGridShape_context_conversion hB hA hA' hsA hc).symm
    · intro x hx y hy
      exact (upperGridSemantics_context_conversion hb hA hA' hc hρ hδ hx hy).1.symm
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    refine ⟨?_, fun _ _ => rfl⟩
    rw [upperGridSemantics_lam hPi hb hρ,
      upperGridSemantics_lam hPi (hb.preservation hs) hρ,
      ← shapeEval_step h rfl hρ (.lamBody A hs)]
    apply firstGridLambda_congr rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    intro x hx y hy
    exact (ih hb (hρ.up hx) (hδ.up hA hy)).1
  | @piDom A A' B hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping (p + 4) Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have he : upperGridSemantics p Γ ρ δ (.pi A B) = upperGridSemantics p Γ ρ δ (.pi A' B) := by
      apply upperGridSemantics_pi_compare ht (ht.preservation (.piDom B hs)) hρ hρ
        ((hA.goodAt rfl).arity_step hs).symm
        ((ht.goodAt rfl).arity_step (.piDom B hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piDom B hs)))
      · intro x hx
        exact firstGridShape_step hA hρ hs
      · intro x hx z
        exact (firstGridShape_context_conversion hB hA hA' hsA hc).symm
      · intro x hx y hy
        exact congrFun (congrFun ((ih hA hρ hδ).2 sA hA) x) y
      · intro x hx y hy
        exact ((upperGridSemantics_context_conversion hB hA hA' hc hρ hδ hx hy).2 sB hB).symm
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping (p + 4) Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have he : upperGridSemantics p Γ ρ δ (.pi A B) = upperGridSemantics p Γ ρ δ (.pi A B') := by
      apply upperGridSemantics_pi_compare ht (ht.preservation (.piCod A hs)) hρ hρ rfl
        ((ht.goodAt rfl).arity_step (.piCod A hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piCod A hs)))
      · intro x hx
        rfl
      · intro x hx z
        exact firstGridShape_step hB (hρ.up hx) hs
      · intro x hx y hy
        rfl
      · intro x hx y hy
        exact (ih hB (hρ.up hx) (hδ.up hA hy)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

theorem upperGridSemantics_steps_value (h : BoundedTyping (p + 4) Γ t T)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hs : Steps t t') :
    (upperGridSemantics p Γ ρ δ t).1 = (upperGridSemantics p Γ ρ δ t').1 := by
  induction hs with
  | refl => rfl
  | head hs hr ih =>
    exact (upperGridSemantics_step h hρ hδ hs).1.trans (ih (h.preservation hs))

theorem upperGridSemantics_steps_carrier (h : BoundedTyping (p + 4) Γ A (.srt s))
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hs : Steps A A') :
    (upperGridSemantics p Γ ρ δ A).2 = (upperGridSemantics p Γ ρ δ A').2 := by
  induction hs with
  | refl => rfl
  | head hs hr ih =>
    exact ((upperGridSemantics_step h hρ hδ hs).2 s h).trans (ih (h.preservation hs))

theorem ShapeTypedOrSort.upperGridSemantics_value_red (h : ShapeTypedOrSort (p + 4) Γ t)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hr : Red t t') :
    (upperGridSemantics p Γ ρ δ t).1 = (upperGridSemantics p Γ ρ δ t').1 := by
  rcases h with ⟨T, ht⟩ | ⟨s, he⟩
  · exact upperGridSemantics_steps_value ht hρ hδ hr.steps
  · rw [he, red_srt hr s he]

theorem FiberTypeExpression.upperGridSemantics_carrier_red (h : FiberTypeExpression (p + 4) Γ A)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hr : Red A A') :
    (upperGridSemantics p Γ ρ δ A).2 = (upperGridSemantics p Γ ρ δ A').2 := by
  rcases h with ⟨s, hA⟩ | ⟨s, he⟩
  · exact upperGridSemantics_steps_carrier hA hρ hδ hr.steps
  · rw [he, red_srt hr s he]

/-- Typed lower values are invariant under conversion. Untypable sorts may
occur as type expressions, and reduce only to themselves. -/
theorem upperGridSemantics_value_conv (ht : ShapeTypedOrSort (p + 4) Γ t)
    (ht' : ShapeTypedOrSort (p + 4) Γ t')
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hc : Conv t t') :
    (upperGridSemantics p Γ ρ δ t).1 = (upperGridSemantics p Γ ρ δ t').1 := by
  obtain ⟨u, hu, hu'⟩ := conv_join hc
  exact (ht.upperGridSemantics_value_red hρ hδ hu).trans
    (ht'.upperGridSemantics_value_red hρ hδ hu').symm

/-- Carrier conversion invariance for every formed type at every bound `p + 4`,
including the top sort; no normalization assumption is used. -/
theorem upperGridSemantics_carrier_conv (hA : FiberTypeExpression (p + 4) Γ A)
    (hB : FiberTypeExpression (p + 4) Γ B)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hc : Conv A B) :
    (upperGridSemantics p Γ ρ δ A).2 = (upperGridSemantics p Γ ρ δ B).2 := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (hA.upperGridSemantics_carrier_red hρ hδ hC).trans
    (hB.upperGridSemantics_carrier_red hρ hδ hC').symm

theorem type_upperGridSemantics_conv (ht : BoundedTyping (p + 4) Γ t A)
    (hB : BoundedTyping (p + 4) Γ B (.srt s))
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hc : Conv A B) :
    (upperGridSemantics p Γ ρ δ A).2 = (upperGridSemantics p Γ ρ δ B).2 :=
  upperGridSemantics_carrier_conv ht.type_expression (.inl ⟨s, hB⟩) hρ hδ hc

end Submission.Helpers
