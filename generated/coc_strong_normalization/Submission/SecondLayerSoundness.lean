import Submission.SecondLayerSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 2000000
variable {p : Nat} {δ δ' : Nat → UpperGridValue (p + 1)} {ε ε' : Nat → SecondLayerValue p}
  {x : ShapeValue} {y : UpperGridValue (p + 1)} {z : SecondLayerValue p}

theorem upperGridSemantics_lam_apply (hPi : BoundedTyping (p + 5) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (p + 5) (A :: Γ) b B) (hρ : ShapeContext (.type (p + 3)) Γ ρ)
    (hx : x.code = arityAt (.type (p + 3)) A) (hy : y.code = firstGridShape (p + 2) Γ ρ A x) :
    firstGridApply (p + 2) (arityAt (.type (p + 3)) A) (fun x => firstGridShape (p + 2) Γ ρ A x)
      (fun x z => firstGridShape (p + 2) (A :: Γ) (push x ρ) B z)
      (shapeEval (p + 5) (p + 3) Γ ρ (.lam A b)) (upperGridSemantics (p + 1) Γ ρ δ (.lam A b)).1 x y =
        (upperGridSemantics (p + 1) (A :: Γ) (push x ρ) (push y δ) b).1 := by
  erw [upperGridSemantics_lam hPi hb hρ]
  apply firstGridBeta (p + 2) _ _ _ _ _ _ _ hx hy
  erw [upperShapeEval_lam_apply hb hρ hx]
  exact upperGridSemantics_typed_code hb (hρ.up hx)

theorem secondLayerSemantics_below_compare
    (h : BoundedTyping (p + 5) Γ t (.srt s)) (h' : BoundedTyping (p + 5) Δ t' (.srt s)) (hs : sortRank s < p + 5)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hρ' : ShapeContext (.type (p + 3)) Δ ρ')
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hδ' : FirstGridContext (p + 2) Δ ρ' δ')
    (hk : nextArity (p + 5) (p + 3) Γ ρ t = nextArity (p + 5) (p + 3) Δ ρ' t')
    (hm : (upperGridSemantics (p + 1) Γ ρ δ t).1 = (upperGridSemantics (p + 1) Δ ρ' δ' t').1)
    (hv : (secondLayerSemantics p Γ ρ δ ε t).1 = (secondLayerSemantics p Δ ρ' δ' ε' t').1) :
    (secondLayerSemantics p Γ ρ δ ε t).2 = (secondLayerSemantics p Δ ρ' δ' ε' t').2 := by
  funext u f g
  erw [secondLayerSemantics_decode h hs hρ hδ, secondLayerSemantics_decode h' hs hρ' hδ', hk, hm, hv]

theorem secondLayerSemantics_context (h : BoundedTyping (p + 5) Γ t T)
    (hw : BoundedWf (p + 5) Δ) (hσ : BoundedSubCtx (p + 5) Γ Δ Tm.var)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hρ' : ShapeContext (.type (p + 3)) Δ ρ)
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hδ' : FirstGridContext (p + 2) Δ ρ δ)
    (hε : SecondGridContext (p + 1) Γ ρ δ ε) (hε' : SecondGridContext (p + 1) Δ ρ δ ε) :
    (secondLayerSemantics p Δ ρ δ ε t).1 = (secondLayerSemantics p Γ ρ δ ε t).1 ∧
    (∀ s, BoundedTyping (p + 5) Γ t (.srt s) →
      (secondLayerSemantics p Δ ρ δ ε t).2 = (secondLayerSemantics p Γ ρ δ ε t).2) := by
  have he := secondLayerSemantics_substitute_related h hw hσ (fun _ => rfl)
    hρ hρ' hδ hδ' hε hε' (fun _ _ _ => rfl) (by
      intro j C hj
      obtain ⟨D, hD, _⟩ := (hσ j C hj).generation
      exact upperGridSemantics_var hδ' hw hD hρ') (by
      intro j C hj
      obtain ⟨D, hD, _⟩ := (hσ j C hj).generation
      exact secondLayerSemantics_var hε' hw hD hρ' hδ')
  simpa only [sub_var] using he

theorem secondLayerSemantics_context_conversion (hb : BoundedTyping (p + 5) (A :: Γ) b B)
    (hA : BoundedTyping (p + 5) Γ A (.srt sA)) (hA' : BoundedTyping (p + 5) Γ A' (.srt sA'))
    (hc : Conv A A') (hρ : ShapeContext (.type (p + 3)) Γ ρ)
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hx : x.code = arityAt (.type (p + 3)) A) (hy : y.code = firstGridShape (p + 2) Γ ρ A x)
    (hz : z.code = secondGridShape (p + 1) Γ ρ δ A x y) :
    (secondLayerSemantics p (A' :: Γ) (push x ρ) (push y δ) (push z ε) b).1 =
        (secondLayerSemantics p (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1 ∧
    (∀ s, BoundedTyping (p + 5) (A :: Γ) b (.srt s) →
      (secondLayerSemantics p (A' :: Γ) (push x ρ) (push y δ) (push z ε) b).2 =
        (secondLayerSemantics p (A :: Γ) (push x ρ) (push y δ) (push z ε) b).2) := by
  have hx' := hx.trans (arityAt_conv (hA.goodAt rfl) (hA'.goodAt rfl) hc)
  have hy' := hy.trans (firstGridShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hρ hc)
  have hz' := hz.trans (congrFun (congrFun
    (secondGridShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hρ hδ hc) x) y)
  exact secondLayerSemantics_context hb (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hA.sort_bound hc)
    (hρ.up hx) (hρ.up hx') (hδ.up hA hy) (hδ.up hA' hy')
    (hε.up hA hρ hx hz) (hε.up hA' hρ hx' hz')

theorem secondLayerSemantics_beta_value (hPi : BoundedTyping (p + 5) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (p + 5) (A :: Γ) b B) (ha : BoundedTyping (p + 5) Γ a A)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε) :
    (secondLayerSemantics p Γ ρ δ ε (.app (.lam A b) a)).1 =
      (secondLayerSemantics p Γ ρ δ ε (subst 0 a b)).1 := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  erw [secondLayerSemantics_app (.lam hPi hb hPi.sort_bound) ha hρ hδ,
    secondLayerSemantics_lam hPi hb hρ hδ, secondLayerSemantics_subst_value hb ha hA hρ hδ hε]
  apply secondGridBeta (p + 1) _ _ _ _ _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ)
    (upperGridSemantics_typed_code ha hρ) (secondLayerSemantics_typed_code ha hρ hδ)
  erw [upperShapeEval_lam_apply hb hρ (shapeEval_typed_code ha rfl hρ),
    upperGridSemantics_lam_apply hPi hb hρ (shapeEval_typed_code ha rfl hρ) (upperGridSemantics_typed_code ha hρ)]
  exact secondLayerSemantics_typed_code hb (hρ.up (shapeEval_typed_code ha rfl hρ))
    (hδ.up hA (upperGridSemantics_typed_code ha hρ))

theorem secondLayerSemantics_step (h : BoundedTyping (p + 5) Γ t T)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hs : Step t t') :
    (secondLayerSemantics p Γ ρ δ ε t).1 = (secondLayerSemantics p Γ ρ δ ε t').1 ∧
    (∀ s, BoundedTyping (p + 5) Γ t (.srt s) →
      (secondLayerSemantics p Γ ρ δ ε t).2 = (secondLayerSemantics p Γ ρ δ ε t').2) := by
  induction hs generalizing Γ T ρ δ ε with
  | beta A b a =>
    obtain ⟨D, E, hf, ha, _⟩ := h.generation
    obtain ⟨B, s, hPi, hb, _, hc⟩ := hf.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    have ha' : BoundedTyping (p + 5) Γ a A := .conv ha hA (conv_symm (conv_pi_inj hc).1) hsA
    have hv := secondLayerSemantics_beta_value hPi hb ha' hρ hδ hε
    refine ⟨hv, ?_⟩
    intro s hs
    exact secondLayerSemantics_below_compare hs (hs.preservation (.beta A b a))
      hs.app_below_top hρ hρ hδ hδ
      (congrArg ShapeValue.asArity (shapeEval_step hs rfl hρ (.beta A b a)))
      (upperGridSemantics_step hs hρ hδ (.beta A b a)).1 hv
  | @appFun f f' a hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (secondLayerSemantics p Γ ρ δ ε (.app f a)).1 = (secondLayerSemantics p Γ ρ δ ε (.app f' a)).1 := by
      erw [secondLayerSemantics_app hf ha hρ hδ, secondLayerSemantics_app (hf.preservation hs) ha hρ hδ,
        shapeEval_step hf rfl hρ hs, (upperGridSemantics_step hf hρ hδ hs).1, (ih hf hρ hδ hε).1]
    refine ⟨hv, ?_⟩
    intro s ht
    exact secondLayerSemantics_below_compare ht (ht.preservation (.appFun a hs)) ht.app_below_top hρ hρ hδ hδ
      (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.appFun a hs)))
      (upperGridSemantics_step ht hρ hδ (.appFun a hs)).1 hv
  | @appArg f a a' hs ih =>
    obtain ⟨A, B, hf, ha, _⟩ := h.generation
    have hv : (secondLayerSemantics p Γ ρ δ ε (.app f a)).1 = (secondLayerSemantics p Γ ρ δ ε (.app f a')).1 := by
      erw [secondLayerSemantics_app hf ha hρ hδ, secondLayerSemantics_app hf (ha.preservation hs) hρ hδ,
        shapeEval_step ha rfl hρ hs, (upperGridSemantics_step ha hρ hδ hs).1, (ih ha hρ hδ hε).1]
    refine ⟨hv, ?_⟩
    intro s ht
    exact secondLayerSemantics_below_compare ht (ht.preservation (.appArg f hs)) ht.app_below_top hρ hρ hδ hδ
      (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.appArg f hs)))
      (upperGridSemantics_step ht hρ hδ (.appArg f hs)).1 hv
  | @lamTy A A' b hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have hb' := hb.context_conv hA hA' hsA hc
    refine ⟨?_, fun _ _ => rfl⟩
    erw [secondLayerSemantics_lam hPi hb hρ hδ,
      secondLayerSemantics_lam (hPi.preservation (.piDom B hs)) hb' hρ hδ,
      ← shapeEval_step h rfl hρ (.lamTy b hs), ← (upperGridSemantics_step h hρ hδ (.lamTy b hs)).1]
    apply secondGridLambda_congr ((hA.goodAt rfl).arity_step hs).symm
    · intro x hx; exact firstGridShape_step hA hρ hs
    · intro x hx z; exact (firstGridShape_context_conversion hB hA hA' hsA hc).symm
    · intro x hx y hy
      exact congrFun (congrFun ((upperGridSemantics_step hA hρ hδ hs).2 sA hA) x) y
    · intro x hx y hy z w
      exact congrFun (congrFun
        ((upperGridSemantics_context_conversion hB hA hA' hc hρ hδ hx hy).2 sB hB).symm z) w
    · intro x hx y hy z hz
      exact (secondLayerSemantics_context_conversion hb hA hA' hc hρ hδ hε hx hy hz).1.symm
  | @lamBody A b b' hs ih =>
    obtain ⟨B, s, hPi, hb, _, _⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    refine ⟨?_, fun _ _ => rfl⟩
    erw [secondLayerSemantics_lam hPi hb hρ hδ, secondLayerSemantics_lam hPi (hb.preservation hs) hρ hδ,
      ← shapeEval_step h rfl hρ (.lamBody A hs), ← (upperGridSemantics_step h hρ hδ (.lamBody A hs)).1]
    apply secondGridLambda_congr rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    intro x hx y hy z hz
    exact (ih hb (hρ.up hx) (hδ.up hA hy) (hε.up hA hρ hx hz)).1
  | @piDom A A' B hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping (p + 5) Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have hA' := hA.preservation hs
    have hc : Conv A A' := .fwd (.refl _) hs
    have hm := upperGridSemantics_step ht hρ hδ (.piDom B hs)
    have he : secondLayerSemantics p Γ ρ δ ε (.pi A B) = secondLayerSemantics p Γ ρ δ ε (.pi A' B) := by
      apply secondLayerSemantics_pi_compare ht (ht.preservation (.piDom B hs)) hρ hρ hδ hδ
        ((hA.goodAt rfl).arity_step hs).symm ((ht.goodAt rfl).arity_step (.piDom B hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piDom B hs))) (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; exact firstGridShape_step hA hρ hs
      · intro x hx z; exact (firstGridShape_context_conversion hB hA hA' hsA hc).symm
      · intro x hx y hy
        exact congrFun (congrFun ((upperGridSemantics_step hA hρ hδ hs).2 sA hA) x) y
      · intro x hx y hy
        exact ((upperGridSemantics_context_conversion hB hA hA' hc hρ hδ hx hy).2 sB hB).symm
      · intro x hx y hy z hz
        exact congrFun (congrFun (congrFun ((ih hA hρ hδ hε).2 sA hA) x) y) z
      · intro x hx y hy z hz
        exact ((secondLayerSemantics_context_conversion hB hA hA' hc hρ hδ hε hx hy hz).2 sB hB).symm
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩
  | @piCod A B B' hs ih =>
    obtain ⟨sA, sB, s, hA, hB, hr, hsA, hsB, hsS, _⟩ := h.generation
    have ht : BoundedTyping (p + 5) Γ (.pi A B) (.srt s) := .pi hA hB hr hsA hsB hsS
    have hm := upperGridSemantics_step ht hρ hδ (.piCod A hs)
    have he : secondLayerSemantics p Γ ρ δ ε (.pi A B) = secondLayerSemantics p Γ ρ δ ε (.pi A B') := by
      apply secondLayerSemantics_pi_compare ht (ht.preservation (.piCod A hs)) hρ hρ hδ hδ rfl
        ((ht.goodAt rfl).arity_step (.piCod A hs)).symm
        (congrArg ShapeValue.asArity (shapeEval_step ht rfl hρ (.piCod A hs))) (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; rfl
      · intro x hx z; exact firstGridShape_step hB (hρ.up hx) hs
      · intro x hx y hy; rfl
      · intro x hx y hy; exact (upperGridSemantics_step hB (hρ.up hx) (hδ.up hA hy) hs).2 sB hB
      · intro x hx y hy z hz; rfl
      · intro x hx y hy z hz
        exact (ih hB (hρ.up hx) (hδ.up hA hy) (hε.up hA hρ hx hz)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

theorem secondLayerSemantics_steps_value (h : BoundedTyping (p + 5) Γ t T)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hs : Steps t t') : (secondLayerSemantics p Γ ρ δ ε t).1 = (secondLayerSemantics p Γ ρ δ ε t').1 := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact (secondLayerSemantics_step h hρ hδ hε hs).1.trans (ih (h.preservation hs))

theorem secondLayerSemantics_steps_carrier (h : BoundedTyping (p + 5) Γ A (.srt s))
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hs : Steps A A') : (secondLayerSemantics p Γ ρ δ ε A).2 = (secondLayerSemantics p Γ ρ δ ε A').2 := by
  induction hs with
  | refl => rfl
  | head hs hr ih => exact ((secondLayerSemantics_step h hρ hδ hε hs).2 s h).trans (ih (h.preservation hs))

theorem FiberTypeExpression.secondLayerSemantics_carrier_red (h : FiberTypeExpression (p + 5) Γ A)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hr : Red A A') : (secondLayerSemantics p Γ ρ δ ε A).2 = (secondLayerSemantics p Γ ρ δ ε A').2 := by
  rcases h with ⟨s, hA⟩ | ⟨s, he⟩
  · exact secondLayerSemantics_steps_carrier hA hρ hδ hε hr.steps
  · erw [he, red_srt hr s he]

theorem secondLayerSemantics_carrier_conv (hA : FiberTypeExpression (p + 5) Γ A) (hB : FiberTypeExpression (p + 5) Γ B)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hc : Conv A B) : (secondLayerSemantics p Γ ρ δ ε A).2 = (secondLayerSemantics p Γ ρ δ ε B).2 := by
  obtain ⟨C, hC, hC'⟩ := conv_join hc
  exact (hA.secondLayerSemantics_carrier_red hρ hδ hε hC).trans
    (hB.secondLayerSemantics_carrier_red hρ hδ hε hC').symm

theorem type_secondLayerSemantics_conv (ht : BoundedTyping (p + 5) Γ t A) (hB : BoundedTyping (p + 5) Γ B (.srt s))
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hc : Conv A B) : (secondLayerSemantics p Γ ρ δ ε A).2 = (secondLayerSemantics p Γ ρ δ ε B).2 :=
  secondLayerSemantics_carrier_conv ht.type_expression (.inl ⟨s, hB⟩) hρ hδ hε hc

end Submission.Helpers
