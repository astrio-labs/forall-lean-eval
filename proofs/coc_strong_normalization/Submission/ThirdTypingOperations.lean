import Submission.ThirdDecoding

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem thirdProduct_types_conv
    (hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hPi' : BoundedTyping 3 Γ (.pi A' B') (.srt s'))
    (hc : Conv (.pi A B) (.pi A' B'))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    thirdShape Γ ρ δ A = thirdShape Γ ρ δ A' ∧
    (∀ x, x.code = arityAt (.type 1) A → ∀ y,
      y.code = middleShape 3 1 Γ ρ A x →
      thirdShape (A :: Γ) (push x ρ) (push y δ) B =
        thirdShape (A' :: Γ) (push x ρ) (push y δ) B') := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi.pi_codomain
  obtain ⟨sA', hA', hsA'⟩ := hPi'.pi_domain
  obtain ⟨sB', hB', hsB'⟩ := hPi'.pi_codomain
  obtain ⟨hcA, hcB⟩ := conv_pi_inj hc
  refine ⟨thirdShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hρ hδ hcA, ?_⟩
  intro x hx y hy
  have hB'' := hB'.context_conv hA' hA hsA' (conv_symm hcA)
  exact (thirdShape_conv (.inl ⟨sB, hB⟩) (.inl ⟨sB', hB''⟩)
    (hρ.up hx) (hδ.up hA rfl hy) hcB).trans
    ((middleSemantics_context_conversion hB'' hA hA' hcA hρ hδ hx hy).2 sB' hB'').symm

theorem thirdSemantics_lam (hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 3 (A :: Γ) b B)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.lam A b)).1 =
      thirdLambda (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (thirdShape Γ ρ δ A)
        (fun x y => thirdShape (A :: Γ) (push x ρ) (push y δ) B)
        (shapeEval 3 1 Γ ρ (.lam A b)) (middleSemantics Γ ρ δ (.lam A b)).1
        (fun x y z => (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1) := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  have hbc (x : ShapeValue) (hx : x.code = arityAt (.type 1) A) (y : ShapeValue) :
      middleShape 3 1 (A :: Γ) (push x ρ) (chosenType 3 (A :: Γ) b) y =
        middleShape 3 1 (A :: Γ) (push x ρ) B y :=
    middleShape_conv (chosenType_typing hb).type_expression hb.type_expression rfl
      (hρ.up hx) (typing_unique (chosenType_typing hb).forget hb.forget)
  have htc (x : ShapeValue) (hx : x.code = arityAt (.type 1) A)
      (y : MiddleValue) (hy : y.code = middleShape 3 1 Γ ρ A x) :
      thirdShape (A :: Γ) (push x ρ) (push y δ) (chosenType 3 (A :: Γ) b) =
        thirdShape (A :: Γ) (push x ρ) (push y δ) B :=
    thirdShape_conv (chosenType_typing hb).type_expression hb.type_expression
      (hρ.up hx) (hδ.up hA rfl hy) (typing_unique (chosenType_typing hb).forget hb.forget)
  have he := thirdLambda_congr (u := shapeEval 3 1 Γ ρ (.lam A b))
    (f := (middleSemantics Γ ρ δ (.lam A b)).1)
    (D := fun x => middleShape 3 1 Γ ρ A x) (d := thirdShape Γ ρ δ A)
    (g := fun x y z => (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1)
    rfl (fun _ _ => rfl) hbc (fun _ _ _ _ => rfl)
    (fun x hx y hy z w => congrFun (congrFun (htc x hx y hy) z) w)
    (fun _ _ _ _ _ _ => rfl)
  change ThirdValue.force _ (thirdLambda _ _ _ _ _ _ _ _) = _
  rw [he]
  apply ThirdValue.force_eq
  have ht := BoundedTyping.lam hPi hb hPi.sort_bound
  rw [thirdLambda_code, inferredThird_eq ht hρ hδ,
    thirdShape_pi (shapeEval_typed_code ht rfl hρ) (middleSemantics_typed_code ht hρ)]

theorem thirdSemantics_app (hf : BoundedTyping 3 Γ f (.pi A B))
    (ha : BoundedTyping 3 Γ a A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.app f a)).1 =
      thirdApply (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (thirdShape Γ ρ δ A)
        (fun x y => thirdShape (A :: Γ) (push x ρ) (push y δ) B)
        (shapeEval 3 1 Γ ρ f) (middleSemantics Γ ρ δ f).1 (thirdSemantics Γ ρ δ ε f).1
        (shapeEval 3 1 Γ ρ a) (middleSemantics Γ ρ δ a).1 (thirdSemantics Γ ρ δ ε a).1 := by
  obtain ⟨s, hPi⟩ := hf.pi_type
  obtain ⟨s', hPi'⟩ := (chosenProduct_typing hf).pi_type
  have hc := typing_unique (chosenProduct_typing hf).forget hf.forget
  obtain ⟨heA, heD, heB⟩ := middleProduct_types_conv hPi' hPi hc rfl hρ
  obtain ⟨hed, hec⟩ := thirdProduct_types_conv hPi' hPi hc hρ hδ
  have he := thirdApply_congr
    (u := shapeEval 3 1 Γ ρ f) (f := (middleSemantics Γ ρ δ f).1)
    (g := (thirdSemantics Γ ρ δ ε f).1)
    (x := shapeEval 3 1 Γ ρ a) (y := (middleSemantics Γ ρ δ a).1)
    (z := (thirdSemantics Γ ρ δ ε a).1)
    heA (fun x _ => heD x) heB
    (fun x _ y _ => congrFun (congrFun hed x) y)
    (fun x hx y hy z w => congrFun (congrFun (hec x hx y hy) z) w)
  change ThirdValue.force _ (thirdApply _ _ _ _ _ _ _ _ _ _ _) = _
  rw [he]
  apply ThirdValue.force_eq
  rw [thirdApply_code _ _ _ _ _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ)
    (middleSemantics_typed_code ha hρ), inferredThird_eq (.app hf ha) hρ hδ]
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  rw [thirdShape_subst hB ha hA hρ hδ, middleSemantics_app hf ha hρ]
  rfl

end Submission.Helpers
