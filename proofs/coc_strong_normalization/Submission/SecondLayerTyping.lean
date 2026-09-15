import Submission.SecondLayerCongruence

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000
variable {r : Nat} {δ : Nat → UpperGridValue (r + 1)} {ε : Nat → SecondLayerValue r}

theorem secondGridProduct_types_conv
    (hPi : BoundedTyping (r + 5) Γ (.pi A B) (.srt s))
    (hPi' : BoundedTyping (r + 5) Γ (.pi A' B') (.srt s'))
    (hc : Conv (.pi A B) (.pi A' B'))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    secondGridShape (r + 1) Γ ρ δ A = secondGridShape (r + 1) Γ ρ δ A' ∧
    (∀ x, x.code = arityAt (.type (r + 3)) A → ∀ y,
      y.code = firstGridShape (r + 2) Γ ρ A x →
      secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) B =
        secondGridShape (r + 1) (A' :: Γ) (push x ρ) (push y δ) B') := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi.pi_codomain
  obtain ⟨sA', hA', hsA'⟩ := hPi'.pi_domain
  obtain ⟨sB', hB', hsB'⟩ := hPi'.pi_codomain
  obtain ⟨hcA, hcB⟩ := conv_pi_inj hc
  refine ⟨secondGridShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hρ hδ hcA, ?_⟩
  intro x hx y hy
  have hB'' := hB'.context_conv hA' hA hsA' (conv_symm hcA)
  exact (secondGridShape_conv (.inl ⟨sB, hB⟩) (.inl ⟨sB', hB''⟩)
    (hρ.up hx) (hδ.up hA hy) hcB).trans
    ((upperGridSemantics_context_conversion hB'' hA hA' hcA hρ hδ hx hy).2 sB' hB'').symm

theorem secondLayerSemantics_lam (hPi : BoundedTyping (r + 5) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 5) (A :: Γ) b B)
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε (.lam A b)).1 =
      secondGridLambda (r + 1) (arityAt (.type (r + 3)) A)
        (fun x => firstGridShape (r + 2) Γ ρ A x)
        (fun x y => firstGridShape (r + 2) (A :: Γ) (push x ρ) B y)
        (secondGridShape (r + 1) Γ ρ δ A)
        (fun x y => secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) B)
        (shapeEval (r + 5) (r + 3) Γ ρ (.lam A b)) (upperGridSemantics (r + 1) Γ ρ δ (.lam A b)).1
        (fun x y z => (secondLayerSemantics r (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1) := by
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  have hbc (x : ShapeValue) (hx : x.code = arityAt (.type (r + 3)) A) (y : ShapeValue) :
      firstGridShape (r + 2) (A :: Γ) (push x ρ) (chosenType (r + 5) (A :: Γ) b) y =
        firstGridShape (r + 2) (A :: Γ) (push x ρ) B y :=
    firstGridShape_conv (chosenType_typing hb).type_expression hb.type_expression
      (hρ.up hx) (typing_unique (chosenType_typing hb).forget hb.forget)
  have htc (x : ShapeValue) (hx : x.code = arityAt (.type (r + 3)) A)
      (y : UpperGridValue (r + 1)) (hy : y.code = firstGridShape (r + 2) Γ ρ A x) :
      secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) (chosenType (r + 5) (A :: Γ) b) =
        secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) B :=
    secondGridShape_conv (chosenType_typing hb).type_expression hb.type_expression
      (hρ.up hx) (hδ.up hA hy) (typing_unique (chosenType_typing hb).forget hb.forget)
  have he := secondGridLambda_congr (u := shapeEval (r + 5) (r + 3) Γ ρ (.lam A b))
    (f := (upperGridSemantics (r + 1) Γ ρ δ (.lam A b)).1)
    (D := fun x => firstGridShape (r + 2) Γ ρ A x) (d := secondGridShape (r + 1) Γ ρ δ A)
    (g := fun x y z => (secondLayerSemantics r (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1)
    rfl (fun _ _ => rfl) hbc (fun _ _ _ _ => rfl)
    (fun x hx y hy z w => congrFun (congrFun (htc x hx y hy) z) w)
    (fun _ _ _ _ _ _ => rfl)
  change TowerValue.force _ (secondGridLambda (r + 1) _ _ _ _ _ _ _ _) = _
  erw [he]
  apply TowerValue.force_eq
  have ht := BoundedTyping.lam hPi hb hPi.sort_bound
  erw [secondGridLambda_code, inferredSecondGrid_eq ht hρ hδ,
    secondGridShape_pi (shapeEval_typed_code ht rfl hρ) (upperGridSemantics_typed_code ht hρ)]

theorem secondLayerSemantics_app (hf : BoundedTyping (r + 5) Γ f (.pi A B))
    (ha : BoundedTyping (r + 5) Γ a A)
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε (.app f a)).1 =
      secondGridApply (r + 1) (arityAt (.type (r + 3)) A)
        (fun x => firstGridShape (r + 2) Γ ρ A x)
        (fun x y => firstGridShape (r + 2) (A :: Γ) (push x ρ) B y)
        (secondGridShape (r + 1) Γ ρ δ A)
        (fun x y => secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) B)
        (shapeEval (r + 5) (r + 3) Γ ρ f) (upperGridSemantics (r + 1) Γ ρ δ f).1 (secondLayerSemantics r Γ ρ δ ε f).1
        (shapeEval (r + 5) (r + 3) Γ ρ a) (upperGridSemantics (r + 1) Γ ρ δ a).1 (secondLayerSemantics r Γ ρ δ ε a).1 := by
  obtain ⟨s, hPi⟩ := hf.pi_type
  obtain ⟨s', hPi'⟩ := (chosenProduct_typing hf).pi_type
  have hc := typing_unique (chosenProduct_typing hf).forget hf.forget
  obtain ⟨heA, heD, heB⟩ := firstGridProduct_types_conv hPi' hPi hc hρ
  obtain ⟨hed, hec⟩ := secondGridProduct_types_conv hPi' hPi hc hρ hδ
  have he := secondGridApply_congr
    (u := shapeEval (r + 5) (r + 3) Γ ρ f) (f := (upperGridSemantics (r + 1) Γ ρ δ f).1)
    (g := (secondLayerSemantics r Γ ρ δ ε f).1)
    (x := shapeEval (r + 5) (r + 3) Γ ρ a) (y := (upperGridSemantics (r + 1) Γ ρ δ a).1)
    (z := (secondLayerSemantics r Γ ρ δ ε a).1)
    heA (fun x _ => heD x) heB
    (fun x _ y _ => congrFun (congrFun hed x) y)
    (fun x hx y hy z w => congrFun (congrFun (hec x hx y hy) z) w)
  change TowerValue.force _ (secondGridApply (r + 1) _ _ _ _ _ _ _ _ _ _ _) = _
  erw [he]
  apply TowerValue.force_eq
  rw [inferredSecondGrid_eq (.app hf ha) hρ hδ]
  exact secondGridApply_typed hf ha hρ hδ _ _

end Submission.Helpers
