import Submission.SecondLayerSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 2000000

abbrev ThirdGridValue (p : Nat) := TowerValue (carrierGrid (p + 4) 3)
variable {p : Nat} {δ δ' : Nat → UpperGridValue (p + 1)}
  {ε ε' : Nat → SecondLayerValue p} {ζ : Nat → ThirdGridValue p}
  {x : ShapeValue} {y : UpperGridValue (p + 1)} {z : SecondLayerValue p} {w : ThirdGridValue p}

noncomputable def thirdGridShape (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue (p + 1)) (ε : Nat → SecondLayerValue p) (A : Tm) :
    ShapeValue → UpperGridValue (p + 1) → SecondLayerValue p → SecondLayerCode p :=
  (secondLayerSemantics p Γ ρ δ ε A).2

noncomputable def inferredThirdGrid (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue (p + 1)) (ε : Nat → SecondLayerValue p) (t : Tm) : SecondLayerCode p :=
  thirdGridShape p Γ ρ δ ε (chosenType (p + 5) Γ t) (shapeEval (p + 5) (p + 3) Γ ρ t)
    (upperGridSemantics (p + 1) Γ ρ δ t).1 (secondLayerSemantics p Γ ρ δ ε t).1

theorem thirdGridShape_conv (hA : FiberTypeExpression (p + 5) Γ A)
    (hB : FiberTypeExpression (p + 5) Γ B) (hρ : ShapeContext (.type (p + 3)) Γ ρ)
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hc : Conv A B) : thirdGridShape p Γ ρ δ ε A = thirdGridShape p Γ ρ δ ε B :=
  secondLayerSemantics_carrier_conv hA hB hρ hδ hε hc

theorem inferredThirdGrid_eq (h : BoundedTyping (p + 5) Γ t A)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ)
    (hε : SecondGridContext (p + 1) Γ ρ δ ε) :
    inferredThirdGrid p Γ ρ δ ε t = thirdGridShape p Γ ρ δ ε A
      (shapeEval (p + 5) (p + 3) Γ ρ t) (upperGridSemantics (p + 1) Γ ρ δ t).1
        (secondLayerSemantics p Γ ρ δ ε t).1 := by
  unfold inferredThirdGrid
  rw [thirdGridShape_conv (chosenType_typing h).type_expression h.type_expression hρ hδ hε
    (typing_unique (chosenType_typing h).forget h.forget)]

theorem thirdGridShape_ren (h : BoundedTyping (p + 5) Γ A (.srt s))
    (hw : BoundedWf (p + 5) Δ) (hr : RenCtx Γ Δ ι)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hρ' : ShapeContext (.type (p + 3)) Δ ρ')
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hδ' : FirstGridContext (p + 2) Δ ρ' δ')
    (heρ : ∀ j, ρ' (ι j) = ρ j) (heδ : ∀ j, δ' (ι j) = δ j) (heε : ∀ j, ε' (ι j) = ε j) :
    thirdGridShape p Δ ρ' δ' ε' (ren ι A) = thirdGridShape p Γ ρ δ ε A :=
  (secondLayerSemantics_ren h hw hr hρ hρ' hδ hδ' heρ heδ heε).2 s h

theorem inferredThirdGrid_ren (h : BoundedTyping (p + 5) Γ t A)
    (hw : BoundedWf (p + 5) Δ) (hr : RenCtx Γ Δ ι)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hρ' : ShapeContext (.type (p + 3)) Δ ρ')
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hδ' : FirstGridContext (p + 2) Δ ρ' δ')
    (hε : SecondGridContext (p + 1) Γ ρ δ ε) (hε' : SecondGridContext (p + 1) Δ ρ' δ' ε')
    (heρ : ∀ j, ρ' (ι j) = ρ j) (heδ : ∀ j, δ' (ι j) = δ j) (heε : ∀ j, ε' (ι j) = ε j) :
    inferredThirdGrid p Δ ρ' δ' ε' (ren ι t) = inferredThirdGrid p Γ ρ δ ε t := by
  rw [inferredThirdGrid_eq (h.rename hw hr) hρ' hδ' hε', inferredThirdGrid_eq h hρ hδ hε,
    shapeEval_ren h hw hr rfl heρ, (upperGridSemantics_ren h hw hr hρ hρ' heρ heδ).1,
    (secondLayerSemantics_ren h hw hr hρ hρ' hδ hδ' heρ heδ heε).1]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A; rfl
  · rw [thirdGridShape_ren hA hw hr hρ hρ' hδ hδ' heρ heδ heε]

theorem thirdGridShape_subst (hB : BoundedTyping (p + 5) (A :: Γ) B (.srt sB))
    (ha : BoundedTyping (p + 5) Γ a A) (hA : BoundedTyping (p + 5) Γ A (.srt sA))
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ)
    (hε : SecondGridContext (p + 1) Γ ρ δ ε) :
    thirdGridShape p Γ ρ δ ε (subst 0 a B) =
      thirdGridShape p (A :: Γ) (push (shapeEval (p + 5) (p + 3) Γ ρ a) ρ)
        (push (upperGridSemantics (p + 1) Γ ρ δ a).1 δ)
        (push (secondLayerSemantics p Γ ρ δ ε a).1 ε) B :=
  secondLayerSemantics_subst_carrier hB ha hA hρ hδ hε

def ThirdGridContext (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue (p + 1)) (ε : Nat → SecondLayerValue p)
    (ζ : Nat → ThirdGridValue p) : Prop :=
  ∀ j A, Γ[j]? = some A → (ζ j).code = thirdGridShape p Γ ρ δ ε (lift (j + 1) 0 A) (ρ j) (δ j) (ε j)

theorem ThirdGridContext.up (h : ThirdGridContext p Γ ρ δ ε ζ)
    (hA : BoundedTyping (p + 5) Γ A (.srt s)) (hρ : ShapeContext (.type (p + 3)) Γ ρ)
    (hδ : FirstGridContext (p + 2) Γ ρ δ)
    (hx : x.code = arityAt (.type (p + 3)) A) (hy : y.code = firstGridShape (p + 2) Γ ρ A x)
    (hw : w.code = thirdGridShape p Γ ρ δ ε A x y z) :
    ThirdGridContext p (A :: Γ) (push x ρ) (push y δ) (push z ε) (push w ζ) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      thirdGridShape_ren hA (.cons hA.wf hA) (.weaken Γ A) hρ (hρ.up hx) hδ (hδ.up hA hy)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)] using hw
  | succ j =>
    obtain ⟨sC, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1),
      thirdGridShape_ren hC (.cons hA.wf hA) (.weaken Γ A) hρ (hρ.up hx) hδ (hδ.up hA hy)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)] using h j C hj

theorem ThirdGridContext.var_code (h : ThirdGridContext p Γ ρ δ ε ζ)
    (hw : BoundedWf (p + 5) Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ)
    (hε : SecondGridContext (p + 1) Γ ρ δ ε) :
    (ζ j).code = inferredThirdGrid p Γ ρ δ ε (.var j) := by
  rw [inferredThirdGrid_eq (.var hw hj) hρ hδ hε, upperGridSemantics_var hδ hw hj hρ,
    secondLayerSemantics_var hε hw hj hρ hδ]
  exact h j A hj

theorem inferredThirdGrid_step (h : BoundedTyping (p + 5) Γ t A)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ)
    (hε : SecondGridContext (p + 1) Γ ρ δ ε) (hs : Step t t') :
    inferredThirdGrid p Γ ρ δ ε t = inferredThirdGrid p Γ ρ δ ε t' := by
  rw [inferredThirdGrid_eq h hρ hδ hε, inferredThirdGrid_eq (h.preservation hs) hρ hδ hε,
    shapeEval_step h rfl hρ hs, (upperGridSemantics_step h hρ hδ hs).1,
    (secondLayerSemantics_step h hρ hδ hε hs).1]

noncomputable def defaultThirdGridEnv (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue (p + 1)) (ε : Nat → SecondLayerValue p) (j : Nat) : ThirdGridValue p :=
  let A := thirdGridShape p Γ ρ δ ε (lift (j + 1) 0 (Γ[j]?.getD (.srt .prop))) (ρ j) (δ j) (ε j)
  ⟨A, (carrierGrid (p + 4) 3).point A⟩

theorem defaultThirdGridEnv_context (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue (p + 1)) (ε : Nat → SecondLayerValue p) :
    ThirdGridContext p Γ ρ δ ε (defaultThirdGridEnv p Γ ρ δ ε) := by
  intro j A hj
  simp only [defaultThirdGridEnv, hj, Option.getD_some]

/-- Four compatible source coordinates exist without assuming normalization
or even well-formedness of the source context. -/
theorem thirdGrid_environments (p : Nat) (Γ : List Tm) :
    ∃ (ρ : Nat → ShapeValue) (δ : Nat → UpperGridValue (p + 1))
      (ε : Nat → SecondLayerValue p) (ζ : Nat → ThirdGridValue p),
      ShapeContext (.type (p + 3)) Γ ρ ∧ FirstGridContext (p + 2) Γ ρ δ ∧
        SecondGridContext (p + 1) Γ ρ δ ε ∧ ThirdGridContext p Γ ρ δ ε ζ := by
  obtain ⟨ρ, δ, ε, hρ, hδ, hε⟩ := secondGrid_environments (p + 1) Γ
  exact ⟨ρ, δ, ε, defaultThirdGridEnv p Γ ρ δ ε, hρ, hδ, hε,
    defaultThirdGridEnv_context p Γ ρ δ ε⟩

end Submission.Helpers
