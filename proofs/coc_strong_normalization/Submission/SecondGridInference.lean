import Submission.UpperGridSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

abbrev SecondGridValue (p : Nat) := TowerValue (carrierGrid (p + 3) 2)
variable {p : Nat} {δ δ' : Nat → UpperGridValue p} {ε : Nat → SecondGridValue p}
  {u x : ShapeValue} {f y : UpperGridValue p} {z : SecondGridValue p}

noncomputable def secondGridShape (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue) (δ : Nat → UpperGridValue p)
    (A : Tm) : ShapeValue → UpperGridValue p → UpperGridCode p := (upperGridSemantics p Γ ρ δ A).2

noncomputable def inferredSecondGrid (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue) (δ : Nat → UpperGridValue p)
    (t : Tm) : UpperGridCode p :=
  secondGridShape p Γ ρ δ (chosenType (p + 4) Γ t) (shapeEval (p + 4) (p + 2) Γ ρ t) (upperGridSemantics p Γ ρ δ t).1

theorem secondGridShape_conv (hA : FiberTypeExpression (p + 4) Γ A) (hB : FiberTypeExpression (p + 4) Γ B)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ) (hc : Conv A B) :
    secondGridShape p Γ ρ δ A = secondGridShape p Γ ρ δ B := upperGridSemantics_carrier_conv hA hB hρ hδ hc

theorem inferredSecondGrid_eq (h : BoundedTyping (p + 4) Γ t A)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ) :
    inferredSecondGrid p Γ ρ δ t = secondGridShape p Γ ρ δ A (shapeEval (p + 4) (p + 2) Γ ρ t) (upperGridSemantics p Γ ρ δ t).1 := by
  unfold inferredSecondGrid
  rw [secondGridShape_conv (chosenType_typing h).type_expression h.type_expression hρ hδ
    (typing_unique (chosenType_typing h).forget h.forget)]

theorem secondGridShape_pi (hu : u.code = arityAt (.type (p + 2)) (.pi A B))
    (hf : f.code = firstGridShape (p + 1) Γ ρ (.pi A B) u) :
    secondGridShape p Γ ρ δ (.pi A B) u f =
      upperGridProduct p (arityAt (.type (p + 2)) A)
        (fun x => firstGridShape (p + 1) Γ ρ A x)
        (fun x y => firstGridShape (p + 1) (A :: Γ) (push x ρ) B y)
        (secondGridShape p Γ ρ δ A)
        (fun x y => secondGridShape p (A :: Γ) (push x ρ) (push y δ) B) u f :=
  upperGridSemantics_pi hu hf

theorem secondGridShape_ren (h : BoundedTyping (p + 4) Γ A (.srt s)) (hw : BoundedWf (p + 4) Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j) :
    secondGridShape p Δ ρ' δ' (ren r A) = secondGridShape p Γ ρ δ A :=
  (upperGridSemantics_ren h hw hr hρ hρ' heρ heδ).2 s h

theorem inferredSecondGrid_ren (h : BoundedTyping (p + 4) Γ t A) (hw : BoundedWf (p + 4) Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ')
    (hδ : FirstGridContext (p + 1) Γ ρ δ) (hδ' : FirstGridContext (p + 1) Δ ρ' δ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j) :
    inferredSecondGrid p Δ ρ' δ' (ren r t) = inferredSecondGrid p Γ ρ δ t := by
  rw [inferredSecondGrid_eq (h.rename hw hr) hρ' hδ', inferredSecondGrid_eq h hρ hδ,
    shapeEval_ren h hw hr rfl heρ, (upperGridSemantics_ren h hw hr hρ hρ' heρ heδ).1]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A; rfl
  · rw [secondGridShape_ren hA hw hr hρ hρ' heρ heδ]

theorem secondGridShape_substitute_related (h : BoundedTyping (p + 4) Γ A (.srt s))
    (hw : BoundedWf (p + 4) Δ) (hσ : BoundedSubCtx (p + 4) Γ Δ σ)
    (hk : ∀ j, kindAt (.type (p + 2)) (σ j) = false)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ')
    (hδ : FirstGridContext (p + 1) Γ ρ δ) (hδ' : FirstGridContext (p + 1) Δ ρ' δ')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval (p + 4) (p + 2) Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (upperGridSemantics p Δ ρ' δ' (σ j)).1 = δ j) :
    secondGridShape p Δ ρ' δ' (sub σ A) = secondGridShape p Γ ρ δ A :=
  (upperGridSemantics_substitute_related h hw hσ hk hρ hρ' hδ hδ' heρ heδ).2 s h

theorem inferredSecondGrid_substitute_related (h : BoundedTyping (p + 4) Γ t A)
    (hw : BoundedWf (p + 4) Δ) (hσ : BoundedSubCtx (p + 4) Γ Δ σ)
    (hk : ∀ j, kindAt (.type (p + 2)) (σ j) = false)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ')
    (hδ : FirstGridContext (p + 1) Γ ρ δ) (hδ' : FirstGridContext (p + 1) Δ ρ' δ')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval (p + 4) (p + 2) Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (upperGridSemantics p Δ ρ' δ' (σ j)).1 = δ j) :
    inferredSecondGrid p Δ ρ' δ' (sub σ t) = inferredSecondGrid p Γ ρ δ t := by
  rw [inferredSecondGrid_eq (h.substitute hw hσ) hρ' hδ', inferredSecondGrid_eq h hρ hδ,
    upperShapeEval_substitute_related h hw hσ hk heρ,
    (upperGridSemantics_substitute_related h hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A; rfl
  · rw [secondGridShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ]

theorem secondGridShape_subst (hB : BoundedTyping (p + 4) (A :: Γ) B (.srt sB))
    (ha : BoundedTyping (p + 4) Γ a A) (hA : BoundedTyping (p + 4) Γ A (.srt sA))
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ) :
    secondGridShape p Γ ρ δ (subst 0 a B) =
      secondGridShape p (A :: Γ) (push (shapeEval (p + 4) (p + 2) Γ ρ a) ρ)
        (push (upperGridSemantics p Γ ρ δ a).1 δ) B :=
  upperGridSemantics_subst_carrier hB ha hA hρ hδ

def SecondGridContext (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue) (δ : Nat → UpperGridValue p)
    (ε : Nat → SecondGridValue p) : Prop :=
  ∀ j A, Γ[j]? = some A → (ε j).code = secondGridShape p Γ ρ δ (lift (j + 1) 0 A) (ρ j) (δ j)

theorem SecondGridContext.up (h : SecondGridContext p Γ ρ δ ε)
    (hA : BoundedTyping (p + 4) Γ A (.srt s)) (hρ : ShapeContext (.type (p + 2)) Γ ρ)
    (hx : x.code = arityAt (.type (p + 2)) A) (hz : z.code = secondGridShape p Γ ρ δ A x y) :
    SecondGridContext p (A :: Γ) (push x ρ) (push y δ) (push z ε) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      secondGridShape_ren hA (.cons hA.wf hA) (.weaken Γ A) hρ (hρ.up hx)
        (fun _ => rfl) (fun _ => rfl)] using hz
  | succ j =>
    obtain ⟨r, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1),
      secondGridShape_ren hC (.cons hA.wf hA) (.weaken Γ A) hρ (hρ.up hx)
        (fun _ => rfl) (fun _ => rfl)] using h j C hj

theorem SecondGridContext.var_code (h : SecondGridContext p Γ ρ δ ε)
    (hw : BoundedWf (p + 4) Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ) :
    (ε j).code = inferredSecondGrid p Γ ρ δ (.var j) := by
  rw [inferredSecondGrid_eq (.var hw hj) hρ hδ, upperGridSemantics_var hδ hw hj hρ]
  exact h j A hj

theorem inferredSecondGrid_step (h : BoundedTyping (p + 4) Γ t A)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hδ : FirstGridContext (p + 1) Γ ρ δ)
    (hs : Step t t') : inferredSecondGrid p Γ ρ δ t = inferredSecondGrid p Γ ρ δ t' := by
  rw [inferredSecondGrid_eq h hρ hδ, inferredSecondGrid_eq (h.preservation hs) hρ hδ,
    shapeEval_step h rfl hρ hs, (upperGridSemantics_step h hρ hδ hs).1]

noncomputable def defaultSecondGridEnv (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue p) (j : Nat) : SecondGridValue p :=
  let A := secondGridShape p Γ ρ δ (lift (j + 1) 0 (Γ[j]?.getD (.srt .prop))) (ρ j) (δ j)
  ⟨A, (carrierGrid (p + 3) 2).point A⟩

theorem defaultSecondGridEnv_context (p : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue p) : SecondGridContext p Γ ρ δ (defaultSecondGridEnv p Γ ρ δ) := by
  intro j A hj
  simp only [defaultSecondGridEnv, hj, Option.getD_some]

def defaultGridShapeEnv (p : Nat) (Γ : List Tm) (j : Nat) : ShapeValue :=
  let a := arityAt (.type (p + 2)) (Γ[j]?.getD (.srt .prop))
  ⟨a, a.shapePoint⟩

theorem defaultGridShapeEnv_context (p : Nat) (Γ : List Tm) :
    ShapeContext (.type (p + 2)) Γ (defaultGridShapeEnv p Γ) := by
  intro j A hj
  simp only [defaultGridShapeEnv, hj, Option.getD_some]

/-- Every source context has compatible values in the first three
coordinates, without a typing or normalization premise. -/
theorem secondGrid_environments (p : Nat) (Γ : List Tm) :
    ∃ (ρ : Nat → ShapeValue) (δ : Nat → UpperGridValue p) (ε : Nat → SecondGridValue p),
      ShapeContext (.type (p + 2)) Γ ρ ∧ FirstGridContext (p + 1) Γ ρ δ ∧ SecondGridContext p Γ ρ δ ε := by
  let ρ := defaultGridShapeEnv p Γ
  let δ := defaultFirstGridEnv (p + 1) Γ ρ
  exact ⟨ρ, δ, defaultSecondGridEnv p Γ ρ δ, defaultGridShapeEnv_context p Γ,
    defaultFirstGridEnv_context (p + 1) Γ ρ, defaultSecondGridEnv_context p Γ ρ δ⟩

end Submission.Helpers
