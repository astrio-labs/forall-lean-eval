import Submission.MiddleSoundness
import Submission.ThirdValues

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def thirdShape (Γ : List Tm) (ρ : Nat → ShapeValue) (δ : Nat → MiddleValue)
    (A : Tm) : ShapeValue → MiddleValue → ThirdCode := (middleSemantics Γ ρ δ A).2

noncomputable def inferredThird (Γ : List Tm) (ρ : Nat → ShapeValue) (δ : Nat → MiddleValue)
    (t : Tm) : ThirdCode :=
  thirdShape Γ ρ δ (chosenType 3 Γ t) (shapeEval 3 1 Γ ρ t) (middleSemantics Γ ρ δ t).1

theorem thirdShape_conv (hA : FiberTypeExpression 3 Γ A) (hB : FiberTypeExpression 3 Γ B)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hc : Conv A B) :
    thirdShape Γ ρ δ A = thirdShape Γ ρ δ B := middleSemantics_carrier_conv hA hB hρ hδ hc

theorem inferredThird_eq (h : BoundedTyping 3 Γ t A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    inferredThird Γ ρ δ t = thirdShape Γ ρ δ A (shapeEval 3 1 Γ ρ t) (middleSemantics Γ ρ δ t).1 := by
  unfold inferredThird
  rw [thirdShape_conv (chosenType_typing h).type_expression h.type_expression hρ hδ
    (typing_unique (chosenType_typing h).forget h.forget)]

theorem thirdShape_pi (hu : u.code = arityAt (.type 1) (.pi A B))
    (hf : f.code = middleShape 3 1 Γ ρ (.pi A B) u) :
    thirdShape Γ ρ δ (.pi A B) u f =
      thirdProduct (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (thirdShape Γ ρ δ A)
        (fun x y => thirdShape (A :: Γ) (push x ρ) (push y δ) B) u f :=
  middleSemantics_pi hu hf

theorem thirdShape_ren (h : BoundedTyping 3 Γ A (.srt s)) (hw : BoundedWf 3 Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j) :
    thirdShape Δ ρ' δ' (ren r A) = thirdShape Γ ρ δ A :=
  (middleSemantics_ren h hw hr hρ hρ' heρ heδ).2 s h

theorem inferredThird_ren (h : BoundedTyping 3 Γ t A) (hw : BoundedWf 3 Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j) :
    inferredThird Δ ρ' δ' (ren r t) = inferredThird Γ ρ δ t := by
  rw [inferredThird_eq (h.rename hw hr) hρ' hδ', inferredThird_eq h hρ hδ,
    shapeEval_ren h hw hr rfl heρ, (middleSemantics_ren h hw hr hρ hρ' heρ heδ).1]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A; rfl
  · rw [thirdShape_ren hA hw hr hρ hρ' heρ heδ]

theorem thirdShape_substitute_related (h : BoundedTyping 3 Γ A (.srt s))
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 1) (σ j) = false)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 3 1 Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (middleSemantics Δ ρ' δ' (σ j)).1 = δ j) :
    thirdShape Δ ρ' δ' (sub σ A) = thirdShape Γ ρ δ A :=
  (middleSemantics_substitute_related h hw hσ hk hρ hρ' hδ hδ' heρ heδ).2 s h

theorem inferredThird_substitute_related (h : BoundedTyping 3 Γ t A)
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 1) (σ j) = false)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 3 1 Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (middleSemantics Δ ρ' δ' (σ j)).1 = δ j) :
    inferredThird Δ ρ' δ' (sub σ t) = inferredThird Γ ρ δ t := by
  rw [inferredThird_eq (h.substitute hw hσ) hρ' hδ', inferredThird_eq h hρ hδ,
    middleShapeEval_substitute_related h hw hσ hk heρ,
    (middleSemantics_substitute_related h hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
  rcases h.regularity_top with ⟨s, hs, hsn⟩ | ⟨s, hA, hsn⟩
  · subst A; rfl
  · rw [thirdShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ]

theorem thirdShape_subst (hB : BoundedTyping 3 (A :: Γ) B (.srt sB))
    (ha : BoundedTyping 3 Γ a A) (hA : BoundedTyping 3 Γ A (.srt sA))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    thirdShape Γ ρ δ (subst 0 a B) =
      thirdShape (A :: Γ) (push (shapeEval 3 1 Γ ρ a) ρ)
        (push (middleSemantics Γ ρ δ a).1 δ) B :=
  middleSemantics_subst_carrier hB ha hA hρ hδ

def ThirdContext (Γ : List Tm) (ρ : Nat → ShapeValue) (δ : Nat → MiddleValue)
    (ε : Nat → ThirdValue) : Prop :=
  ∀ j A, Γ[j]? = some A → (ε j).code = thirdShape Γ ρ δ (lift (j + 1) 0 A) (ρ j) (δ j)

theorem ThirdContext.up (h : ThirdContext Γ ρ δ ε)
    (hA : BoundedTyping 3 Γ A (.srt s)) (hρ : ShapeContext (.type 1) Γ ρ)
    (hx : x.code = arityAt (.type 1) A) (hz : z.code = thirdShape Γ ρ δ A x y) :
    ThirdContext (A :: Γ) (push x ρ) (push y δ) (push z ε) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      thirdShape_ren hA (.cons hA.wf hA) (.weaken Γ A) hρ (hρ.up hx)
        (fun _ => rfl) (fun _ => rfl)] using hz
  | succ j =>
    obtain ⟨r, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1),
      thirdShape_ren hC (.cons hA.wf hA) (.weaken Γ A) hρ (hρ.up hx)
        (fun _ => rfl) (fun _ => rfl)] using h j C hj

theorem ThirdContext.var_code (h : ThirdContext Γ ρ δ ε)
    (hw : BoundedWf 3 Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (ε j).code = inferredThird Γ ρ δ (.var j) := by
  rw [inferredThird_eq (.var hw hj) hρ hδ, middleSemantics_var hδ hw hj hρ]
  exact h j A hj

end Submission.Helpers
