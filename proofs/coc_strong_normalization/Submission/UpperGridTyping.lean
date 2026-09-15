import Submission.UpperGridDecoding
import Submission.FirstGridCongruence

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Abstraction uses the declared codomain rather than the arbitrary type
selected by carrier inference. -/
theorem upperGridSemantics_lam {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A B b : Tm} {s : Srt}
    (hPi : BoundedTyping (r + 4) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 4) (A :: Γ) b B) (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ (.lam A b)).1 =
      firstGridLambda (r + 1) (arityAt (.type (r + 2)) A)
        (fun x => firstGridShape (r + 1) Γ ρ A x)
        (fun x y => firstGridShape (r + 1) (A :: Γ) (push x ρ) B y)
        (shapeEval (r + 4) (r + 2) Γ ρ (.lam A b))
        (fun x y => (upperGridSemantics r (A :: Γ) (push x ρ) (push y δ) b).1) := by
  have hbc (x : ShapeValue) (hx : x.code = arityAt (.type (r + 2)) A) (y : ShapeValue) :
      firstGridShape (r + 1) (A :: Γ) (push x ρ) (chosenType (r + 4) (A :: Γ) b) y =
        firstGridShape (r + 1) (A :: Γ) (push x ρ) B y :=
    firstGridShape_conv (chosenType_typing hb).type_expression hb.type_expression
      (hρ.up hx) (typing_unique (chosenType_typing hb).forget hb.forget)
  have he := firstGridLambda_congr (r := r + 1) (u := shapeEval (r + 4) (r + 2) Γ ρ (.lam A b))
    (D := fun x => firstGridShape (r + 1) Γ ρ A x)
    (b := fun x y => (upperGridSemantics r (A :: Γ) (push x ρ) (push y δ) b).1)
    rfl (fun _ _ => rfl) hbc (fun _ _ _ _ => rfl)
  rw [upperGridSemantics]
  dsimp only
  erw [he]
  apply TowerValue.force_eq
  rw [firstGridLambda_code, inferredFirstGrid_eq (.lam hPi hb hPi.sort_bound) hρ,
    firstGridShape_pi hPi hρ]

/-- Application uses any convertible well-typed product, and its carrier is
the carrier obtained by typed single substitution. -/
theorem upperGridSemantics_app {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A B f a : Tm}
    (hf : BoundedTyping (r + 4) Γ f (.pi A B)) (ha : BoundedTyping (r + 4) Γ a A)
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ (.app f a)).1 =
      firstGridApply (r + 1) (arityAt (.type (r + 2)) A)
        (fun x => firstGridShape (r + 1) Γ ρ A x)
        (fun x y => firstGridShape (r + 1) (A :: Γ) (push x ρ) B y)
        (shapeEval (r + 4) (r + 2) Γ ρ f) (upperGridSemantics r Γ ρ δ f).1
        (shapeEval (r + 4) (r + 2) Γ ρ a) (upperGridSemantics r Γ ρ δ a).1 := by
  obtain ⟨s, hPi⟩ := hf.pi_type
  obtain ⟨s', hPi'⟩ := (chosenProduct_typing hf).pi_type
  obtain ⟨heA, heD, heB⟩ := firstGridProduct_types_conv hPi' hPi
    (typing_unique (chosenProduct_typing hf).forget hf.forget) hρ
  have he := firstGridApply_congr (r := r + 1)
    (u := shapeEval (r + 4) (r + 2) Γ ρ f) (f := (upperGridSemantics r Γ ρ δ f).1)
    (x := shapeEval (r + 4) (r + 2) Γ ρ a) (y := (upperGridSemantics r Γ ρ δ a).1)
    heA (fun x _ => heD x) heB
  rw [upperGridSemantics]
  dsimp only
  erw [he]
  apply TowerValue.force_eq
  rw [firstGridApply_code _ _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ),
    inferredFirstGrid_eq (.app hf ha) hρ]
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  rw [firstGridShape_subst hB ha hA]
  rfl

end Submission.Helpers
