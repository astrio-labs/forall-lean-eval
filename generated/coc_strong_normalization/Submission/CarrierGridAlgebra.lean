import Submission.CarrierAlgebra

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def arityCarrierArrows : CarrierArrows arityCarrierSystem where
  terminal := ⟨inferInstanceAs (Subsingleton Unit)⟩
  code := Arity.arrow
  functions a b := ⟨Arity.arrowLambda a b, Arity.arrowApply a b, Arity.arrowBeta a b⟩
  trivial _ := rfl

def shapeCarrierArrows : CarrierArrows shapeCarrierSystem where
  terminal := ⟨inferInstanceAs (Subsingleton Unit)⟩
  code := Arity.arrow
  functions a b := by
    cases b with
    | unit => exact CarrierFunction.trivial _
    | prop => exact CarrierFunction.direct _ _
    | fn => exact CarrierFunction.direct _ _
  trivial _ := rfl

/-- Each compact arrow refers only to the preceding row and coordinate. -/
noncomputable def carrierGridArrows : (r d : Nat) → CarrierArrows (carrierGrid r d)
  | 0, _ => arityCarrierArrows
  | _ + 1, 0 => shapeCarrierArrows
  | r + 1, d + 1 => LayerCode.arrows (carrierGridArrows r d)

theorem carrierGridTerminal (r d : Nat) : CarrierTerminal (carrierGrid r d) :=
  (carrierGridArrows r d).terminal

/-- Compact dependent products fill the grid using only products in the
preceding row. The off-triangle first row uses the free construction. -/
noncomputable def carrierGridQuantifiers : (r d : Nat) →
    CarrierQuantifiers (carrierGrid (r + 1) d) (carrierGrid (r + 1) (d + 1))
  | 0, d => LayerCode.freeQuantifiers (carrierGridTerminal 1 d) (carrierGridTerminal 0 d)
  | r + 1, 0 => LayerCode.freeQuantifiers (carrierGridTerminal (r + 2) 0)
      (carrierGridTerminal (r + 1) 0)
  | r + 1, d + 1 => LayerCode.quantifiers (carrierGridQuantifiers r d)
      (carrierGridTerminal (r + 1) d) (carrierGridTerminal (r + 1) (d + 1))

theorem carrierGrid_arrow_beta (r d : Nat) (A B : (carrierGrid r d).Code)
    (f : (carrierGrid r d).El A → (carrierGrid r d).El B) (x : (carrierGrid r d).El A) :
    ((carrierGridArrows r d).functions A B).apply
      (((carrierGridArrows r d).functions A B).lambda f) x = f x :=
  ((carrierGridArrows r d).functions A B).beta f x

theorem carrierGrid_all_beta (r d : Nat) (A : (carrierGrid (r + 1) d).Code)
    (B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code)
    (f : (x : (carrierGrid (r + 1) d).El A) → (carrierGrid (r + 1) (d + 1)).El (B x))
    (x : (carrierGrid (r + 1) d).El A) :
    ((carrierGridQuantifiers r d).functions A B).apply
      (((carrierGridQuantifiers r d).functions A B).lambda f) x = f x :=
  ((carrierGridQuantifiers r d).functions A B).beta f x

theorem carrierGrid_arrow_small (r d : Nat) (A B : (carrierGrid r d).Code) :
    (carrierGridArrows (r + 1) (d + 1)).code (.small A) (.small B) =
      .small ((carrierGridArrows r d).code A B) :=
  LayerCode.compactArrow_small (carrierGridArrows r d) A B

/-- Products commute with the small embedding across every grid square. -/
theorem carrierGrid_all_small (r d : Nat) (A : (carrierGrid (r + 1) d).Code)
    (B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code) :
    (carrierGridQuantifiers (r + 1) (d + 1)).code (.small A) (fun x => .small (B x)) =
      .small ((carrierGridQuantifiers r d).code A B) :=
  LayerCode.compactAll_small (carrierGridQuantifiers r d)
    (carrierGridTerminal (r + 1) d) (carrierGridTerminal (r + 1) (d + 1)) A B

namespace CarrierQuantifiers

variable {I S : CarrierSystem}

noncomputable def pi (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code) : S.Code :=
  Q.code a (fun x => P.code (D x) (B x))

noncomputable def piLambda (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code) (f : (x : I.El a) → S.El (D x) → S.El (B x)) :
    S.El (Q.pi P a D B) :=
  (Q.functions a _).lambda (fun x => (P.functions (D x) (B x)).lambda (f x))

noncomputable def piApply (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code) (f : S.El (Q.pi P a D B))
    (x : I.El a) (y : S.El (D x)) : S.El (B x) :=
  (P.functions (D x) (B x)).apply ((Q.functions a _).apply f x) y

theorem piBeta (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code)
    (f : (x : I.El a) → S.El (D x) → S.El (B x)) (x : I.El a) (y : S.El (D x)) :
    Q.piApply P a D B (Q.piLambda P a D B f) x y = f x y := by
  unfold piApply piLambda
  rw [(Q.functions a _).beta, (P.functions (D x) (B x)).beta]

theorem pi_trivial (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code) (h : ∀ x, B x = S.defaultCode) :
    Q.pi P a D B = S.defaultCode := by
  apply Q.trivial
  intro x
  rw [h x, P.trivial]

end CarrierQuantifiers

/-- The complete one-coordinate product, including its final arrow, folds
to the lower row whenever both its domain and codomain do. -/
theorem carrierGrid_pi_small (r d : Nat) (A : (carrierGrid (r + 1) d).Code)
    (D B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code) :
    (carrierGridQuantifiers (r + 1) (d + 1)).pi (carrierGridArrows (r + 2) (d + 2))
      (.small A) (fun x => .small (D x)) (fun x => .small (B x)) =
    .small ((carrierGridQuantifiers r d).pi (carrierGridArrows (r + 1) (d + 1)) A D B) := by
  unfold CarrierQuantifiers.pi
  have he : (fun x => (carrierGridArrows (r + 2) (d + 2)).code
        (.small (D x)) (.small (B x))) =
      (fun x => LayerCode.small ((carrierGridArrows (r + 1) (d + 1)).code (D x) (B x))) :=
    funext (fun x => carrierGrid_arrow_small (r + 1) (d + 1) (D x) (B x))
  exact (congrArg ((carrierGridQuantifiers (r + 1) (d + 1)).code (.small A)) he).trans
    (carrierGrid_all_small r d A _)

end Submission.Helpers
