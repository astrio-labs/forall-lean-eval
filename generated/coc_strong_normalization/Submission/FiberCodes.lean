import Submission.ArityCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Codes for the lower semantic data, indexed only by values of the preceding layer. -/
inductive FiberCode where
  | small : Arity → FiberCode
  | fn : FiberCode → FiberCode → FiberCode
  | quant (A : Arity) : (A.ShapeEl → FiberCode) → FiberCode

def FiberCode.El : FiberCode → Type
  | .small A => A.El
  | .fn A B => A.El → B.El
  | .quant A B => ∀ x : A.ShapeEl, (B x).El

def FiberCode.point : (A : FiberCode) → A.El
  | .small A => A.point
  | .fn _ B => fun _ => B.point
  | .quant _ B => fun x => (B x).point

/-- Products retain the finite arity representation when both carriers are small. -/
def FiberCode.arrow (A B : FiberCode) : FiberCode :=
  match B with
  | .small .unit => .small .unit
  | .small b => match A with
      | .small a => .small (a.arrow b)
      | _ => .fn A B
  | _ => .fn A B

def FiberCode.arrowApply (A B : FiberCode) (f : (A.arrow B).El) (x : A.El) : B.El :=
  match B with
  | .small b => match b with
      | .unit => ()
      | .prop => match A with
          | .small _ => f x
          | .fn _ _ => f x
          | .quant _ _ => f x
      | .fn _ _ => match A with
          | .small _ => f x
          | .fn _ _ => f x
          | .quant _ _ => f x
  | .fn _ _ => f x
  | .quant _ _ => f x

def FiberCode.arrowLambda (A B : FiberCode) (f : A.El → B.El) : (A.arrow B).El :=
  match B with
  | .small b => match b with
      | .unit => ()
      | .prop => match A with
          | .small _ => f
          | .fn _ _ => f
          | .quant _ _ => f
      | .fn _ _ => match A with
          | .small _ => f
          | .fn _ _ => f
          | .quant _ _ => f
  | .fn _ _ => f
  | .quant _ _ => f

theorem FiberCode.arrowBeta (A B : FiberCode) (f : A.El → B.El) (x : A.El) :
    A.arrowApply B (A.arrowLambda B f) x = f x := by
  cases B with
  | small b =>
    cases b with
    | unit =>
      change (Unit.unit : Unit) = f x
      exact Subsingleton.elim _ _
    | prop => cases A <;> rfl
    | fn C D => cases A <;> rfl
  | fn => rfl
  | quant => rfl

@[simp] theorem FiberCode.arrow_small (a b : Arity) :
    (FiberCode.small a).arrow (.small b) = .small (a.arrow b) := by
  cases b <;> rfl

@[simp] theorem FiberCode.arrow_unit (A : FiberCode) :
    A.arrow (.small .unit) = .small .unit := rfl

/-- Quantification over the singleton upper carrier needs no extra function layer. -/
noncomputable def FiberCode.all (A : Arity) (B : A.ShapeEl → FiberCode) : FiberCode := by
  classical
  exact if ∀ x, B x = .small .unit then .small .unit else
    match A with
    | .unit => B ()
    | .prop => .quant .prop B
    | .fn a b => .quant (.fn a b) B

theorem FiberCode.all_unit (B : Arity.unit.ShapeEl → FiberCode) :
    FiberCode.all .unit B = B () := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · simp only [FiberCode.all, if_pos h]
    exact (h ()).symm
  · simp only [FiberCode.all, if_neg h]

theorem FiberCode.all_trivial (A : Arity) (B : A.ShapeEl → FiberCode)
    (h : ∀ x, B x = .small .unit) : FiberCode.all A B = .small .unit := by
  classical
  simp only [FiberCode.all, if_pos h]

noncomputable def FiberCode.allApply (A : Arity) (B : A.ShapeEl → FiberCode)
    (f : (FiberCode.all A B).El) (x : A.ShapeEl) : (B x).El := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · exact (h x).symm ▸ (Unit.unit : FiberCode.El (.small .unit))
  · unfold FiberCode.all at f
    rw [if_neg h] at f
    cases A with
    | unit => cases x; exact f
    | prop => exact f x
    | fn a b => exact f x

noncomputable def FiberCode.allLambda (A : Arity) (B : A.ShapeEl → FiberCode)
    (f : ∀ x : A.ShapeEl, (B x).El) : (FiberCode.all A B).El := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · rw [FiberCode.all_trivial A B h]
    exact ()
  · unfold FiberCode.all
    rw [if_neg h]
    cases A with
    | unit => exact f ()
    | prop => exact f
    | fn a b => exact f

theorem fiber_cast_cancel {α β : Sort u} (h : α = β) (h' : β = α) (x : α) :
    cast h' (cast h x) = x := by cases h; rfl

theorem FiberCode.allBeta (A : Arity) (B : A.ShapeEl → FiberCode)
    (f : ∀ x : A.ShapeEl, (B x).El) (x : A.ShapeEl) :
    FiberCode.allApply A B (FiberCode.allLambda A B f) x = f x := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · have hs : Subsingleton (B x).El := by
      rw [h x]
      change Subsingleton Unit
      infer_instance
    exact hs.elim _ _
  · cases A with
    | unit => cases x; simp [FiberCode.allApply, FiberCode.allLambda, FiberCode.all, h]
    | prop =>
      simp [FiberCode.allApply, FiberCode.allLambda, FiberCode.all, h]
      exact congrFun (fiber_cast_cancel _ _ f) x
    | fn a b =>
      simp [FiberCode.allApply, FiberCode.allLambda, FiberCode.all, h]
      exact congrFun (fiber_cast_cancel _ _ f) x

noncomputable def FiberCode.pi (A : Arity) (D B : A.ShapeEl → FiberCode) : FiberCode :=
  FiberCode.all A (fun x => (D x).arrow (B x))

noncomputable def FiberCode.piApply (A : Arity) (D B : A.ShapeEl → FiberCode)
    (f : (FiberCode.pi A D B).El) (x : A.ShapeEl) (a : (D x).El) : (B x).El :=
  (D x).arrowApply (B x) (FiberCode.allApply A _ f x) a

noncomputable def FiberCode.piLambda (A : Arity) (D B : A.ShapeEl → FiberCode)
    (f : ∀ x : A.ShapeEl, (D x).El → (B x).El) : (FiberCode.pi A D B).El :=
  FiberCode.allLambda A _ (fun x => (D x).arrowLambda (B x) (f x))

theorem FiberCode.piBeta (A : Arity) (D B : A.ShapeEl → FiberCode)
    (f : ∀ x : A.ShapeEl, (D x).El → (B x).El) (x : A.ShapeEl) (a : (D x).El) :
    FiberCode.piApply A D B (FiberCode.piLambda A D B f) x a = f x a := by
  unfold FiberCode.piApply FiberCode.piLambda
  rw [FiberCode.allBeta, FiberCode.arrowBeta]

theorem FiberCode.pi_small (a b : Arity) :
    FiberCode.pi .unit (fun _ => .small a) (fun _ => .small b) = .small (a.arrow b) := by
  unfold FiberCode.pi
  rw [FiberCode.all_unit, FiberCode.arrow_small]

theorem FiberCode.pi_trivial (A : Arity) (D : A.ShapeEl → FiberCode) :
    FiberCode.pi A D (fun _ => .small .unit) = .small .unit := by
  apply FiberCode.all_trivial
  intro x
  rfl

end Submission.Helpers
