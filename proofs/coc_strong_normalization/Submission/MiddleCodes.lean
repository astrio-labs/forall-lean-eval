import Submission.FiberCodes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The middle layer for bound three. Its lowest nontrivial data are arities;
at `Type 1`, a value instead specifies a lower fiber for every upper inhabitant.
These two atoms have different carriers. -/
inductive MiddleCode where
  | small : Arity → MiddleCode
  | universe : Arity → MiddleCode
  | fn : MiddleCode → MiddleCode → MiddleCode
  | quant (A : Arity) : (A.ShapeEl → MiddleCode) → MiddleCode

def MiddleCode.El : MiddleCode → Type
  | .small A => A.ShapeEl
  | .universe A => A.ShapeEl → FiberCode
  | .fn A B => A.El → B.El
  | .quant A B => (x : A.ShapeEl) → (B x).El

def MiddleCode.point : (A : MiddleCode) → A.El
  | .small A => A.shapePoint
  | .universe _ => fun _ => .small .unit
  | .fn _ B => fun _ => B.point
  | .quant _ B => fun x => (B x).point

def MiddleCode.arrow (A B : MiddleCode) : MiddleCode :=
  match B with
  | .small .unit => .small .unit
  | .small b => match A with
      | .small a => .small (a.arrow b)
      | _ => .fn A B
  | _ => .fn A B

def MiddleCode.arrowApply (A B : MiddleCode) (f : (A.arrow B).El) (x : A.El) : B.El :=
  match B with
  | .small b => match b with
      | .unit => ()
      | .prop => match A with
          | .small _ => f x
          | .universe _ => f x
          | .fn _ _ => f x
          | .quant _ _ => f x
      | .fn _ _ => match A with
          | .small _ => f x
          | .universe _ => f x
          | .fn _ _ => f x
          | .quant _ _ => f x
  | .universe _ => f x
  | .fn _ _ => f x
  | .quant _ _ => f x

def MiddleCode.arrowLambda (A B : MiddleCode) (f : A.El → B.El) : (A.arrow B).El :=
  match B with
  | .small b => match b with
      | .unit => ()
      | .prop => match A with
          | .small _ => f
          | .universe _ => f
          | .fn _ _ => f
          | .quant _ _ => f
      | .fn _ _ => match A with
          | .small _ => f
          | .universe _ => f
          | .fn _ _ => f
          | .quant _ _ => f
  | .universe _ => f
  | .fn _ _ => f
  | .quant _ _ => f

theorem MiddleCode.arrowBeta (A B : MiddleCode) (f : A.El → B.El) (x : A.El) :
    A.arrowApply B (A.arrowLambda B f) x = f x := by
  cases B with
  | small b =>
    cases b with
    | unit =>
      change (Unit.unit : Unit) = f x
      exact Subsingleton.elim _ _
    | prop => cases A <;> rfl
    | fn C D => cases A <;> rfl
  | «universe» => rfl
  | fn => rfl
  | quant => rfl

@[simp] theorem MiddleCode.arrow_small (a b : Arity) :
    (MiddleCode.small a).arrow (.small b) = .small (a.arrow b) := by cases b <;> rfl

@[simp] theorem MiddleCode.arrow_unit (A : MiddleCode) :
    A.arrow (.small .unit) = .small .unit := rfl

noncomputable def MiddleCode.all (A : Arity) (B : A.ShapeEl → MiddleCode) : MiddleCode := by
  classical
  exact if ∀ x, B x = .small .unit then .small .unit else
    match A with
    | .unit => B ()
    | .prop => .quant .prop B
    | .fn a b => .quant (.fn a b) B

theorem MiddleCode.all_unit (B : Arity.unit.ShapeEl → MiddleCode) :
    MiddleCode.all .unit B = B () := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · simp only [MiddleCode.all, if_pos h]
    exact (h ()).symm
  · simp only [MiddleCode.all, if_neg h]

theorem MiddleCode.all_trivial (A : Arity) (B : A.ShapeEl → MiddleCode)
    (h : ∀ x, B x = .small .unit) : MiddleCode.all A B = .small .unit := by
  classical
  simp only [MiddleCode.all, if_pos h]

noncomputable def MiddleCode.allApply (A : Arity) (B : A.ShapeEl → MiddleCode)
    (f : (MiddleCode.all A B).El) (x : A.ShapeEl) : (B x).El := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · exact (h x).symm ▸ (Unit.unit : MiddleCode.El (.small .unit))
  · unfold MiddleCode.all at f
    rw [if_neg h] at f
    cases A with
    | unit => cases x; exact f
    | prop => exact f x
    | fn a b => exact f x

noncomputable def MiddleCode.allLambda (A : Arity) (B : A.ShapeEl → MiddleCode)
    (f : (x : A.ShapeEl) → (B x).El) : (MiddleCode.all A B).El := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · rw [MiddleCode.all_trivial A B h]
    exact ()
  · unfold MiddleCode.all
    rw [if_neg h]
    cases A with
    | unit => exact f ()
    | prop => exact f
    | fn a b => exact f

theorem MiddleCode.allBeta (A : Arity) (B : A.ShapeEl → MiddleCode)
    (f : (x : A.ShapeEl) → (B x).El) (x : A.ShapeEl) :
    MiddleCode.allApply A B (MiddleCode.allLambda A B f) x = f x := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · have hs : Subsingleton (B x).El := by
      rw [h x]
      exact inferInstanceAs (Subsingleton Unit)
    exact hs.elim _ _
  · cases A with
    | unit => cases x; simp [MiddleCode.allApply, MiddleCode.allLambda, MiddleCode.all, h]
    | prop =>
      simp [MiddleCode.allApply, MiddleCode.allLambda, MiddleCode.all, h]
      exact congrFun (fiber_cast_cancel _ _ f) x
    | fn a b =>
      simp [MiddleCode.allApply, MiddleCode.allLambda, MiddleCode.all, h]
      exact congrFun (fiber_cast_cancel _ _ f) x

noncomputable def MiddleCode.pi (a : Arity) (D B : a.ShapeEl → MiddleCode) : MiddleCode :=
  MiddleCode.all a (fun x => (D x).arrow (B x))

noncomputable def MiddleCode.piApply (a : Arity) (D B : a.ShapeEl → MiddleCode)
    (f : (MiddleCode.pi a D B).El) (x : a.ShapeEl) (y : (D x).El) : (B x).El :=
  (D x).arrowApply (B x) (MiddleCode.allApply a _ f x) y

noncomputable def MiddleCode.piLambda (a : Arity) (D B : a.ShapeEl → MiddleCode)
    (f : (x : a.ShapeEl) → (D x).El → (B x).El) : (MiddleCode.pi a D B).El :=
  MiddleCode.allLambda a _ (fun x => (D x).arrowLambda (B x) (f x))

theorem MiddleCode.piBeta (a : Arity) (D B : a.ShapeEl → MiddleCode)
    (f : (x : a.ShapeEl) → (D x).El → (B x).El) (x : a.ShapeEl) (y : (D x).El) :
    MiddleCode.piApply a D B (MiddleCode.piLambda a D B f) x y = f x y := by
  unfold MiddleCode.piApply MiddleCode.piLambda
  rw [MiddleCode.allBeta, MiddleCode.arrowBeta]

structure MiddleValue where
  code : MiddleCode
  data : code.El

noncomputable def MiddleValue.cast (v : MiddleValue) (A : MiddleCode) : A.El := by
  classical
  exact if h : v.code = A then h ▸ v.data else A.point

@[simp] theorem MiddleValue.cast_mk (A : MiddleCode) (x : A.El) :
    (MiddleValue.mk A x).cast A = x := by simp only [MiddleValue.cast, ↓reduceDIte]

theorem MiddleValue.mk_cast (v : MiddleValue) (h : v.code = A) :
    MiddleValue.mk A (v.cast A) = v := by
  cases v with
  | mk B x => cases h; rw [MiddleValue.cast_mk]

def MiddleValue.unit : MiddleValue := ⟨.small .unit, ()⟩

noncomputable def MiddleValue.force (A : MiddleCode) (v : MiddleValue) : MiddleValue :=
  ⟨A, v.cast A⟩

theorem MiddleValue.force_eq (v : MiddleValue) (h : v.code = A) : v.force A = v :=
  v.mk_cast h

end Submission.Helpers
