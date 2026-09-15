import Submission.ThirdCodes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A carrier implements dependent functions with a checked beta law. -/
structure CarrierFunction (X : Type) (Y : X → Type) (Z : Type) where
  lambda : ((x : X) → Y x) → Z
  apply : Z → (x : X) → Y x
  beta : ∀ f x, apply (lambda f) x = f x

def CarrierFunction.direct (X : Type) (Y : X → Type) :
    CarrierFunction X Y ((x : X) → Y x) := ⟨id, id, fun _ _ => rfl⟩

def CarrierFunction.trivial (X : Type) : CarrierFunction X (fun _ => Unit) Unit :=
  ⟨fun _ => (), fun _ _ => (), fun _ _ => Subsingleton.elim _ _⟩

noncomputable def ThirdCode.arrowFunctions (A B : ThirdCode) :
    CarrierFunction A.El (fun _ => B.El) (A.arrow B).El := by
  cases A with
  | small a =>
    cases B with
    | small b =>
      rw [ThirdCode.arrow_small]
      exact ⟨FiberCode.arrowLambda a b, FiberCode.arrowApply a b, FiberCode.arrowBeta a b⟩
    | fn C D => exact CarrierFunction.direct _ _
    | quant C D => exact CarrierFunction.direct _ _
  | fn C D =>
    cases B with
    | small b => cases b with
      | small b => cases b with
        | unit => exact CarrierFunction.trivial _
        | prop => exact CarrierFunction.direct _ _
        | fn E F => exact CarrierFunction.direct _ _
      | fn E F => exact CarrierFunction.direct _ _
      | quant E F => exact CarrierFunction.direct _ _
    | fn E F => exact CarrierFunction.direct _ _
    | quant E F => exact CarrierFunction.direct _ _
  | quant C D =>
    cases B with
    | small b => cases b with
      | small b => cases b with
        | unit => exact CarrierFunction.trivial _
        | prop => exact CarrierFunction.direct _ _
        | fn E F => exact CarrierFunction.direct _ _
      | fn E F => exact CarrierFunction.direct _ _
      | quant E F => exact CarrierFunction.direct _ _
    | fn E F => exact CarrierFunction.direct _ _
    | quant E F => exact CarrierFunction.direct _ _

noncomputable def ThirdCode.arrowApply (A B : ThirdCode) : (A.arrow B).El → A.El → B.El :=
  (A.arrowFunctions B).apply

noncomputable def ThirdCode.arrowLambda (A B : ThirdCode) : (A.El → B.El) → (A.arrow B).El :=
  (A.arrowFunctions B).lambda

theorem ThirdCode.arrowBeta (A B : ThirdCode) (f : A.El → B.El) (x : A.El) :
    A.arrowApply B (A.arrowLambda B f) x = f x := (A.arrowFunctions B).beta f x

noncomputable def ThirdCode.smallFunctions (a : Arity) (B : a.ShapeEl → ThirdCode)
    (h : ∀ x, B x = .small (B x).asFiber) :
    CarrierFunction a.ShapeEl (fun x => (B x).El)
      (FiberCode.all a (fun x => (B x).asFiber)).El := by
  refine ⟨fun f => FiberCode.allLambda a _
      (fun x => cast (congrArg ThirdCode.El (h x)) (f x)),
    fun f x => cast (congrArg ThirdCode.El (h x).symm) (FiberCode.allApply a _ f x), ?_⟩
  intro f x
  rw [FiberCode.allBeta]
  exact fiber_cast_cancel _ _ (f x)

noncomputable def ThirdCode.allFunctions (A : MiddleCode) (B : A.El → ThirdCode) :
    CarrierFunction A.El (fun x => (B x).El) (ThirdCode.all A B).El := by
  classical
  unfold ThirdCode.all
  split
  · rename_i h
    refine ⟨fun _ => (), fun _ x => (B x).point, ?_⟩
    intro f x
    have hsub : Subsingleton (B x).El := by
      rw [h x]
      exact inferInstanceAs (Subsingleton Unit)
    exact hsub.elim _ _
  · cases A with
    | small a =>
      cases a with
      | unit =>
        refine ⟨fun f => f (), fun f x => ?_, ?_⟩
        · cases x; exact f
        · intro f x; cases x; rfl
      | prop =>
        dsimp only
        split
        · rename_i h
          exact ThirdCode.smallFunctions .prop B h
        · exact CarrierFunction.direct _ _
      | fn a b =>
        dsimp only
        split
        · rename_i h
          exact ThirdCode.smallFunctions (.fn a b) B h
        · exact CarrierFunction.direct _ _
    | «universe» a => exact CarrierFunction.direct _ _
    | fn a b => exact CarrierFunction.direct _ _
    | quant a b => exact CarrierFunction.direct _ _

noncomputable def ThirdCode.allApply (A : MiddleCode) (B : A.El → ThirdCode) :
    (ThirdCode.all A B).El → (x : A.El) → (B x).El := (ThirdCode.allFunctions A B).apply

noncomputable def ThirdCode.allLambda (A : MiddleCode) (B : A.El → ThirdCode) :
    ((x : A.El) → (B x).El) → (ThirdCode.all A B).El := (ThirdCode.allFunctions A B).lambda

theorem ThirdCode.allBeta (A : MiddleCode) (B : A.El → ThirdCode)
    (f : (x : A.El) → (B x).El) (x : A.El) :
    ThirdCode.allApply A B (ThirdCode.allLambda A B f) x = f x :=
  (ThirdCode.allFunctions A B).beta f x

end Submission.Helpers
