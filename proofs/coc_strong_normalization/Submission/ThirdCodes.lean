import Submission.MiddleOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Bottom carriers may depend on the preceding middle data. The old fiber
codes remain identifiable, which is needed to encode types in `Type 1`. -/
inductive ThirdCode where
  | small : FiberCode → ThirdCode
  | fn : ThirdCode → ThirdCode → ThirdCode
  | quant (A : MiddleCode) : (A.El → ThirdCode) → ThirdCode

def ThirdCode.El : ThirdCode → Type
  | .small A => A.El
  | .fn A B => A.El → B.El
  | .quant _ B => (x : _) → (B x).El

def ThirdCode.point : (A : ThirdCode) → A.El
  | .small A => A.point
  | .fn _ B => fun _ => B.point
  | .quant _ B => fun x => (B x).point

def ThirdCode.asFiber : ThirdCode → FiberCode
  | .small A => A
  | _ => .small .unit

def FiberCode.asArity : FiberCode → Arity
  | .small A => A
  | _ => .unit

def ThirdCode.arrow (A B : ThirdCode) : ThirdCode :=
  match B with
  | .small (.small .unit) => .small (.small .unit)
  | .small b => match A with
      | .small a => .small (a.arrow b)
      | _ => .fn A B
  | _ => .fn A B

@[simp] theorem ThirdCode.arrow_small (a b : FiberCode) :
    (ThirdCode.small a).arrow (.small b) = .small (a.arrow b) := by
  cases b with
  | small c => cases c <;> rfl
  | fn => rfl
  | quant => rfl

@[simp] theorem ThirdCode.arrow_unit (A : ThirdCode) :
    A.arrow (.small (.small .unit)) = .small (.small .unit) := rfl

/-- Quantification over small middle carriers and small output fibers stays
in `FiberCode`; unrestricted middle carriers use the new quantifier. -/
noncomputable def ThirdCode.all (A : MiddleCode) (B : A.El → ThirdCode) : ThirdCode := by
  classical
  exact if ∀ x, B x = .small (.small .unit) then .small (.small .unit) else
    match A with
    | .small .unit => B ()
    | .small a =>
      if ∀ x, B x = .small (B x).asFiber then
        .small (FiberCode.all a (fun x => (B x).asFiber))
      else .quant (.small a) B
    | A' => .quant A' B

theorem ThirdCode.all_unit (B : (MiddleCode.small .unit).El → ThirdCode) :
    ThirdCode.all (.small .unit) B = B () := by
  classical
  by_cases h : ∀ x, B x = .small (.small .unit)
  · simp only [ThirdCode.all, if_pos h]
    exact (h ()).symm
  · simp only [ThirdCode.all, if_neg h]

theorem ThirdCode.all_trivial (A : MiddleCode) (B : A.El → ThirdCode)
    (h : ∀ x, B x = .small (.small .unit)) :
    ThirdCode.all A B = .small (.small .unit) := by
  classical
  simp only [ThirdCode.all, if_pos h]

theorem ThirdCode.all_small (a : Arity) (B : a.ShapeEl → FiberCode) :
    ThirdCode.all (.small a) (fun x => .small (B x)) = .small (FiberCode.all a B) := by
  classical
  by_cases h : ∀ x, B x = .small .unit
  · rw [ThirdCode.all_trivial (.small a) (fun x => .small (B x)) (fun x => congrArg ThirdCode.small (h x)),
      FiberCode.all_trivial a B h]
  · have h' : ¬ ∀ x, ThirdCode.small (B x) = .small (.small .unit) := by
      intro he
      exact h (fun x => ThirdCode.small.inj (he x))
    cases a with
    | unit => rw [ThirdCode.all_unit, FiberCode.all_unit]
    | prop => simp only [ThirdCode.all, MiddleCode.El, if_neg h', ThirdCode.asFiber, implies_true, ↓reduceIte]
    | fn a b => simp only [ThirdCode.all, MiddleCode.El, if_neg h', ThirdCode.asFiber, implies_true, ↓reduceIte]

def ThirdCode.IsFiber (C : ThirdCode) : Prop := ∃ A, C = .small A

def ThirdCode.IsArity (C : ThirdCode) : Prop := ∃ A, C = .small (.small A)

theorem ThirdCode.IsArity.fiber {C : ThirdCode} (h : C.IsArity) : C.IsFiber := by
  obtain ⟨A, rfl⟩ := h
  exact ⟨.small A, rfl⟩

theorem ThirdCode.arrow_isFiber {A B : ThirdCode} (hA : A.IsFiber) (hB : B.IsFiber) :
    (A.arrow B).IsFiber := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  exact ⟨a.arrow b, ThirdCode.arrow_small a b⟩

theorem ThirdCode.arrow_isArity {A B : ThirdCode} (hA : A.IsArity) (hB : B.IsArity) :
    (A.arrow B).IsArity := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  exact ⟨a.arrow b, (ThirdCode.arrow_small _ _).trans (congrArg ThirdCode.small (FiberCode.arrow_small a b))⟩

theorem ThirdCode.all_isFiber (a : Arity) (B : (MiddleCode.small a).El → ThirdCode)
    (h : ∀ x, (B x).IsFiber) : (ThirdCode.all (.small a) B).IsFiber := by
  classical
  let C := fun x => Classical.choose (h x)
  have he : B = fun x => .small (C x) := funext (fun x => Classical.choose_spec (h x))
  rw [he, ThirdCode.all_small a C]
  exact ⟨_, rfl⟩

def ThirdCode.AtSort : Srt → ThirdCode → Prop
  | .prop, C => C = .small (.small .unit)
  | .type 0, C => C.IsArity
  | .type 1, C => C.IsFiber
  | _, _ => True

theorem ThirdCode.AtSort.arity (h : AtSort s C) (hs : sortRank s ≤ 1) : C.IsArity := by
  cases s with
  | prop => exact ⟨.unit, h⟩
  | type i =>
    have hi : i = 0 := by simp only [sortRank] at hs; omega
    subst i
    exact h

theorem ThirdCode.AtSort.fiber (h : AtSort s C) (hs : sortRank s ≤ 2) : C.IsFiber := by
  cases s with
  | prop => exact ⟨.small .unit, h⟩
  | type i =>
    cases i with
    | zero => exact ThirdCode.IsArity.fiber h
    | succ j =>
      have hj : j = 0 := by simp only [sortRank] at hs; omega
      subst j
      exact h

end Submission.Helpers
