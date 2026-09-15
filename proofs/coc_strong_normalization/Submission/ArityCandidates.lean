import Submission.TopShapeSoundness
import Submission.DependentCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Function values use the singleton carrier when their codomain is a singleton. -/
def Arity.arrowApply (A B : Arity) (f : (A.arrow B).El) (x : A.El) : B.El :=
  match B with
  | .unit => ()
  | .prop => f x
  | .fn _ _ => f x

def Arity.arrowLambda (A B : Arity) (f : A.El → B.El) : (A.arrow B).El :=
  match B with
  | .unit => ()
  | .prop => f
  | .fn _ _ => f

@[simp] theorem Arity.arrowBeta (A B : Arity) (f : A.El → B.El) (x : A.El) :
    A.arrowApply B (A.arrowLambda B f) x = f x := by
  cases B with
  | unit =>
    change (Unit.unit : Unit) = f x
    exact Subsingleton.elim _ _
  | prop => rfl
  | fn => rfl

/-- Small semantic types have a finite carrier arity and arbitrary realizability predicates. -/
structure ArityType where
  code : Arity
  realizes : code.El → Candidate

abbrev ArityType.Carrier (A : ArityType) : Type := A.code.El

def ArityType.point (A : ArityType) : A.Carrier := A.code.point

def ArityType.toRealizedType (A : ArityType) : RealizedType.{0} :=
  ⟨A.Carrier, A.point, A.realizes⟩

def ArityType.proof (C : Candidate) : ArityType := ⟨.unit, fun _ => C⟩

def ArityType.propositions : ArityType := ⟨.prop, fun _ => Candidate.sn⟩

def ArityType.value (A : ArityType) (x : A.Carrier) : Value := ⟨A.code, x⟩

/-- Predicative products with a fixed codomain shape stay in the same small universe. -/
def ArityType.pi (A : ArityType) (b : Arity)
    (B : A.Carrier → b.El → Candidate) : ArityType where
  code := A.code.arrow b
  realizes f := Candidate.inter (fun x : A.Carrier =>
    (A.realizes x).arrow (B x (A.code.arrowApply b f x)))

theorem ArityType.pi_apply (A : ArityType) (b : Arity)
    (B : A.Carrier → b.El → Candidate) {f : (A.pi b B).Carrier} {x : A.Carrier}
    (hf : ((A.pi b B).realizes f).contains t) (hx : (A.realizes x).contains a) :
    (B x (A.code.arrowApply b f x)).contains (.app t a) :=
  (hf.2 x).2 a hx

theorem ArityType.pi_lambda (A : ArityType) (b : Arity)
    (B : A.Carrier → b.El → Candidate) (f : A.Carrier → b.El) (hD : SN D)
    (hb : ∀ x a, (A.realizes x).contains a → (B x (f x)).contains (subst 0 a body)) :
    ((A.pi b B).realizes (A.code.arrowLambda b f)).contains (.lam D body) := by
  have h (x : A.Carrier) :
      ((A.realizes x).arrow (B x (A.code.arrowApply b (A.code.arrowLambda b f) x))).contains
        (.lam D body) := by
    rw [Arity.arrowBeta]
    exact Candidate.lambda _ _ hD (hb x)
  exact ⟨(h A.point).1, h⟩

def ArityType.realizeAt (A : ArityType) (b : Arity) (he : A.code = b) : b.El → Candidate :=
  fun x => A.realizes (he.symm ▸ x)

@[simp] theorem ArityType.realizeAt_self (A : ArityType) :
    A.realizeAt A.code rfl = A.realizes := rfl

/-- Families may vary in their candidates while retaining the shape proved by `shapeEval`. -/
def ArityType.familyPi (A : ArityType) (B : A.Carrier → ArityType)
    (b : Arity) (hb : ∀ x, (B x).code = b) : ArityType :=
  A.pi b (fun x => (B x).realizeAt b (hb x))

theorem ArityType.familyPi_code (A : ArityType) (B : A.Carrier → ArityType)
    (b : Arity) (hb : ∀ x, (B x).code = b) :
    (A.familyPi B b hb).code = A.code.arrow b := rfl

/-- The class of these small types itself fits in Lean's first data universe. -/
def ArityType.universe : RealizedType.{0} where
  Carrier := ArityType
  point := .proof Candidate.sn
  realizes _ := Candidate.sn

/-- Propositional products can quantify over semantic domains of any size. -/
def ArityType.propPi (A : RealizedType.{u}) (B : A.Carrier → Candidate) : ArityType :=
  .proof (Candidate.inter (fun x => (A.realizes x).arrow (B x)))

theorem ArityType.propPi_apply (A : RealizedType.{u}) (B : A.Carrier → Candidate)
    {x : A.Carrier} (hf : ((ArityType.propPi A B).realizes ()).contains f)
    (hx : (A.realizes x).contains a) : (B x).contains (.app f a) :=
  (hf.2 x).2 a hx

theorem ArityType.propPi_lambda (A : RealizedType.{u}) (B : A.Carrier → Candidate)
    (hD : SN D)
    (hb : ∀ x a, (A.realizes x).contains a → (B x).contains (subst 0 a body)) :
    ((ArityType.propPi A B).realizes ()).contains (.lam D body) := by
  have h (x : A.Carrier) := Candidate.lambda (A.realizes x) (B x) hD (hb x)
  exact ⟨(h A.point).1, h⟩

theorem ArityType.pi_value_apply (A : ArityType) (b : Arity)
    (B : A.Carrier → b.El → Candidate) (f : (A.pi b B).Carrier) (x : A.Carrier) :
    ((A.pi b B).value f).apply (A.value x) =
      ⟨b, A.code.arrowApply b f x⟩ := by
  cases b with
  | unit => rfl
  | prop =>
    change Value.mk .prop (f ((Value.mk A.code x).cast A.code)) = _
    rw [Value.cast_mk]
    rfl
  | fn C D =>
    change Value.mk (.fn C D) (f ((Value.mk A.code x).cast A.code)) = _
    rw [Value.cast_mk]
    rfl

/-- The upper interpretation of a small type remembers precisely its carrier arity. -/
def ArityType.shape (A : ArityType) : ShapeValue := .base A.code

@[simp] theorem ArityType.pi_shape (A : ArityType) (b : Arity)
    (B : A.Carrier → b.El → Candidate) :
    (A.pi b B).shape = .base (A.code.arrow b) := rfl

end Submission.Helpers
