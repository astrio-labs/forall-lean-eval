import Submission.FiberCodes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

structure FiberValue where
  code : FiberCode
  data : code.El

noncomputable def FiberValue.cast (v : FiberValue) (A : FiberCode) : A.El := by
  classical
  exact if h : v.code = A then h ▸ v.data else A.point

@[simp] theorem FiberValue.cast_mk (A : FiberCode) (x : A.El) :
    (FiberValue.mk A x).cast A = x := by simp only [FiberValue.cast, ↓reduceDIte]

theorem FiberValue.mk_cast (v : FiberValue) (h : v.code = A) :
    FiberValue.mk A (v.cast A) = v := by
  cases v with
  | mk B x => cases h; rw [FiberValue.cast_mk]

def FiberValue.unit : FiberValue := ⟨.small .unit, ()⟩

def FiberValue.small (v : Value) : FiberValue := ⟨.small v.code, v.data⟩

noncomputable def FiberValue.piApply (A : Arity) (D B : A.ShapeEl → FiberCode)
    (f : FiberValue) (x : A.ShapeEl) (a : FiberValue) : FiberValue :=
  ⟨B x, FiberCode.piApply A D B (f.cast (.pi A D B)) x (a.cast (D x))⟩

noncomputable def FiberValue.piLambda (A : Arity) (D B : A.ShapeEl → FiberCode)
    (f : A.ShapeEl → FiberValue → FiberValue) : FiberValue :=
  ⟨.pi A D B, FiberCode.piLambda A D B
    (fun x a => (f x ⟨D x, a⟩).cast (B x))⟩

theorem FiberValue.piBeta (A : Arity) (D B : A.ShapeEl → FiberCode)
    (f : A.ShapeEl → FiberValue → FiberValue) (x : A.ShapeEl) (a : FiberValue)
    (ha : a.code = D x) (hf : (f x a).code = B x) :
    FiberValue.piApply A D B (FiberValue.piLambda A D B f) x a = f x a := by
  unfold FiberValue.piApply FiberValue.piLambda
  rw [FiberValue.cast_mk, FiberCode.piBeta, a.mk_cast ha]
  exact (f x a).mk_cast hf

theorem FiberValue.piLambda_congr (A : Arity) (D B : A.ShapeEl → FiberCode)
    (f g : A.ShapeEl → FiberValue → FiberValue)
    (h : ∀ x a, a.code = D x → f x a = g x a) :
    FiberValue.piLambda A D B f = FiberValue.piLambda A D B g := by
  unfold FiberValue.piLambda
  congr 2
  funext x a
  rw [h x ⟨D x, a⟩ rfl]

/-- Candidate families over the lower carriers determined by an upper shape. -/
structure FiberType where
  code : FiberCode
  realizes : code.El → Candidate

abbrev FiberType.Carrier (A : FiberType) : Type := A.code.El

def FiberType.point (A : FiberType) : A.Carrier := A.code.point

def FiberType.value (A : FiberType) (x : A.Carrier) : FiberValue := ⟨A.code, x⟩

def FiberType.toRealizedType (A : FiberType) : RealizedType.{0} :=
  ⟨A.Carrier, A.point, A.realizes⟩

def ArityType.toFiberType (A : ArityType) : FiberType := ⟨.small A.code, A.realizes⟩

def FiberType.proof (C : Candidate) : FiberType := (.proof C : ArityType).toFiberType

/-- Each upper value selects a domain and a codomain carrier for the lower data. -/
noncomputable def FiberType.pi (A : Arity) (D : A.ShapeEl → FiberType)
    (b : A.ShapeEl → FiberCode)
    (B : ∀ x : A.ShapeEl, (D x).Carrier → (b x).El → Candidate) : FiberType where
  code := FiberCode.pi A (fun x => (D x).code) b
  realizes f := Candidate.inter (fun z : (x : A.ShapeEl) × (D x).Carrier =>
    ((D z.1).realizes z.2).arrow
      (B z.1 z.2 (FiberCode.piApply A (fun x => (D x).code) b f z.1 z.2)))

theorem FiberType.pi_apply (A : Arity) (D : A.ShapeEl → FiberType)
    (b : A.ShapeEl → FiberCode)
    (B : ∀ x : A.ShapeEl, (D x).Carrier → (b x).El → Candidate)
    {f : (FiberType.pi A D b B).Carrier} {x : A.ShapeEl} {y : (D x).Carrier}
    (hf : ((FiberType.pi A D b B).realizes f).contains t)
    (ha : ((D x).realizes y).contains a) :
    (B x y (FiberCode.piApply A (fun x => (D x).code) b f x y)).contains (.app t a) :=
  (hf.2 ⟨x, y⟩).2 a ha

theorem FiberType.pi_lambda (A : Arity) (D : A.ShapeEl → FiberType)
    (b : A.ShapeEl → FiberCode)
    (B : ∀ x : A.ShapeEl, (D x).Carrier → (b x).El → Candidate)
    (f : ∀ x : A.ShapeEl, (D x).Carrier → (b x).El) (hC : SN C)
    (hb : ∀ x y a, ((D x).realizes y).contains a →
      (B x y (f x y)).contains (subst 0 a body)) :
    ((FiberType.pi A D b B).realizes
      (FiberCode.piLambda A (fun x => (D x).code) b f)).contains (.lam C body) := by
  have h (z : (x : A.ShapeEl) × (D x).Carrier) :
      (((D z.1).realizes z.2).arrow
        (B z.1 z.2 (FiberCode.piApply A (fun x => (D x).code) b
          (FiberCode.piLambda A (fun x => (D x).code) b f) z.1 z.2))).contains (.lam C body) := by
    rw [FiberCode.piBeta]
    exact Candidate.lambda _ _ hC (hb z.1 z.2)
  exact ⟨(h ⟨A.shapePoint, (D A.shapePoint).point⟩).1, h⟩

theorem FiberType.pi_value_apply (A : Arity) (D : A.ShapeEl → FiberType)
    (b : A.ShapeEl → FiberCode)
    (B : ∀ x : A.ShapeEl, (D x).Carrier → (b x).El → Candidate)
    (f : (FiberType.pi A D b B).Carrier) (x : A.ShapeEl) (y : (D x).Carrier) :
    FiberValue.piApply A (fun x => (D x).code) b
      ((FiberType.pi A D b B).value f) x ((D x).value y) =
        ⟨b x, FiberCode.piApply A (fun x => (D x).code) b f x y⟩ := by
  change (FiberCode.pi A (fun x => (D x).code) b).El at f
  unfold FiberValue.piApply FiberType.value
  change FiberValue.mk (b x) (FiberCode.piApply A (fun x => (D x).code) b
    ((FiberValue.mk (FiberCode.pi A (fun x => (D x).code) b) f).cast
      (FiberCode.pi A (fun x => (D x).code) b)) x
    ((FiberValue.mk (D x).code y).cast (D x).code)) = _
  rw [FiberValue.cast_mk, FiberValue.cast_mk]

/-- This next collection of coded types also remains a small semantic carrier. -/
def FiberType.universe : RealizedType.{0} where
  Carrier := FiberType
  point := .proof Candidate.sn
  realizes _ := Candidate.sn

end Submission.Helpers
