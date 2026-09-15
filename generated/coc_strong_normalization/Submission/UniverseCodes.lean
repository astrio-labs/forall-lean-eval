import Submission.Reducibility

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The carrier is an index, so dependent function codes remain strictly positive. -/
inductive CarrierCode : Type u → Type (u + 1) where
  | atom {α : Type u} (point : α) : CarrierCode α
  | pi {α : Type u} {β : α → Type u}
      (A : CarrierCode α) (B : ∀ x, CarrierCode (β x)) : CarrierCode (∀ x, β x)

def CarrierCode.point : {α : Type u} → CarrierCode α → α
  | _, .atom x => x
  | _, .pi _ B => fun x => (B x).point

/-- A code retains the domain and the whole dependent codomain of a function. -/
structure SemanticShape where
  Carrier : Type u
  code : CarrierCode Carrier

def SemanticShape.point (A : SemanticShape) : A.Carrier := A.code.point

def SemanticShape.unit : SemanticShape.{u} :=
  ⟨PUnit.{u + 1}, .atom PUnit.unit⟩

def SemanticShape.pi (A : SemanticShape.{u}) (B : A.Carrier → SemanticShape.{u}) :
    SemanticShape.{u} :=
  ⟨∀ x, (B x).Carrier, .pi A.code (fun x => (B x).code)⟩

/-- Values carry a structured code, rather than just an arbitrary carrier type. -/
structure SemanticValue where
  shape : SemanticShape.{u}
  data : shape.Carrier

def SemanticValue.unit : SemanticValue.{u} := ⟨.unit, PUnit.unit⟩

noncomputable def SemanticValue.cast (v : SemanticValue.{u}) (A : SemanticShape.{u}) :
    A.Carrier := by
  classical
  exact if h : v.shape = A then h ▸ v.data else A.point

@[simp] theorem SemanticValue.cast_mk (A : SemanticShape.{u}) (x : A.Carrier) :
    (SemanticValue.mk A x).cast A = x := by
  simp only [SemanticValue.cast, ↓reduceDIte]

theorem SemanticValue.mk_cast (v : SemanticValue.{u}) (h : v.shape = A) :
    SemanticValue.mk A (v.cast A) = v := by
  cases v with
  | mk B x => cases h; rw [SemanticValue.cast_mk]

noncomputable def SemanticValue.apply (f a : SemanticValue.{u}) : SemanticValue.{u} :=
  match f with
  | ⟨⟨_, .atom _⟩, _⟩ => .unit
  | ⟨⟨_, .pi A B⟩, f⟩ =>
    let x := a.cast ⟨_, A⟩
    ⟨⟨_, B x⟩, f x⟩

def SemanticValue.lambda (A : SemanticShape.{u}) (b : A.Carrier → SemanticValue.{u}) :
    SemanticValue.{u} :=
  ⟨A.pi (fun x => (b x).shape), fun x => (b x).data⟩

/-- Application uses the stored function constructor; no injectivity of function types is used. -/
theorem SemanticValue.beta (A : SemanticShape.{u}) (b : A.Carrier → SemanticValue.{u})
    (x : A.Carrier) :
    (SemanticValue.lambda A b).apply ⟨A, x⟩ = b x := by
  change b ((SemanticValue.mk A x).cast A) = b x
  exact congrArg b (SemanticValue.cast_mk A x)

theorem SemanticValue.beta_cast (A : SemanticShape.{u})
    (b : A.Carrier → SemanticValue.{u}) (a : SemanticValue.{u}) (ha : a.shape = A) :
    (SemanticValue.lambda A b).apply a = b (a.cast A) := by
  calc
    (SemanticValue.lambda A b).apply a =
        (SemanticValue.lambda A b).apply ⟨A, a.cast A⟩ :=
      congrArg (SemanticValue.apply (SemanticValue.lambda A b)) (a.mk_cast ha).symm
    _ = b (a.cast A) := SemanticValue.beta A b (a.cast A)

/-- A realized type with a code that supports dependent application. -/
structure SemanticType where
  shape : SemanticShape.{u}
  realizes : shape.Carrier → Candidate

def SemanticType.Carrier (A : SemanticType.{u}) : Type u := A.shape.Carrier

def SemanticType.point (A : SemanticType.{u}) : A.Carrier := A.shape.point

def SemanticType.value (A : SemanticType.{u}) (x : A.Carrier) : SemanticValue.{u} :=
  ⟨A.shape, x⟩

def SemanticType.toRealizedType (A : SemanticType.{u}) : RealizedType.{u} :=
  ⟨A.Carrier, A.point, A.realizes⟩

def SemanticType.proof (C : Candidate) : SemanticType.{u} :=
  ⟨.unit, fun _ => C⟩

def SemanticType.propositions : SemanticType.{u} :=
  ⟨⟨ULift.{u} Candidate, .atom ⟨Candidate.sn⟩⟩, fun _ => Candidate.sn⟩

def SemanticType.pi (A : SemanticType.{u}) (B : A.Carrier → SemanticType.{u}) :
    SemanticType.{u} where
  shape := A.shape.pi (fun x => (B x).shape)
  realizes f := Candidate.inter (fun x => (A.realizes x).arrow ((B x).realizes (f x)))

/-- Impredicative products have a proof carrier, with the full candidate intersection. -/
def SemanticType.propPi (A : SemanticType.{u}) (B : A.Carrier → Candidate) :
    SemanticType.{v} :=
  .proof (Candidate.inter (fun x => (A.realizes x).arrow (B x)))

/-- The universe of these codes is a realized type one host universe higher. -/
def SemanticType.universe : SemanticType.{u + 1} where
  shape := ⟨SemanticType.{u}, .atom (SemanticType.proof Candidate.sn)⟩
  realizes _ := Candidate.sn

theorem SemanticType.pi_apply (A : SemanticType.{u}) (B : A.Carrier → SemanticType.{u})
    {f : (A.pi B).Carrier} {x : A.Carrier}
    (hf : ((A.pi B).realizes f).contains t) (hx : (A.realizes x).contains a) :
    ((B x).realizes (f x)).contains (.app t a) :=
  (hf.2 x).2 a hx

theorem SemanticType.pi_lambda (A : SemanticType.{u}) (B : A.Carrier → SemanticType.{u})
    (f : (A.pi B).Carrier) (hD : SN D)
    (hb : ∀ x a, (A.realizes x).contains a →
      ((B x).realizes (f x)).contains (subst 0 a b)) :
    ((A.pi B).realizes f).contains (.lam D b) := by
  have h (x : A.Carrier) :=
    Candidate.lambda (A.realizes x) ((B x).realizes (f x)) hD (hb x)
  exact ⟨(h A.point).1, h⟩

theorem SemanticType.pi_value_apply (A : SemanticType.{u})
    (B : A.Carrier → SemanticType.{u}) (f : (A.pi B).Carrier) (x : A.Carrier) :
    ((A.pi B).value f).apply (A.value x) = (B x).value (f x) := by
  change (B ((A.value x).cast A.shape)).value (f ((A.value x).cast A.shape)) =
    (B x).value (f x)
  exact congrArg (fun y => (B y).value (f y)) (SemanticValue.cast_mk A.shape x)

theorem SemanticType.propPi_apply (A : SemanticType.{u}) (B : A.Carrier → Candidate)
    {p : (A.propPi B).Carrier} {x : A.Carrier}
    (hf : ((A.propPi B).realizes p).contains t) (hx : (A.realizes x).contains a) :
    (B x).contains (.app t a) :=
  (hf.2 x).2 a hx

theorem SemanticType.propPi_lambda (A : SemanticType.{u}) (B : A.Carrier → Candidate)
    (hD : SN D) (hb : ∀ x a, (A.realizes x).contains a →
      (B x).contains (subst 0 a b)) :
    ((A.propPi B).realizes PUnit.unit).contains (.lam D b) := by
  have h (x : A.Carrier) := Candidate.lambda (A.realizes x) (B x) hD (hb x)
  exact ⟨(h A.point).1, h⟩

end Submission.Helpers
