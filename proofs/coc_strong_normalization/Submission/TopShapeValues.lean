import Submission.TopArity

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Highest-level values whose base objects are arities for the next level. -/
def Arity.ShapeEl : Arity → Type
  | .unit => Unit
  | .prop => Arity
  | .fn A B => A.ShapeEl → B.ShapeEl

def Arity.shapePoint : (A : Arity) → A.ShapeEl
  | .unit => ()
  | .prop => .unit
  | .fn _ B => fun _ => B.shapePoint

structure ShapeValue where
  code : Arity
  data : code.ShapeEl

def ShapeValue.unit : ShapeValue := ⟨.unit, ()⟩

def ShapeValue.base (A : Arity) : ShapeValue := ⟨.prop, A⟩

def ShapeValue.cast (v : ShapeValue) (A : Arity) : A.ShapeEl :=
  if h : v.code = A then h ▸ v.data else A.shapePoint

@[simp] theorem ShapeValue.cast_mk (A : Arity) (x : A.ShapeEl) :
    (ShapeValue.mk A x).cast A = x := by simp only [ShapeValue.cast, ↓reduceDIte]

theorem ShapeValue.mk_cast (v : ShapeValue) (h : v.code = A) :
    ShapeValue.mk A (v.cast A) = v := by
  cases v with
  | mk B x => cases h; rw [ShapeValue.cast_mk]

theorem ShapeValue.eq_unit (v : ShapeValue) (h : v.code = .unit) : v = .unit := by
  cases v with
  | mk A x => cases h; cases x; rfl

def ShapeValue.asArity (v : ShapeValue) : Arity :=
  match v with
  | ⟨.prop, A⟩ => A
  | _ => .unit

def ShapeValue.apply (f a : ShapeValue) : ShapeValue :=
  match f with
  | ⟨.fn A B, f⟩ => ⟨B, f (a.cast A)⟩
  | _ => .unit

@[simp] theorem ShapeValue.apply_code (f a : ShapeValue) :
    (f.apply a).code = f.code.codomain := by
  cases f with
  | mk A f => cases A <;> rfl

def ShapeValue.lambda (A B : Arity) (f : ShapeValue → ShapeValue) : ShapeValue :=
  match B with
  | .unit => .unit
  | .prop => ⟨.fn A .prop, fun x => (f ⟨A, x⟩).cast .prop⟩
  | .fn C D => ⟨.fn A (.fn C D), fun x => (f ⟨A, x⟩).cast (.fn C D)⟩

@[simp] theorem ShapeValue.lambda_code (A B : Arity) (f : ShapeValue → ShapeValue) :
    (ShapeValue.lambda A B f).code = A.arrow B := by cases B <;> rfl

theorem ShapeValue.lambda_apply (A B : Arity) (f : ShapeValue → ShapeValue)
    (x : ShapeValue) (hx : x.code = A) (hf : (f x).code = B) :
    (ShapeValue.lambda A B f).apply x = f x := by
  have hex := x.mk_cast hx
  cases B with
  | unit => exact (ShapeValue.eq_unit (f x) hf).symm
  | prop => simpa only [ShapeValue.lambda, ShapeValue.apply, hex] using (f x).mk_cast hf
  | fn C D => simpa only [ShapeValue.lambda, ShapeValue.apply, hex] using (f x).mk_cast hf

theorem ShapeValue.lambda_congr (A B : Arity) (f g : ShapeValue → ShapeValue)
    (h : ∀ x, x.code = A → f x = g x) :
    ShapeValue.lambda A B f = ShapeValue.lambda A B g := by
  cases B with
  | unit => rfl
  | prop =>
    simp only [ShapeValue.lambda]
    congr 1
    funext x
    rw [h ⟨A, x⟩ rfl]
  | fn C D =>
    simp only [ShapeValue.lambda]
    congr 1
    funext x
    rw [h ⟨A, x⟩ rfl]

/-- A top sort cannot be the type of an applicable or abstracted term. -/
theorem BoundedTyping.below_top_kind (h : BoundedTyping n Γ t (.srt s))
    (hq : sortRank q + 1 = n) (hs : sortRank s < n) : arityAt q t = .unit := by
  apply (arityAt_unit_iff _ _).2
  by_cases hk : kindAt q t = true
  · obtain ⟨s', he, hs'⟩ := h.kindAt_top hq hk
    have he' := Tm.srt.inj he
    subst s'
    omega
  · cases he : kindAt q t <;> simp_all

theorem rule_predicative_domain (hr : Rl s₁ s₂ (.type i)) :
    sortRank s₁ ≤ sortRank (.type i) := by
  cases hr with
  | type a b => simp only [sortRank]; omega
  | propType i => simp only [sortRank]; omega

theorem rule_predicative_codomain (hr : Rl s₁ s₂ (.type i)) :
    sortRank s₂ ≤ sortRank (.type i) := by
  cases hr with
  | type a b => simp only [sortRank]; omega
  | propType i => exact Nat.le_refl _

theorem BoundedTyping.top_pi_domain_unit
    (h : BoundedTyping n Γ (.pi A B) (.srt (.type i)))
    (hq : sortRank (.type i) + 1 = n) : arityAt (.type i) A = .unit := by
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
  have he := conv_srt_inj hc
  subst s₃
  apply hA.below_top_kind hq
  have hd := rule_predicative_domain hr
  omega

end Submission.Helpers
