import Submission.TwoSortArity

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A semantic value retains its finite arity. -/
structure Value where
  code : Arity
  data : code.El

def Value.unit : Value := ⟨.unit, ()⟩

def Value.cast (v : Value) (A : Arity) : A.El :=
  if h : v.code = A then h ▸ v.data else A.point

@[simp] theorem Value.cast_mk (A : Arity) (x : A.El) : (Value.mk A x).cast A = x := by
  simp only [Value.cast, ↓reduceDIte]

theorem Value.mk_cast (v : Value) (h : v.code = A) : Value.mk A (v.cast A) = v := by
  cases v with
  | mk B x => cases h; rw [Value.cast_mk]

theorem Value.eq_unit (v : Value) (h : v.code = .unit) : v = .unit := by
  cases v with
  | mk A x => cases h; cases x; rfl

def Value.asCandidate (v : Value) : Candidate :=
  match v with
  | ⟨.prop, C⟩ => C
  | _ => Candidate.sn

def Value.apply (f x : Value) : Value :=
  match f with
  | ⟨.fn A B, f⟩ => ⟨B, f (x.cast A)⟩
  | _ => .unit

@[simp] theorem Value.apply_code (f x : Value) : (f.apply x).code = f.code.codomain := by
  cases f with
  | mk A f => cases A <;> rfl

def Value.lambda (A B : Arity) (f : Value → Value) : Value :=
  match B with
  | .unit => .unit
  | .prop => ⟨.fn A .prop, fun x => (f ⟨A, x⟩).cast .prop⟩
  | .fn C D => ⟨.fn A (.fn C D), fun x => (f ⟨A, x⟩).cast (.fn C D)⟩

@[simp] theorem Value.lambda_code (A B : Arity) (f : Value → Value) :
    (Value.lambda A B f).code = A.arrow B := by
  cases B <;> rfl

theorem Value.lambda_apply (A B : Arity) (f : Value → Value) (x : Value)
    (hx : x.code = A) (hf : (f x).code = B) : (Value.lambda A B f).apply x = f x := by
  have hex := x.mk_cast hx
  cases B with
  | unit => exact (Value.eq_unit (f x) hf).symm
  | prop => simpa only [Value.lambda, Value.apply, hex] using (f x).mk_cast hf
  | fn C D => simpa only [Value.lambda, Value.apply, hex] using (f x).mk_cast hf

theorem Value.lambda_congr (A B : Arity) (f g : Value → Value)
    (h : ∀ x, x.code = A → f x = g x) : Value.lambda A B f = Value.lambda A B g := by
  cases B with
  | unit => rfl
  | prop =>
    simp only [Value.lambda]
    congr 1
    funext x
    rw [h ⟨A, x⟩ rfl]
  | fn C D =>
    simp only [Value.lambda]
    congr 1
    funext x
    rw [h ⟨A, x⟩ rfl]

def valueCodes (ρ : Nat → Value) : Nat → Arity := fun i => (ρ i).code

@[simp] theorem valueCodes_push (x : Value) (ρ : Nat → Value) :
    valueCodes (push x ρ) = push x.code (valueCodes ρ) := by
  funext i
  cases i <;> rfl

def candidatePi (A : Arity) (d : Value → Candidate) (c : Value → Value → Candidate)
    (f : Value) : Candidate :=
  Candidate.inter (fun x : A.El => (d ⟨A, x⟩).arrow (c ⟨A, x⟩ (f.apply ⟨A, x⟩)))

def piSemantics (A B : Arity) (d : Value → Candidate) (c : Value → Value → Candidate) :
    Value × (Value → Candidate) :=
  if B = .unit then (⟨.prop, candidatePi A d c .unit⟩, fun _ => candidatePi A d c .unit)
  else (.unit, candidatePi A d c)

/-- Interpret a term and, simultaneously, its use as a type. -/
def semantics (ρ : Nat → Value) : Tm → Value × (Value → Candidate)
  | .var i => (ρ i, fun _ => (ρ i).asCandidate)
  | .srt _ => (Value.unit, fun _ => Candidate.sn)
  | .app f a =>
    let v := (semantics ρ f).1.apply (semantics ρ a).1
    (v, fun _ => v.asCandidate)
  | .lam A b =>
    let v := Value.lambda (arity A) (inferArity (push (arity A) (valueCodes ρ)) b)
      (fun x => (semantics (push x ρ) b).1)
    (v, fun _ => v.asCandidate)
  | .pi A B =>
    piSemantics (arity A) (arity B) (semantics ρ A).2
      (fun x => (semantics (push x ρ) B).2)

theorem semantics_code (ρ : Nat → Value) (t : Tm) :
    (semantics ρ t).1.code = inferArity (valueCodes ρ) t := by
  induction t generalizing ρ with
  | var => rfl
  | srt => rfl
  | app f a ihf iha => simp only [semantics, Value.apply_code, ihf, inferArity]
  | lam A b ihA ihb => simp only [semantics, Value.lambda_code, inferArity]
  | pi A B ihA ihB => simp only [semantics, piSemantics, inferArity]; split <;> rfl

theorem semantics_nonkind (ρ : Nat → Value) (hk : isKind t = false) :
    (semantics ρ t).2 = fun _ => (semantics ρ t).1.asCandidate := by
  cases t with
  | var => rfl
  | srt s =>
    cases s with
    | prop => cases hk
    | type => rfl
  | app => rfl
  | lam => rfl
  | pi A B =>
    have hb : arity B = .unit := (arity_unit_iff _).2 hk
    simp only [semantics, piSemantics, hb, ↓reduceIte]
    rfl

theorem semantics_ren (ρ δ : Nat → Value) (r : Nat → Nat)
    (hr : ∀ i, δ (r i) = ρ i) (t : Tm) :
    semantics δ (ren r t) = semantics ρ t := by
  induction t generalizing ρ δ r with
  | var i => simp only [ren, semantics, hr]
  | srt => rfl
  | app f a ihf iha => simp only [ren, semantics, ihf _ _ _ hr, iha _ _ _ hr]
  | lam A b ihA ihb =>
    have hup (x : Value) : ∀ i, push x δ (upRen r i) = push x ρ i := by
      intro i
      cases i with
      | zero => rfl
      | succ i => exact hr i
    have hb : (fun x => semantics (push x δ) (ren (upRen r) b)) =
        fun x => semantics (push x ρ) b := by
      funext x
      exact ihb _ _ _ (hup x)
    have hc : inferArity (push (arity A) (valueCodes δ)) (ren (upRen r) b) =
        inferArity (push (arity A) (valueCodes ρ)) b := by
      apply inferArity_ren
      intro i
      cases i with
      | zero => rfl
      | succ i => exact congrArg Value.code (hr i)
    simp only [ren, semantics, arity_ren, hc]
    have hbe (x : Value) := congrFun hb x
    simp only [hbe]
  | pi A B ihA ihB =>
    have hup (x : Value) : ∀ i, push x δ (upRen r i) = push x ρ i := by
      intro i
      cases i with
      | zero => rfl
      | succ i => exact hr i
    have hb (x : Value) := ihB (push x ρ) (push x δ) (upRen r) (hup x)
    simp only [ren, semantics, arity_ren, ihA _ _ _ hr, hb]

def semanticSub (ρ : Nat → Value) (σ : Nat → Tm) : Nat → Value :=
  fun i => (semantics ρ (σ i)).1

theorem semanticSub_up (ρ : Nat → Value) (σ : Nat → Tm) (x : Value) :
    semanticSub (push x ρ) (upSub σ) = push x (semanticSub ρ σ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    change (semantics (push x ρ) (ren Nat.succ (σ i))).1 = (semantics ρ (σ i)).1
    rw [semantics_ren ρ (push x ρ) Nat.succ (fun _ => rfl)]

theorem semantics_sub (ρ : Nat → Value) (σ : Nat → Tm)
    (hσ : ∀ i, isKind (σ i) = false) (t : Tm) :
    semantics ρ (sub σ t) = semantics (semanticSub ρ σ) t := by
  have hup {σ : Nat → Tm} (hσ : ∀ i, isKind (σ i) = false) :
      ∀ i, isKind (upSub σ i) = false := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (isKind_ren _ _).trans (hσ i)
  induction t generalizing ρ σ with
  | var i =>
    apply Prod.ext
    · rfl
    · exact semantics_nonkind ρ (hσ i)
  | srt => rfl
  | app f a ihf iha => simp only [sub, semantics, ihf _ _ hσ, iha _ _ hσ]
  | lam A b ihA ihb =>
    have hb (x : Value) : semantics (push x ρ) (sub (upSub σ) b) =
        semantics (push x (semanticSub ρ σ)) b := by
      rw [ihb _ _ (hup hσ), semanticSub_up]
    have hc : inferArity (push (arity A) (valueCodes ρ)) (sub (upSub σ) b) =
        inferArity (push (arity A) (valueCodes (semanticSub ρ σ))) b := by
      have he := congrArg (fun p => p.1.code) (hb ⟨arity A, (arity A).point⟩)
      simpa only [semantics_code, valueCodes_push] using he
    simp only [sub, semantics, arity_sub hσ, hc, hb]
  | pi A B ihA ihB =>
    have hb (x : Value) : semantics (push x ρ) (sub (upSub σ) B) =
        semantics (push x (semanticSub ρ σ)) B := by
      rw [ihB _ _ (hup hσ), semanticSub_up]
    simp only [sub, semantics, arity_sub hσ, arity_sub (hup hσ), ihA _ _ hσ, hb]

theorem semanticSub_single (ρ : Nat → Value) (a : Tm) :
    semanticSub ρ (single a) = push (semantics ρ a).1 ρ := by
  funext i
  cases i <;> rfl

theorem semantics_subst (ρ : Nat → Value) (ha : isKind a = false) (b : Tm) :
    semantics ρ (subst 0 a b) = semantics (push (semantics ρ a).1 ρ) b := by
  rw [subst_eq_sub, semantics_sub, semanticSub_single]
  intro i
  cases i with
  | zero => exact ha
  | succ => rfl

theorem semantics_beta (ρ : Nat → Value) (ha : isKind a = false)
    (hb : isKind b = false) (hc : inferArity (valueCodes ρ) a = arity A) :
    semantics ρ (.app (.lam A b) a) = semantics ρ (subst 0 a b) := by
  rw [semantics_subst ρ ha]
  have hca : (semantics ρ a).1.code = arity A := (semantics_code ρ a).trans hc
  have hcb : (semantics (push (semantics ρ a).1 ρ) b).1.code =
      inferArity (push (arity A) (valueCodes ρ)) b := by
    simp only [semantics_code, valueCodes_push, hc]
  have he := Value.lambda_apply (arity A) (inferArity (push (arity A) (valueCodes ρ)) b)
    (fun x => (semantics (push x ρ) b).1) (semantics ρ a).1 hca hcb
  apply Prod.ext
  · exact he
  · simp only [semantics]
    rw [he, semantics_nonkind _ hb]

end Submission.Helpers
