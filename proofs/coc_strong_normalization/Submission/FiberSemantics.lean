import Submission.FiberProductCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def ShapeValue.force (A : Arity) (x : ShapeValue) : ShapeValue := ⟨A, x.cast A⟩

@[simp] theorem ShapeValue.force_code (A : Arity) (x : ShapeValue) :
    (x.force A).code = A := rfl

theorem ShapeValue.force_eq (x : ShapeValue) (h : x.code = A) : x.force A = x :=
  x.mk_cast h

/-- Candidate interpretation only uses the compatible part of a semantic input. -/
noncomputable def fiberCanonical (a : Arity) (D : ShapeValue → FiberCode)
    (C : ShapeValue → FiberValue → Candidate) (u : ShapeValue) (f : FiberValue) : Candidate :=
  C (u.force a) (f.force (D (u.force a)))

theorem fiberCanonical_eq (hu : u.code = a) (hf : f.code = D u) :
    fiberCanonical a D C u f = C u f := by
  unfold fiberCanonical
  rw [u.force_eq hu, f.force_eq hf]

noncomputable def fiberEncode (s : Option Srt) (k : Arity)
    (C : ShapeValue → FiberValue → Candidate) : FiberValue :=
  match s with
  | some .prop => ⟨.small .prop, C .unit .unit⟩
  | some (.type 0) => ⟨.small (.fn k .prop), fun f => C .unit ⟨.small k, f⟩⟩
  | _ => .unit

noncomputable def fiberDecode (s : Option Srt) (k : Arity) (v : FiberValue)
    (_u : ShapeValue) (f : FiberValue) : Candidate :=
  match s with
  | some .prop => v.cast (.small .prop)
  | some (.type 0) => v.cast (.small (.fn k .prop)) (f.cast (.small k))
  | _ => Candidate.sn

/-- The first two semantic layers, including the candidates for inhabitants of each type. -/
noncomputable def fiberSemantics (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → FiberValue) : Tm → FiberValue × (ShapeValue → FiberValue → Candidate)
  | .var j =>
    let v := (δ j).force (inferredFiber 2 0 Γ ρ (.var j))
    (v, fiberDecode (typeSort 2 Γ (.var j)) (nextArity 2 0 Γ ρ (.var j)) v)
  | .srt s =>
    let C : ShapeValue → FiberValue → Candidate := fun _ _ => Candidate.sn
    let v := (fiberEncode (typeSort 2 Γ (.srt s)) (nextArity 2 0 Γ ρ (.srt s)) C).force
      (inferredFiber 2 0 Γ ρ (.srt s))
    (v, C)
  | .app f a =>
    let p := chosenProduct 2 Γ f
    let v := (fiberApply (arityAt (.type 0) p.1)
      (fun x => fiberShape 2 0 Γ ρ p.1 x)
      (fun x y => fiberShape 2 0 (p.1 :: Γ) (push x ρ) p.2 y)
      (shapeEval 2 0 Γ ρ f) (fiberSemantics Γ ρ δ f).1
      (shapeEval 2 0 Γ ρ a) (fiberSemantics Γ ρ δ a).1).force
        (inferredFiber 2 0 Γ ρ (.app f a))
    (v, fiberDecode (typeSort 2 Γ (.app f a)) (nextArity 2 0 Γ ρ (.app f a)) v)
  | .lam A b =>
    let v := (fiberLambda (arityAt (.type 0) A)
      (fun x => fiberShape 2 0 Γ ρ A x)
      (fun x y => fiberShape 2 0 (A :: Γ) (push x ρ) (chosenType 2 (A :: Γ) b) y)
      (shapeEval 2 0 Γ ρ (.lam A b))
      (fun x y => (fiberSemantics (A :: Γ) (push x ρ) (push y δ) b).1)).force
        (inferredFiber 2 0 Γ ρ (.lam A b))
    (v, fun _ _ => Candidate.sn)
  | .pi A B =>
    let C := fiberCanonical (arityAt (.type 0) (.pi A B))
      (fun x => fiberShape 2 0 Γ ρ (.pi A B) x)
      (fiberCandidatePi (arityAt (.type 0) A)
        (fun x => fiberShape 2 0 Γ ρ A x)
        (fun x y => fiberShape 2 0 (A :: Γ) (push x ρ) B y)
        (fiberSemantics Γ ρ δ A).2
        (fun x y => (fiberSemantics (A :: Γ) (push x ρ) (push y δ) B).2))
    let v := (fiberEncode (typeSort 2 Γ (.pi A B)) (nextArity 2 0 Γ ρ (.pi A B)) C).force
      (inferredFiber 2 0 Γ ρ (.pi A B))
    (v, C)

theorem fiberSemantics_code (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → FiberValue) (t : Tm) :
    (fiberSemantics Γ ρ δ t).1.code = inferredFiber 2 0 Γ ρ t := by
  cases t <;> rfl

theorem fiberSemantics_typed_code (h : BoundedTyping 2 Γ t A)
    (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ t).1.code = fiberShape 2 0 Γ ρ A (shapeEval 2 0 Γ ρ t) :=
  (fiberSemantics_code Γ ρ δ t).trans (inferredFiber_eq h rfl hρ)

theorem fiberSemantics_pi (hu : u.code = arityAt (.type 0) (.pi A B))
    (hf : f.code = fiberShape 2 0 Γ ρ (.pi A B) u) :
    (fiberSemantics Γ ρ δ (.pi A B)).2 u f =
      fiberCandidatePi (arityAt (.type 0) A)
        (fun x => fiberShape 2 0 Γ ρ A x)
        (fun x y => fiberShape 2 0 (A :: Γ) (push x ρ) B y)
        (fiberSemantics Γ ρ δ A).2
        (fun x y => (fiberSemantics (A :: Γ) (push x ρ) (push y δ) B).2) u f := by
  rw [fiberSemantics]
  dsimp only
  rw [fiberCanonical_eq hu hf]

/-- Abstraction uses its declared codomain, independently of the chosen type of its body. -/
theorem fiberSemantics_lam (hPi : BoundedTyping 2 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 2 (A :: Γ) b B) (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ (.lam A b)).1 =
      fiberLambda (arityAt (.type 0) A)
        (fun x => fiberShape 2 0 Γ ρ A x)
        (fun x y => fiberShape 2 0 (A :: Γ) (push x ρ) B y)
        (shapeEval 2 0 Γ ρ (.lam A b))
        (fun x y => (fiberSemantics (A :: Γ) (push x ρ) (push y δ) b).1) := by
  have hbc (x : ShapeValue) (hx : x.code = arityAt (.type 0) A) (y : ShapeValue) :
      fiberShape 2 0 (A :: Γ) (push x ρ) (chosenType 2 (A :: Γ) b) y =
        fiberShape 2 0 (A :: Γ) (push x ρ) B y :=
    fiberShape_conv (chosenType_typing hb).type_expression hb.type_expression rfl
      (hρ.up hx) (typing_unique (chosenType_typing hb).forget hb.forget)
  have he := fiberLambda_congr (u := shapeEval 2 0 Γ ρ (.lam A b))
    (D := fun x => fiberShape 2 0 Γ ρ A x)
    (f := fun x y => (fiberSemantics (A :: Γ) (push x ρ) (push y δ) b).1)
    rfl (fun _ _ => rfl) hbc (fun _ _ _ _ => rfl)
  change FiberValue.force _ (fiberLambda _ _ _ _ _) = _
  rw [he]
  apply FiberValue.force_eq
  rw [fiberLambda_code, inferredFiber_eq (.lam hPi hb hPi.sort_bound) rfl hρ,
    fiberShape_pi hPi rfl hρ]

/-- Application may use any well-typed product assigned to its function. -/
theorem fiberSemantics_app (hf : BoundedTyping 2 Γ f (.pi A B))
    (ha : BoundedTyping 2 Γ a A) (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ (.app f a)).1 =
      fiberApply (arityAt (.type 0) A)
        (fun x => fiberShape 2 0 Γ ρ A x)
        (fun x y => fiberShape 2 0 (A :: Γ) (push x ρ) B y)
        (shapeEval 2 0 Γ ρ f) (fiberSemantics Γ ρ δ f).1
        (shapeEval 2 0 Γ ρ a) (fiberSemantics Γ ρ δ a).1 := by
  obtain ⟨s, hPi⟩ := hf.pi_type
  obtain ⟨s', hPi'⟩ := (chosenProduct_typing hf).pi_type
  obtain ⟨heA, heD, heB⟩ := fiberProduct_types_conv hPi' hPi
    (typing_unique (chosenProduct_typing hf).forget hf.forget) rfl hρ
  have he := fiberApply_congr
    (u := shapeEval 2 0 Γ ρ f) (f := (fiberSemantics Γ ρ δ f).1)
    (x := shapeEval 2 0 Γ ρ a) (y := (fiberSemantics Γ ρ δ a).1)
    heA (fun x _ => heD x) heB
  change FiberValue.force _ (fiberApply _ _ _ _ _ _ _) = _
  rw [he]
  apply FiberValue.force_eq
  rw [fiberApply_code _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ),
    inferredFiber_eq (.app hf ha) rfl hρ]
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  rw [fiberShape_subst hB ha hA rfl]
  rfl

end Submission.Helpers
