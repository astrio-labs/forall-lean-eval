import Submission.ThirdCodes
import Submission.FiberUniverse

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A source product at the third layer consumes an upper and a middle value
for its argument; its remaining argument lives in the resulting arrow. -/
noncomputable def thirdProduct (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue) : ThirdCode :=
  ThirdCode.all (.small a) (fun x =>
    ThirdCode.all (D ⟨a, x⟩) (fun y =>
      (d ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩).arrow
        (c ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩ (u.apply ⟨a, x⟩)
          (middleApply a D B u f ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩))))

noncomputable def middleCanonical (a : Arity) (D : ShapeValue → MiddleCode)
    (C : ShapeValue → MiddleValue → ThirdCode) (u : ShapeValue) (f : MiddleValue) : ThirdCode :=
  C (u.force a) (f.force (D (u.force a)))

theorem middleCanonical_eq (hu : u.code = a) (hf : f.code = D u) :
    middleCanonical a D C u f = C u f := by
  unfold middleCanonical
  rw [u.force_eq hu, f.force_eq hf]

noncomputable def middleEncode (s : Option Srt) (k : Arity)
    (C : ShapeValue → MiddleValue → ThirdCode) : MiddleValue :=
  match s with
  | some (.type 0) => ⟨.small .prop, (C .unit .unit).asFiber.asArity⟩
  | some (.type 1) => ⟨.universe k, fun f => (C .unit ⟨.small k, f⟩).asFiber⟩
  | _ => .unit

noncomputable def middleDecode (s : Option Srt) (k : Arity) (v : MiddleValue)
    (_u : ShapeValue) (f : MiddleValue) : ThirdCode :=
  match s with
  | some (.type 0) => .small (.small (v.cast (.small .prop)))
  | some (.type 1) => .small (v.cast (.universe k) (f.cast (.small k)))
  | _ => .small (.small .unit)

/-- Carrier of inhabitants of a sort, parameterized by the preceding two values. -/
noncomputable def thirdSort (s : Srt) (u : ShapeValue) (f : MiddleValue) : ThirdCode :=
  match s with
  | .prop => .small (.small .prop)
  | .type 0 => .small (.small (.fn (f.cast (.small .prop)) .prop))
  | .type 1 => .small (FiberCode.all u.asArity
      (fun x => (f.cast (.universe u.asArity) x).arrow (.small .prop)))
  | _ => .small (.small .unit)

/-- Middle evaluation, together with the carrier of a term viewed as a type.
The third carrier depends only on the preceding layers. -/
noncomputable def middleSemantics (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → MiddleValue) : Tm → MiddleValue × (ShapeValue → MiddleValue → ThirdCode)
  | .var j =>
    let v := (δ j).force (inferredMiddle 3 1 Γ ρ (.var j))
    (v, middleDecode (typeSort 3 Γ (.var j)) (nextArity 3 1 Γ ρ (.var j)) v)
  | .srt s =>
    let C := thirdSort s
    let v := (middleEncode (typeSort 3 Γ (.srt s)) (nextArity 3 1 Γ ρ (.srt s)) C).force
      (inferredMiddle 3 1 Γ ρ (.srt s))
    (v, C)
  | .app f a =>
    let p := chosenProduct 3 Γ f
    let v := (middleApply (arityAt (.type 1) p.1)
      (fun x => middleShape 3 1 Γ ρ p.1 x)
      (fun x y => middleShape 3 1 (p.1 :: Γ) (push x ρ) p.2 y)
      (shapeEval 3 1 Γ ρ f) (middleSemantics Γ ρ δ f).1
      (shapeEval 3 1 Γ ρ a) (middleSemantics Γ ρ δ a).1).force
        (inferredMiddle 3 1 Γ ρ (.app f a))
    (v, middleDecode (typeSort 3 Γ (.app f a)) (nextArity 3 1 Γ ρ (.app f a)) v)
  | .lam A b =>
    let v := (middleLambda (arityAt (.type 1) A)
      (fun x => middleShape 3 1 Γ ρ A x)
      (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) (chosenType 3 (A :: Γ) b) y)
      (shapeEval 3 1 Γ ρ (.lam A b))
      (fun x y => (middleSemantics (A :: Γ) (push x ρ) (push y δ) b).1)).force
        (inferredMiddle 3 1 Γ ρ (.lam A b))
    (v, fun _ _ => .small (.small .unit))
  | .pi A B =>
    let C := middleCanonical (arityAt (.type 1) (.pi A B))
      (fun x => middleShape 3 1 Γ ρ (.pi A B) x)
      (thirdProduct (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (middleSemantics Γ ρ δ A).2
        (fun x y => (middleSemantics (A :: Γ) (push x ρ) (push y δ) B).2))
    let v := (middleEncode (typeSort 3 Γ (.pi A B)) (nextArity 3 1 Γ ρ (.pi A B)) C).force
      (inferredMiddle 3 1 Γ ρ (.pi A B))
    (v, C)

theorem middleSemantics_code (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → MiddleValue) (t : Tm) :
    (middleSemantics Γ ρ δ t).1.code = inferredMiddle 3 1 Γ ρ t := by
  cases t <;> rfl

theorem middleSemantics_typed_code (h : BoundedTyping 3 Γ t A)
    (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ t).1.code = middleShape 3 1 Γ ρ A (shapeEval 3 1 Γ ρ t) :=
  (middleSemantics_code Γ ρ δ t).trans (inferredMiddle_eq h rfl hρ)

theorem middleSemantics_pi (hu : u.code = arityAt (.type 1) (.pi A B))
    (hf : f.code = middleShape 3 1 Γ ρ (.pi A B) u) :
    (middleSemantics Γ ρ δ (.pi A B)).2 u f =
      thirdProduct (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (middleSemantics Γ ρ δ A).2
        (fun x y => (middleSemantics (A :: Γ) (push x ρ) (push y δ) B).2) u f := by
  rw [middleSemantics]
  dsimp only
  rw [middleCanonical_eq hu hf]

/-- Abstraction uses its declared codomain, independently of the chosen type of its body. -/
theorem middleSemantics_lam (hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 3 (A :: Γ) b B) (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ (.lam A b)).1 =
      middleLambda (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (shapeEval 3 1 Γ ρ (.lam A b))
        (fun x y => (middleSemantics (A :: Γ) (push x ρ) (push y δ) b).1) := by
  have hbc (x : ShapeValue) (hx : x.code = arityAt (.type 1) A) (y : ShapeValue) :
      middleShape 3 1 (A :: Γ) (push x ρ) (chosenType 3 (A :: Γ) b) y =
        middleShape 3 1 (A :: Γ) (push x ρ) B y :=
    middleShape_conv (chosenType_typing hb).type_expression hb.type_expression rfl
      (hρ.up hx) (typing_unique (chosenType_typing hb).forget hb.forget)
  have he := middleLambda_congr (u := shapeEval 3 1 Γ ρ (.lam A b))
    (D := fun x => middleShape 3 1 Γ ρ A x)
    (f := fun x y => (middleSemantics (A :: Γ) (push x ρ) (push y δ) b).1)
    rfl (fun _ _ => rfl) hbc (fun _ _ _ _ => rfl)
  change MiddleValue.force _ (middleLambda _ _ _ _ _) = _
  rw [he]
  apply MiddleValue.force_eq
  rw [middleLambda_code, inferredMiddle_eq (.lam hPi hb hPi.sort_bound) rfl hρ,
    middleShape_pi hPi rfl hρ]

/-- Application may use any well-typed product assigned to its function. -/
theorem middleSemantics_app (hf : BoundedTyping 3 Γ f (.pi A B))
    (ha : BoundedTyping 3 Γ a A) (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ (.app f a)).1 =
      middleApply (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (shapeEval 3 1 Γ ρ f) (middleSemantics Γ ρ δ f).1
        (shapeEval 3 1 Γ ρ a) (middleSemantics Γ ρ δ a).1 := by
  obtain ⟨s, hPi⟩ := hf.pi_type
  obtain ⟨s', hPi'⟩ := (chosenProduct_typing hf).pi_type
  obtain ⟨heA, heD, heB⟩ := middleProduct_types_conv hPi' hPi
    (typing_unique (chosenProduct_typing hf).forget hf.forget) rfl hρ
  have he := middleApply_congr
    (u := shapeEval 3 1 Γ ρ f) (f := (middleSemantics Γ ρ δ f).1)
    (x := shapeEval 3 1 Γ ρ a) (y := (middleSemantics Γ ρ δ a).1)
    heA (fun x _ => heD x) heB
  change MiddleValue.force _ (middleApply _ _ _ _ _ _ _) = _
  rw [he]
  apply MiddleValue.force_eq
  rw [middleApply_code _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ),
    inferredMiddle_eq (.app hf ha) rfl hρ]
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  rw [middleShape_subst hB ha hA rfl]
  rfl

end Submission.Helpers
