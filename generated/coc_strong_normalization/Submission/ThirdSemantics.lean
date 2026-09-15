import Submission.ThirdProductCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def thirdCanonical (a : Arity) (D : ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue) : Candidate :=
  let u' := u.force a
  let f' := f.force (D u')
  C u' f' (g.force (d u' f'))

theorem thirdCanonical_eq (hu : u.code = a) (hf : f.code = D u) (hg : g.code = d u f) :
    thirdCanonical a D d C u f g = C u f g := by
  unfold thirdCanonical
  dsimp only
  rw [u.force_eq hu, f.force_eq hf, g.force_eq hg]

noncomputable def thirdEncode (s : Option Srt) (k : Arity) (m : MiddleValue)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate) : ThirdValue :=
  match s with
  | some .prop => ⟨.small (.small .prop), C .unit .unit .unit⟩
  | some (.type 0) =>
      let l := m.cast (.small .prop)
      ⟨.small (.small (.fn l .prop)), fun z => C .unit .unit ⟨.small (.small l), z⟩⟩
  | some (.type 1) =>
      let F := m.cast (.universe k)
      ⟨.small (FiberCode.pi k F (fun _ => .small .prop)),
        FiberCode.piLambda k F (fun _ => .small .prop)
          (fun y z => C .unit ⟨.small k, y⟩ ⟨.small (F y), z⟩)⟩
  | _ => .unit

noncomputable def thirdDecode (s : Option Srt) (k : Arity) (m : MiddleValue)
    (v : ThirdValue) (_u : ShapeValue) (f : MiddleValue) (g : ThirdValue) : Candidate :=
  match s with
  | some .prop => v.cast (.small (.small .prop))
  | some (.type 0) =>
      let l := m.cast (.small .prop)
      v.cast (.small (.small (.fn l .prop))) (g.cast (.small (.small l)))
  | some (.type 1) =>
      let F := m.cast (.universe k)
      FiberCode.piApply k F (fun _ => .small .prop)
        (v.cast (.small (FiberCode.pi k F (fun _ => .small .prop))))
        (f.cast (.small k)) (g.cast (.small (F (f.cast (.small k)))))
  | _ => Candidate.sn

/-- The third value and the reducibility candidate family of a source term. -/
noncomputable def thirdSemantics (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → MiddleValue) (ε : Nat → ThirdValue) :
    Tm → ThirdValue × (ShapeValue → MiddleValue → ThirdValue → Candidate)
  | .var j =>
    let v := (ε j).force (inferredThird Γ ρ δ (.var j))
    (v, thirdDecode (typeSort 3 Γ (.var j)) (nextArity 3 1 Γ ρ (.var j))
      (middleSemantics Γ ρ δ (.var j)).1 v)
  | .srt s =>
    let C : ShapeValue → MiddleValue → ThirdValue → Candidate := fun _ _ _ => Candidate.sn
    let v := (thirdEncode (typeSort 3 Γ (.srt s)) (nextArity 3 1 Γ ρ (.srt s))
      (middleSemantics Γ ρ δ (.srt s)).1 C).force (inferredThird Γ ρ δ (.srt s))
    (v, C)
  | .app f a =>
    let p := chosenProduct 3 Γ f
    let v := (thirdApply (arityAt (.type 1) p.1)
      (fun x => middleShape 3 1 Γ ρ p.1 x)
      (fun x y => middleShape 3 1 (p.1 :: Γ) (push x ρ) p.2 y)
      (thirdShape Γ ρ δ p.1)
      (fun x y => thirdShape (p.1 :: Γ) (push x ρ) (push y δ) p.2)
      (shapeEval 3 1 Γ ρ f) (middleSemantics Γ ρ δ f).1 (thirdSemantics Γ ρ δ ε f).1
      (shapeEval 3 1 Γ ρ a) (middleSemantics Γ ρ δ a).1 (thirdSemantics Γ ρ δ ε a).1).force
        (inferredThird Γ ρ δ (.app f a))
    (v, thirdDecode (typeSort 3 Γ (.app f a)) (nextArity 3 1 Γ ρ (.app f a))
      (middleSemantics Γ ρ δ (.app f a)).1 v)
  | .lam A b =>
    let B := chosenType 3 (A :: Γ) b
    let v := (thirdLambda (arityAt (.type 1) A)
      (fun x => middleShape 3 1 Γ ρ A x)
      (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
      (thirdShape Γ ρ δ A)
      (fun x y => thirdShape (A :: Γ) (push x ρ) (push y δ) B)
      (shapeEval 3 1 Γ ρ (.lam A b)) (middleSemantics Γ ρ δ (.lam A b)).1
      (fun x y z => (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1)).force
        (inferredThird Γ ρ δ (.lam A b))
    (v, fun _ _ _ => Candidate.sn)
  | .pi A B =>
    let C := thirdCanonical (arityAt (.type 1) (.pi A B))
      (fun x => middleShape 3 1 Γ ρ (.pi A B) x) (thirdShape Γ ρ δ (.pi A B))
      (thirdCandidatePi (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (thirdShape Γ ρ δ A)
        (fun x y => thirdShape (A :: Γ) (push x ρ) (push y δ) B)
        (thirdSemantics Γ ρ δ ε A).2
        (fun x y z => (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) B).2))
    let v := (thirdEncode (typeSort 3 Γ (.pi A B)) (nextArity 3 1 Γ ρ (.pi A B))
      (middleSemantics Γ ρ δ (.pi A B)).1 C).force (inferredThird Γ ρ δ (.pi A B))
    (v, C)

theorem thirdSemantics_code (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → MiddleValue) (ε : Nat → ThirdValue) (t : Tm) :
    (thirdSemantics Γ ρ δ ε t).1.code = inferredThird Γ ρ δ t := by cases t <;> rfl

theorem thirdSemantics_typed_code (h : BoundedTyping 3 Γ t A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε t).1.code =
      thirdShape Γ ρ δ A (shapeEval 3 1 Γ ρ t) (middleSemantics Γ ρ δ t).1 :=
  (thirdSemantics_code Γ ρ δ ε t).trans (inferredThird_eq h hρ hδ)

theorem thirdSemantics_pi (hu : u.code = arityAt (.type 1) (.pi A B))
    (hf : f.code = middleShape 3 1 Γ ρ (.pi A B) u)
    (hg : g.code = thirdShape Γ ρ δ (.pi A B) u f) :
    (thirdSemantics Γ ρ δ ε (.pi A B)).2 u f g =
      thirdCandidatePi (arityAt (.type 1) A)
        (fun x => middleShape 3 1 Γ ρ A x)
        (fun x y => middleShape 3 1 (A :: Γ) (push x ρ) B y)
        (thirdShape Γ ρ δ A)
        (fun x y => thirdShape (A :: Γ) (push x ρ) (push y δ) B)
        (thirdSemantics Γ ρ δ ε A).2
        (fun x y z => (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) B).2) u f g := by
  rw [thirdSemantics]
  dsimp only
  rw [thirdCanonical_eq hu hf hg]

end Submission.Helpers
