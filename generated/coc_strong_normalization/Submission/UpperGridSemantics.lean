import Submission.FirstGridOperations
import Submission.CarrierUniverseStep

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def TowerValue.force {S : CarrierSystem} (A : S.Code) (v : TowerValue S) : TowerValue S :=
  ⟨A, v.cast A⟩

theorem TowerValue.force_eq {S : CarrierSystem} {A : S.Code} (v : TowerValue S) (h : v.code = A) :
    TowerValue.force A v = v :=
  v.mk_cast h

abbrev UpperGridCode (r : Nat) := (carrierGrid (r + 3) 2).Code
abbrev UpperGridValue (r : Nat) := FirstGridValue (r + 1)

def upperGridUnit (r : Nat) : UpperGridValue r := ⟨.small .unit, ()⟩

def upperGridAsArity (r : Nat) (C : UpperGridCode r) : Arity := C.asSmall.asSmall

noncomputable def upperGridProduct (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r) : UpperGridCode r :=
  (carrierGridQuantifiers (r + 2) 1).code (.small a) (fun x =>
    (carrierGridQuantifiers (r + 2) 1).code (D ⟨a, x⟩) (fun y =>
      (carrierGridArrows (r + 3) 2).code (d ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)
        (c ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩ (u.apply ⟨a, x⟩)
          (firstGridApply (r + 1) a D B u f ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩))))

noncomputable def upperGridCanonical (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (C : ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r) : UpperGridCode r :=
  C (u.force a) (f.force (D (u.force a)))

noncomputable def upperGridEncode (r : Nat) (s : Option Srt) (k : Arity)
    (C : ShapeValue → UpperGridValue r → UpperGridCode r) : UpperGridValue r := by
  classical
  exact if s.map sortRank = some (r + 2) then
    ⟨.small .prop, upperGridAsArity r (C .unit (upperGridUnit r))⟩
  else if s.map sortRank = some (r + 3) then
    ⟨.atom k, fun f => (C .unit ⟨.small k, f⟩).asSmall⟩
  else upperGridUnit r

noncomputable def upperGridDecode (r : Nat) (s : Option Srt) (k : Arity)
    (v : UpperGridValue r) (_u : ShapeValue) (f : UpperGridValue r) : UpperGridCode r := by
  classical
  exact if s.map sortRank = some (r + 2) then .small (.small (v.cast (.small .prop)))
  else if s.map sortRank = some (r + 3) then .small (v.cast (.atom k) (f.cast (.small k)))
  else .small (.small .unit)

/-- The next sort carrier uses the uniform universe refinement. The two
smaller visible sorts retain respectively arity data and lower code families. -/
noncomputable def upperGridSort (r : Nat) (s : Srt) (u : ShapeValue) (f : UpperGridValue r) : UpperGridCode r := by
  classical
  exact if sortRank s = r + 1 then .small (.small .prop)
  else if sortRank s = r + 2 then .small (.atom (f.cast (.small .prop)))
  else if sortRank s = r + 3 then
    (carrierGridUniverseNext (r + 2) 0 (by omega) u.asArity (f.cast (.atom u.asArity))).code
  else .small (.small .unit)

/-- One complete value/carrier refinement for every source bound at least
four. The returned carrier belongs to the next coordinate of the same row. -/
noncomputable def upperGridSemantics (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue r) : Tm → UpperGridValue r × (ShapeValue → UpperGridValue r → UpperGridCode r)
  | .var j =>
    let v := (δ j).force (inferredFirstGrid (r + 1) Γ ρ (.var j))
    (v, upperGridDecode r (typeSort (r + 4) Γ (.var j)) (nextArity (r + 4) (r + 2) Γ ρ (.var j)) v)
  | .srt s =>
    let C := upperGridSort r s
    let v := (upperGridEncode r (typeSort (r + 4) Γ (.srt s))
      (nextArity (r + 4) (r + 2) Γ ρ (.srt s)) C).force (inferredFirstGrid (r + 1) Γ ρ (.srt s))
    (v, C)
  | .app f a =>
    let p := chosenProduct (r + 4) Γ f
    let v := (firstGridApply (r + 1) (arityAt (.type (r + 2)) p.1)
      (fun x => firstGridShape (r + 1) Γ ρ p.1 x)
      (fun x y => firstGridShape (r + 1) (p.1 :: Γ) (push x ρ) p.2 y)
      (shapeEval (r + 4) (r + 2) Γ ρ f) (upperGridSemantics r Γ ρ δ f).1
      (shapeEval (r + 4) (r + 2) Γ ρ a) (upperGridSemantics r Γ ρ δ a).1).force
        (inferredFirstGrid (r + 1) Γ ρ (.app f a))
    (v, upperGridDecode r (typeSort (r + 4) Γ (.app f a)) (nextArity (r + 4) (r + 2) Γ ρ (.app f a)) v)
  | .lam A b =>
    let v := (firstGridLambda (r + 1) (arityAt (.type (r + 2)) A)
      (fun x => firstGridShape (r + 1) Γ ρ A x)
      (fun x y => firstGridShape (r + 1) (A :: Γ) (push x ρ) (chosenType (r + 4) (A :: Γ) b) y)
      (shapeEval (r + 4) (r + 2) Γ ρ (.lam A b))
      (fun x y => (upperGridSemantics r (A :: Γ) (push x ρ) (push y δ) b).1)).force
        (inferredFirstGrid (r + 1) Γ ρ (.lam A b))
    (v, fun _ _ => .small (.small .unit))
  | .pi A B =>
    let C := upperGridCanonical r (arityAt (.type (r + 2)) (.pi A B))
      (fun x => firstGridShape (r + 1) Γ ρ (.pi A B) x)
      (upperGridProduct r (arityAt (.type (r + 2)) A)
        (fun x => firstGridShape (r + 1) Γ ρ A x)
        (fun x y => firstGridShape (r + 1) (A :: Γ) (push x ρ) B y)
        (upperGridSemantics r Γ ρ δ A).2
        (fun x y => (upperGridSemantics r (A :: Γ) (push x ρ) (push y δ) B).2))
    let v := (upperGridEncode r (typeSort (r + 4) Γ (.pi A B))
      (nextArity (r + 4) (r + 2) Γ ρ (.pi A B)) C).force (inferredFirstGrid (r + 1) Γ ρ (.pi A B))
    (v, C)

theorem upperGridSemantics_code (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue r) (t : Tm) :
    (upperGridSemantics r Γ ρ δ t).1.code = inferredFirstGrid (r + 1) Γ ρ t := by
  cases t <;> rfl

theorem upperGridSemantics_typed_code (h : BoundedTyping (r + 4) Γ t A)
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ t).1.code =
      firstGridShape (r + 1) Γ ρ A (shapeEval (r + 4) (r + 2) Γ ρ t) :=
  (upperGridSemantics_code r Γ ρ δ t).trans (inferredFirstGrid_eq h hρ)

theorem upperGridSemantics_pi {r : Nat} {u : ShapeValue} {f : UpperGridValue r}
    {Γ : List Tm} {ρ : Nat → ShapeValue} {δ : Nat → UpperGridValue r} {A B : Tm}
    (hu : u.code = arityAt (.type (r + 2)) (.pi A B))
    (hf : f.code = firstGridShape (r + 1) Γ ρ (.pi A B) u) :
    (upperGridSemantics r Γ ρ δ (.pi A B)).2 u f =
      upperGridProduct r (arityAt (.type (r + 2)) A)
        (fun x => firstGridShape (r + 1) Γ ρ A x)
        (fun x y => firstGridShape (r + 1) (A :: Γ) (push x ρ) B y)
        (upperGridSemantics r Γ ρ δ A).2
        (fun x y => (upperGridSemantics r (A :: Γ) (push x ρ) (push y δ) B).2) u f := by
  rw [upperGridSemantics]
  dsimp only
  unfold upperGridCanonical
  rw [u.force_eq hu, f.force_eq hf]

end Submission.Helpers
