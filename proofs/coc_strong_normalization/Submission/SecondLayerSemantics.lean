import Submission.CarrierUniverseIteration

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- This intermediate refinement applies at every bound `r + 5`.
At bound four its next universe carrier instead needs the bottom construction. -/
abbrev SecondLayerCode (r : Nat) := (carrierGrid (r + 4) 3).Code
abbrev SecondLayerValue (r : Nat) := SecondGridValue (r + 1)

def secondLayerUnit (r : Nat) : SecondLayerValue r := ⟨.small (.small .unit), ()⟩

def secondLayerAsArity (r : Nat) (C : SecondLayerCode r) : Arity := C.asSmall.asSmall.asSmall

noncomputable def secondLayerProduct (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 4) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 4) 1).Code)
    (d : ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code)
    (c : ShapeValue → UpperGridValue (r + 1) → ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code)
    (E : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
    (F : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r →
      ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) : SecondLayerCode r :=
  let H := carrierGridHorizontal (r + 4) 1 (by omega)
  (carrierGridQuantifiers (r + 3) 2).code (.small (.small a)) (fun x =>
    (carrierGridQuantifiers (r + 3) 2).code (H.code (D ⟨a, x⟩)) (fun y =>
      let y' : UpperGridValue (r + 1) := ⟨D ⟨a, x⟩, (H.values (D ⟨a, x⟩)).decode y⟩
      (carrierGridQuantifiers (r + 3) 2).code (d ⟨a, x⟩ y') (fun z =>
        let z' : SecondLayerValue r := ⟨d ⟨a, x⟩ y', z⟩
        (carrierGridArrows (r + 4) 3).code (E ⟨a, x⟩ y' z')
          (F ⟨a, x⟩ y' z' (u.apply ⟨a, x⟩)
            (firstGridApply (r + 2) a D B u f ⟨a, x⟩ y')
            (secondGridApply (r + 1) a D B d c u f g ⟨a, x⟩ y' z')))))

noncomputable def secondLayerCanonical (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 4) 1).Code)
    (d : ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code)
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) : SecondLayerCode r :=
  let u' := u.force a
  let f' := f.force (D u')
  C u' f' (g.force (d u' f'))

theorem secondLayerCanonical_eq {r : Nat} {a : Arity}
    {D : ShapeValue → (carrierGrid (r + 4) 1).Code}
    {d : ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code}
    {C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r}
    {u : ShapeValue} {f : UpperGridValue (r + 1)} {g : SecondLayerValue r}
    (hu : u.code = a) (hf : f.code = D u) (hg : g.code = d u f) :
    secondLayerCanonical r a D d C u f g = C u f g := by
  unfold secondLayerCanonical
  dsimp only
  rw [u.force_eq hu, f.force_eq hf, g.force_eq hg]

noncomputable def secondLayerEncode (r : Nat) (s : Option Srt) (k : Arity) (m : UpperGridValue (r + 1))
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r) : SecondLayerValue r := by
  classical
  exact if s.map sortRank = some (r + 2) then
    ⟨.small (.small .prop), secondLayerAsArity r (C .unit (upperGridUnit (r + 1)) (secondLayerUnit r))⟩
  else if s.map sortRank = some (r + 3) then
    let l := m.cast (.small .prop)
    ⟨.small (.atom l), fun z => (C .unit (upperGridUnit (r + 1)) ⟨.small (.small l), z⟩).asSmall.asSmall⟩
  else if s.map sortRank = some (r + 4) then
    let F := m.cast (.atom k)
    let U := carrierGridUniverseNext (r + 3) 0 (by omega) k F
    ⟨U.code, U.values.encode (fun x y => (C .unit ⟨.small k, x⟩ ⟨.small (F x), y⟩).asSmall)⟩
  else secondLayerUnit r

noncomputable def secondLayerDecode (r : Nat) (s : Option Srt) (k : Arity) (m : UpperGridValue (r + 1))
    (v : SecondLayerValue r) (_u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) : SecondLayerCode r := by
  classical
  exact if s.map sortRank = some (r + 2) then .small (.small (.small (v.cast (.small (.small .prop)))))
  else if s.map sortRank = some (r + 3) then
    let l := m.cast (.small .prop)
    .small (.small (v.cast (.small (.atom l)) (g.cast (.small (.small l)))))
  else if s.map sortRank = some (r + 4) then
    let F := m.cast (.atom k)
    let U := carrierGridUniverseNext (r + 3) 0 (by omega) k F
    .small (U.values.decode (v.cast U.code) (f.cast (.small k)) (g.cast (.small (F (f.cast (.small k))))))
  else .small (.small (.small .unit))

noncomputable def secondLayerSort (r : Nat) (s : Srt) (u : ShapeValue)
    (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) : SecondLayerCode r := by
  classical
  exact if sortRank s = r + 1 then .small (.small (.small .prop))
  else if sortRank s = r + 2 then .small (.small (.atom (g.cast (.small (.small .prop)))))
  else if sortRank s = r + 3 then
    let l := f.cast (.small .prop)
    .small (carrierGridUniverseNext (r + 2) 0 (by omega) l (g.cast (.small (.atom l)))).code
  else if sortRank s = r + 4 then
    let k := u.asArity
    let F := f.cast (.atom k)
    let U := carrierGridUniverseNext (r + 3) 0 (by omega) k F
    (carrierGridUniverseTwice (r + 3) 0 (by omega) k F (U.values.decode (g.cast U.code))).code
  else .small (.small (.small .unit))

/-- The second value and third carrier, evaluated structurally on source
syntax without a normalization premise. -/
noncomputable def secondLayerSemantics (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue (r + 1)) (ε : Nat → SecondLayerValue r) :
    Tm → SecondLayerValue r × (ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
  | .var j =>
    let v := (ε j).force (inferredSecondGrid (r + 1) Γ ρ δ (.var j))
    (v, secondLayerDecode r (typeSort (r + 5) Γ (.var j)) (nextArity (r + 5) (r + 3) Γ ρ (.var j))
      (upperGridSemantics (r + 1) Γ ρ δ (.var j)).1 v)
  | .srt s =>
    let C := secondLayerSort r s
    let v := (secondLayerEncode r (typeSort (r + 5) Γ (.srt s)) (nextArity (r + 5) (r + 3) Γ ρ (.srt s))
      (upperGridSemantics (r + 1) Γ ρ δ (.srt s)).1 C).force (inferredSecondGrid (r + 1) Γ ρ δ (.srt s))
    (v, C)
  | .app f a =>
    let p := chosenProduct (r + 5) Γ f
    let v := (secondGridApply (r + 1) (arityAt (.type (r + 3)) p.1)
      (fun x => firstGridShape (r + 2) Γ ρ p.1 x)
      (fun x y => firstGridShape (r + 2) (p.1 :: Γ) (push x ρ) p.2 y)
      (secondGridShape (r + 1) Γ ρ δ p.1)
      (fun x y => secondGridShape (r + 1) (p.1 :: Γ) (push x ρ) (push y δ) p.2)
      (shapeEval (r + 5) (r + 3) Γ ρ f) (upperGridSemantics (r + 1) Γ ρ δ f).1 (secondLayerSemantics r Γ ρ δ ε f).1
      (shapeEval (r + 5) (r + 3) Γ ρ a) (upperGridSemantics (r + 1) Γ ρ δ a).1 (secondLayerSemantics r Γ ρ δ ε a).1).force
        (inferredSecondGrid (r + 1) Γ ρ δ (.app f a))
    (v, secondLayerDecode r (typeSort (r + 5) Γ (.app f a)) (nextArity (r + 5) (r + 3) Γ ρ (.app f a))
      (upperGridSemantics (r + 1) Γ ρ δ (.app f a)).1 v)
  | .lam A b =>
    let B := chosenType (r + 5) (A :: Γ) b
    let v := (secondGridLambda (r + 1) (arityAt (.type (r + 3)) A)
      (fun x => firstGridShape (r + 2) Γ ρ A x)
      (fun x y => firstGridShape (r + 2) (A :: Γ) (push x ρ) B y)
      (secondGridShape (r + 1) Γ ρ δ A)
      (fun x y => secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) B)
      (shapeEval (r + 5) (r + 3) Γ ρ (.lam A b)) (upperGridSemantics (r + 1) Γ ρ δ (.lam A b)).1
      (fun x y z => (secondLayerSemantics r (A :: Γ) (push x ρ) (push y δ) (push z ε) b).1)).force
        (inferredSecondGrid (r + 1) Γ ρ δ (.lam A b))
    (v, fun _ _ _ => .small (.small (.small .unit)))
  | .pi A B =>
    let C := secondLayerCanonical r (arityAt (.type (r + 3)) (.pi A B))
      (fun x => firstGridShape (r + 2) Γ ρ (.pi A B) x) (secondGridShape (r + 1) Γ ρ δ (.pi A B))
      (secondLayerProduct r (arityAt (.type (r + 3)) A)
        (fun x => firstGridShape (r + 2) Γ ρ A x)
        (fun x y => firstGridShape (r + 2) (A :: Γ) (push x ρ) B y)
        (secondGridShape (r + 1) Γ ρ δ A)
        (fun x y => secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) B)
        (secondLayerSemantics r Γ ρ δ ε A).2
        (fun x y z => (secondLayerSemantics r (A :: Γ) (push x ρ) (push y δ) (push z ε) B).2))
    let v := (secondLayerEncode r (typeSort (r + 5) Γ (.pi A B)) (nextArity (r + 5) (r + 3) Γ ρ (.pi A B))
      (upperGridSemantics (r + 1) Γ ρ δ (.pi A B)).1 C).force (inferredSecondGrid (r + 1) Γ ρ δ (.pi A B))
    (v, C)

theorem secondLayerSemantics_code (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → UpperGridValue (r + 1)) (ε : Nat → SecondLayerValue r) (t : Tm) :
    (secondLayerSemantics r Γ ρ δ ε t).1.code = inferredSecondGrid (r + 1) Γ ρ δ t := by cases t <;> rfl

theorem secondLayerSemantics_typed_code (h : BoundedTyping (r + 5) Γ t A)
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε t).1.code =
      secondGridShape (r + 1) Γ ρ δ A (shapeEval (r + 5) (r + 3) Γ ρ t) (upperGridSemantics (r + 1) Γ ρ δ t).1 :=
  (secondLayerSemantics_code r Γ ρ δ ε t).trans (inferredSecondGrid_eq h hρ hδ)

theorem secondLayerSemantics_pi (hu : u.code = arityAt (.type (r + 3)) (.pi A B))
    (hf : f.code = firstGridShape (r + 2) Γ ρ (.pi A B) u)
    (hg : g.code = secondGridShape (r + 1) Γ ρ δ (.pi A B) u f) :
    (secondLayerSemantics r Γ ρ δ ε (.pi A B)).2 u f g =
      secondLayerProduct r (arityAt (.type (r + 3)) A)
        (fun x => firstGridShape (r + 2) Γ ρ A x)
        (fun x y => firstGridShape (r + 2) (A :: Γ) (push x ρ) B y)
        (secondGridShape (r + 1) Γ ρ δ A)
        (fun x y => secondGridShape (r + 1) (A :: Γ) (push x ρ) (push y δ) B)
        (secondLayerSemantics r Γ ρ δ ε A).2
        (fun x y z => (secondLayerSemantics r (A :: Γ) (push x ρ) (push y δ) (push z ε) B).2) u f g := by
  rw [secondLayerSemantics]
  dsimp only
  rw [secondLayerCanonical_eq hu hf hg]

end Submission.Helpers
