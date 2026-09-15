import Submission.FirstGridShape

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem firstGridShape_top_sort (hw : BoundedWf (r + 3) Γ) :
    firstGridShape r Γ ρ (.srt (.type (r + 1))) u = .atom u.asArity := by
  have h : BoundedTyping (r + 3) Γ (.srt (.type (r + 1))) (.srt (.type (r + 2))) :=
    .srt hw (.type _) (by simp only [sortRank]; omega) (by simp only [sortRank]; omega)
  unfold firstGridShape
  rw [middleShape_top h rfl rfl]
  simp only [↓reduceIte]
  rfl

/-- This universe's payload increases with the bound. -/
theorem firstGridUniverse_carrier (r : Nat) (a : Arity) :
    (carrierGrid (r + 2) 1).El (.atom a) = (a.ShapeEl → (carrierGrid (r + 1) 1).Code) := rfl

def firstGridUniverseEncode (r : Nat) (a : Arity)
    (C : a.ShapeEl → (carrierGrid (r + 1) 1).Code) : FirstGridValue r := ⟨.atom a, C⟩

noncomputable def firstGridUniverseDecode (r : Nat) (a : Arity) (v : FirstGridValue r) :
    a.ShapeEl → (carrierGrid (r + 1) 1).Code := v.cast (.atom a)

theorem firstGrid_universe_roundtrip (r : Nat) (a : Arity)
    (C : a.ShapeEl → (carrierGrid (r + 1) 1).Code) :
    firstGridUniverseDecode r a (firstGridUniverseEncode r a C) = C :=
  TowerValue.cast_mk (S := carrierGrid (r + 2) 1) (.atom a) C

theorem firstGridUniverseEncode_typed (hw : BoundedWf (r + 3) Γ)
    (C : u.asArity.ShapeEl → (carrierGrid (r + 1) 1).Code) :
    (firstGridUniverseEncode r u.asArity C).code =
      firstGridShape r Γ ρ (.srt (.type (r + 1))) u := (firstGridShape_top_sort hw).symm

noncomputable def firstGridApply (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 2) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code)
    (u : ShapeValue) (f : FirstGridValue r) (x : ShapeValue) (y : FirstGridValue r) : FirstGridValue r :=
  let v := x.cast a
  let z : ShapeValue := ⟨a, v⟩
  ⟨B z (u.apply z),
    (carrierGridQuantifiers (r + 1) 0).piApply (carrierGridArrows (r + 2) 1) a
      (fun v => D ⟨a, v⟩) (fun v => B ⟨a, v⟩ (u.apply ⟨a, v⟩))
      (f.cast (firstGridProduct r a D B u)) v (y.cast (D z))⟩

noncomputable def firstGridLambda (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 2) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code)
    (u : ShapeValue) (b : ShapeValue → FirstGridValue r → FirstGridValue r) : FirstGridValue r :=
  ⟨firstGridProduct r a D B u,
    (carrierGridQuantifiers (r + 1) 0).piLambda (carrierGridArrows (r + 2) 1) a
      (fun v => D ⟨a, v⟩) (fun v => B ⟨a, v⟩ (u.apply ⟨a, v⟩))
      (fun v y => (b ⟨a, v⟩ ⟨D ⟨a, v⟩, y⟩).cast (B ⟨a, v⟩ (u.apply ⟨a, v⟩)))⟩

theorem firstGridLambda_code (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 2) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code)
    (u : ShapeValue) (b : ShapeValue → FirstGridValue r → FirstGridValue r) :
    (firstGridLambda r a D B u b).code = firstGridProduct r a D B u := rfl

theorem firstGridApply_code (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 2) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code)
    (u : ShapeValue) (f : FirstGridValue r) (x : ShapeValue) (y : FirstGridValue r)
    (hx : x.code = a) : (firstGridApply r a D B u f x y).code = B x (u.apply x) := by
  change B ⟨a, x.cast a⟩ (u.apply ⟨a, x.cast a⟩) = _
  rw [x.mk_cast hx]

theorem firstGridBeta (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 2) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code)
    (u : ShapeValue) (b : ShapeValue → FirstGridValue r → FirstGridValue r)
    (x : ShapeValue) (y : FirstGridValue r) (hx : x.code = a) (hy : y.code = D x)
    (hb : (b x y).code = B x (u.apply x)) :
    firstGridApply r a D B u (firstGridLambda r a D B u b) x y = b x y := by
  cases x with
  | mk ax vx =>
    change ax = a at hx
    subst ax
    cases y with
    | mk ay vy =>
      change ay = D ⟨a, vx⟩ at hy
      subst ay
      unfold firstGridApply firstGridLambda
      dsimp only
      rw [ShapeValue.cast_mk a vx]
      rw [TowerValue.cast_mk (S := carrierGrid (r + 2) 1) (D ⟨a, vx⟩) vy]
      let F := fun v : a.ShapeEl => D ⟨a, v⟩
      let E := fun v : a.ShapeEl => B ⟨a, v⟩ (u.apply ⟨a, v⟩)
      let body := fun (v : a.ShapeEl) (z : (carrierGrid (r + 2) 1).El (F v)) =>
        (b ⟨a, v⟩ ⟨F v, z⟩).cast (E v)
      have hcast := TowerValue.cast_mk (S := carrierGrid (r + 2) 1)
        (firstGridProduct r a D B u)
        ((carrierGridQuantifiers (r + 1) 0).piLambda (carrierGridArrows (r + 2) 1) a F E body)
      have hbeta := (carrierGridQuantifiers (r + 1) 0).piBeta
        (carrierGridArrows (r + 2) 1) a F E body vx vy
      exact (congrArg (TowerValue.mk (S := carrierGrid (r + 2) 1) (E vx))
        ((congrArg (fun z => (carrierGridQuantifiers (r + 1) 0).piApply
          (carrierGridArrows (r + 2) 1) a F E z vx vy) hcast).trans hbeta)).trans
        (TowerValue.mk_cast _ hb)

/-- The semantic abstraction has the carrier of the source product for
every finite source bound represented by this first grid coordinate. -/
theorem firstGridLambda_typed (hPi : BoundedTyping (r + 3) Γ (.pi A B) (.srt s))
    (hρ : ShapeContext (.type (r + 1)) Γ ρ)
    (b : ShapeValue → FirstGridValue r → FirstGridValue r) :
    (firstGridLambda r (arityAt (.type (r + 1)) A)
      (fun x => firstGridShape r Γ ρ A x)
      (fun x y => firstGridShape r (A :: Γ) (push x ρ) B y) u b).code =
        firstGridShape r Γ ρ (.pi A B) u := (firstGridShape_pi hPi hρ).symm

end Submission.Helpers
