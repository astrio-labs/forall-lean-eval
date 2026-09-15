import Submission.ThirdModel

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A carrier may have a larger representation, provided decoding recovers
its original data exactly. -/
structure CarrierRetraction (A B : Type) where
  encode : A → B
  decode : B → A
  roundtrip : ∀ a, decode (encode a) = a

def CarrierRetraction.identity (A : Type) : CarrierRetraction A A := ⟨id, id, fun _ => rfl⟩

def CarrierRetraction.arrow (R : CarrierRetraction A A') (S : CarrierRetraction B B') :
    CarrierRetraction (A → B) (A' → B') where
  encode f x := S.encode (f (R.decode x))
  decode f x := S.decode (f (R.encode x))
  roundtrip f := by
    funext x
    dsimp only
    rw [R.roundtrip, S.roundtrip]

theorem dependent_cast_apply {X : Type} {B : X → Type} (f : (x : X) → B x)
    {x y : X} (h : x = y) : cast (congrArg B h) (f x) = f y := by cases h; rfl

/-- Dependent functions extend along a retraction of their index carrier. -/
def CarrierRetraction.pi (R : CarrierRetraction X Y)
    (B C : X → Type) (S : (x : X) → CarrierRetraction (B x) (C x)) :
    CarrierRetraction ((x : X) → B x) ((y : Y) → C (R.decode y)) where
  encode f y := (S (R.decode y)).encode (f (R.decode y))
  decode f x := cast (congrArg B (R.roundtrip x)) ((S (R.decode (R.encode x))).decode (f (R.encode x)))
  roundtrip f := by
    funext x
    rw [(S (R.decode (R.encode x))).roundtrip]
    exact dependent_cast_apply f (R.roundtrip x)

abbrev shapeTowerSystem := fiberCarrierSystem.withUniverse.simple

def shapeTowerCode : Arity → shapeTowerSystem.Code
  | .unit => .atom (.old (.small .unit))
  | .prop => .atom .codes
  | .fn A B => .arrow (shapeTowerCode A) (shapeTowerCode B)

def shapeTowerRetraction : (a : Arity) → CarrierRetraction a.ShapeEl (shapeTowerSystem.El (shapeTowerCode a))
  | .unit => CarrierRetraction.identity Unit
  | .prop => ⟨FiberCode.small, FiberCode.asArity, fun _ => rfl⟩
  | .fn A B => (shapeTowerRetraction A).arrow (shapeTowerRetraction B)

/-- The richer middle universes of bound three fit the existing general tower.
The domain of every dependent constructor comes from the preceding system. -/
def middleTowerCode : MiddleCode → (normalizationTower 1).Code
  | .small a => .old (shapeTowerCode a)
  | .universe a => .old (.arrow (shapeTowerCode a) (.atom .codes))
  | .fn A B => .arrow (middleTowerCode A) (middleTowerCode B)
  | .quant a B => .all (shapeTowerCode a)
      (fun x => middleTowerCode (B ((shapeTowerRetraction a).decode x)))

def middleTowerRetraction : (A : MiddleCode) →
    CarrierRetraction A.El ((normalizationTower 1).El (middleTowerCode A))
  | .small a => shapeTowerRetraction a
  | .universe a => (shapeTowerRetraction a).arrow (CarrierRetraction.identity FiberCode)
  | .fn A B => (middleTowerRetraction A).arrow (middleTowerRetraction B)
  | .quant a B => CarrierRetraction.pi (shapeTowerRetraction a)
      (fun x => (B x).El) (fun x => (normalizationTower 1).El (middleTowerCode (B x)))
      (fun x => middleTowerRetraction (B x))

/-- Third-layer dependent carriers fit the next general tower level. -/
def thirdTowerCode : ThirdCode → (normalizationTower 2).Code
  | .small a => .old (.atom (.old (.old (.atom (.old a)))))
  | .fn A B => .arrow (thirdTowerCode A) (thirdTowerCode B)
  | .quant A B => .all (.atom (.old (middleTowerCode A)))
      (fun x => thirdTowerCode (B ((middleTowerRetraction A).decode x)))

def thirdTowerRetraction : (A : ThirdCode) →
    CarrierRetraction A.El ((normalizationTower 2).El (thirdTowerCode A))
  | .small a => CarrierRetraction.identity a.El
  | .fn A B => (thirdTowerRetraction A).arrow (thirdTowerRetraction B)
  | .quant A B => CarrierRetraction.pi (middleTowerRetraction A)
      (fun x => (B x).El) (fun x => (normalizationTower 2).El (thirdTowerCode (B x)))
      (fun x => thirdTowerRetraction (B x))

theorem middle_tower_roundtrip (A : MiddleCode) (x : A.El) :
    (middleTowerRetraction A).decode ((middleTowerRetraction A).encode x) = x :=
  (middleTowerRetraction A).roundtrip x

theorem third_tower_roundtrip (A : ThirdCode) (x : A.El) :
    (thirdTowerRetraction A).decode ((thirdTowerRetraction A).encode x) = x :=
  (thirdTowerRetraction A).roundtrip x

/-- Realizability is pulled back through the checked carrier decoder. -/
noncomputable def thirdTowerType (A : ThirdCode) (C : A.El → Candidate) :
    TowerType (normalizationTower 2) :=
  ⟨thirdTowerCode A, fun x => C ((thirdTowerRetraction A).decode x)⟩

theorem thirdTowerType_realizes (A : ThirdCode) (C : A.El → Candidate) (x : A.El) :
    (thirdTowerType A C).realizes ((thirdTowerRetraction A).encode x) = C x := by
  exact congrArg C (third_tower_roundtrip A x)

/-- Source bound-three carrier substitution also holds after representation in
the reusable tower. This is a representation change, not a source-bound descent. -/
theorem thirdTowerCode_subst (hB : BoundedTyping 3 (A :: Γ) B (.srt sB))
    (ha : BoundedTyping 3 Γ a A) (hA : BoundedTyping 3 Γ A (.srt sA))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    thirdTowerCode (thirdShape Γ ρ δ (subst 0 a B) u f) =
      thirdTowerCode (thirdShape (A :: Γ) (push (shapeEval 3 1 Γ ρ a) ρ)
        (push (middleSemantics Γ ρ δ a).1 δ) B u f) := by
  rw [thirdShape_subst hB ha hA hρ hδ]

end Submission.Helpers
