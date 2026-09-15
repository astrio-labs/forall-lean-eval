import Submission.FiberNormalization

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-!
The successor construction below separates two operations that must not be
confused: adjoining the universe of an existing collection of realized types,
and forming dependent carriers indexed by an already constructed carrier.
Both operations preserve smallness, and can be iterated over a natural number.
This is a carrier construction, not a claim that source universe bounds descend.
-/

/-- A small collection of codes with an inhabited carrier for every code. -/
structure CarrierSystem where
  Code : Type
  El : Code → Type
  point : (A : Code) → El A
  defaultCode : Code

/-- A realized type whose carrier belongs to a specified code system. -/
structure TowerType (S : CarrierSystem) where
  code : S.Code
  realizes : S.El code → Candidate

abbrev TowerType.Carrier {S : CarrierSystem} (A : TowerType S) : Type := S.El A.code

def TowerType.point {S : CarrierSystem} (A : TowerType S) : A.Carrier := S.point A.code

def TowerType.toRealizedType {S : CarrierSystem} (A : TowerType S) : RealizedType where
  Carrier := A.Carrier
  point := A.point
  realizes := A.realizes

def TowerType.default (S : CarrierSystem) : TowerType S := ⟨S.defaultCode, fun _ => Candidate.sn⟩

/-- Adding a universe does not identify it with any of its elements' carriers. -/
inductive UniverseCode (S : CarrierSystem) where
  | old : S.Code → UniverseCode S
  | codes : UniverseCode S
  | universe : UniverseCode S

def UniverseCode.El (S : CarrierSystem) : UniverseCode S → Type
  | .old A => S.El A
  | .codes => S.Code
  | .universe => TowerType S

def UniverseCode.point (S : CarrierSystem) : (A : UniverseCode S) → A.El S
  | .old A => S.point A
  | .codes => S.defaultCode
  | .universe => TowerType.default S

abbrev CarrierSystem.withUniverse (S : CarrierSystem) : CarrierSystem where
  Code := UniverseCode S
  El := UniverseCode.El S
  point := UniverseCode.point S
  defaultCode := .old S.defaultCode

def TowerType.intoUniverse {S : CarrierSystem} (A : TowerType S) :
    TowerType S.withUniverse := ⟨.old A.code, A.realizes⟩

def TowerType.universe (S : CarrierSystem) : TowerType S.withUniverse :=
  ⟨.universe, fun _ => Candidate.sn⟩

/-- Shape functions may have any finite simple order before they become
indices of the next dependent layer. -/
inductive SimpleCode (S : CarrierSystem) where
  | atom : S.Code → SimpleCode S
  | arrow : SimpleCode S → SimpleCode S → SimpleCode S

def SimpleCode.El (S : CarrierSystem) : SimpleCode S → Type
  | .atom A => S.El A
  | .arrow A B => A.El S → B.El S

def SimpleCode.point (S : CarrierSystem) : (A : SimpleCode S) → A.El S
  | .atom A => S.point A
  | .arrow _ B => fun _ => B.point S

abbrev CarrierSystem.simple (S : CarrierSystem) : CarrierSystem where
  Code := SimpleCode S
  El := SimpleCode.El S
  point := SimpleCode.point S
  defaultCode := .atom S.defaultCode

def TowerType.intoSimple {S : CarrierSystem} (A : TowerType S) :
    TowerType S.simple := ⟨.atom A.code, A.realizes⟩

/-- Dependency is permitted over a previously constructed carrier. The domain
of `all` does not refer to the new code type or its decoding function. -/
inductive DependentCode (S : CarrierSystem) where
  | old : S.Code → DependentCode S
  | arrow : DependentCode S → DependentCode S → DependentCode S
  | all (A : S.Code) : (S.El A → DependentCode S) → DependentCode S

def DependentCode.El (S : CarrierSystem) : DependentCode S → Type
  | .old A => S.El A
  | .arrow A B => A.El S → B.El S
  | .all _ B => (x : _) → (B x).El S

def DependentCode.point (S : CarrierSystem) : (A : DependentCode S) → A.El S
  | .old A => S.point A
  | .arrow _ B => fun _ => B.point S
  | .all _ B => fun x => (B x).point S

abbrev CarrierSystem.dependent (S : CarrierSystem) : CarrierSystem where
  Code := DependentCode S
  El := DependentCode.El S
  point := DependentCode.point S
  defaultCode := .old S.defaultCode

/-- A successor permits dependent carriers indexed by old values, old types,
old carrier codes, and finite simple functions built from these data. -/
abbrev CarrierSystem.next (S : CarrierSystem) : CarrierSystem :=
  S.withUniverse.simple.dependent

def TowerType.intoDependent {S : CarrierSystem} (A : TowerType S) :
    TowerType S.dependent := ⟨.old A.code, A.realizes⟩

def TowerType.raise {S : CarrierSystem} (A : TowerType S) : TowerType S.next :=
  A.intoUniverse.intoSimple.intoDependent

def TowerType.nextUniverse (S : CarrierSystem) : TowerType S.next :=
  (TowerType.universe S).intoSimple.intoDependent

/-- Iteration is ordinary recursion on data, with every carrier still in `Type`. -/
def CarrierSystem.iterate (S : CarrierSystem) : Nat → CarrierSystem
  | 0 => S
  | k + 1 => (S.iterate k).next

/-- The checked bound-two fiber carriers are the starting code system. -/
def fiberCarrierSystem : CarrierSystem where
  Code := FiberCode
  El := FiberCode.El
  point := FiberCode.point
  defaultCode := .small .unit

/-- The index counts carrier extensions. An interpretation of source bound
`k + 2` in this system is a further obligation, not part of this definition. -/
def normalizationTower (k : Nat) : CarrierSystem := fiberCarrierSystem.iterate k

def FiberType.toTowerType (A : FiberType) : TowerType fiberCarrierSystem :=
  ⟨A.code, A.realizes⟩

def TowerType.toFiberType (A : TowerType fiberCarrierSystem) : FiberType :=
  ⟨A.code, A.realizes⟩

@[simp] theorem FiberType.toTowerType_toFiberType (A : FiberType) :
    A.toTowerType.toFiberType = A := by cases A; rfl

@[simp] theorem TowerType.toFiberType_toTowerType (A : TowerType fiberCarrierSystem) :
    A.toFiberType.toTowerType = A := by cases A; rfl

/-- Values retain their carrier code; casts require equality of codes. -/
structure TowerValue (S : CarrierSystem) where
  code : S.Code
  data : S.El code

noncomputable def TowerValue.cast {S : CarrierSystem} (v : TowerValue S) (A : S.Code) :
    S.El A := by
  classical
  exact if h : v.code = A then h ▸ v.data else S.point A

@[simp] theorem TowerValue.cast_mk {S : CarrierSystem} (A : S.Code) (a : S.El A) :
    (TowerValue.mk A a).cast A = a := by simp only [TowerValue.cast, ↓reduceDIte]

theorem TowerValue.mk_cast {S : CarrierSystem} (v : TowerValue S) {A : S.Code}
    (h : v.code = A) : TowerValue.mk (S := S) A (v.cast A) = v := by
  cases v with
  | mk B b => cases h; rw [TowerValue.cast_mk]

def TowerType.value {S : CarrierSystem} (A : TowerType S) (a : A.Carrier) : TowerValue S :=
  ⟨A.code, a⟩

def TowerValue.encode {S : CarrierSystem} (A : TowerType S) : TowerValue S.next :=
  (TowerType.nextUniverse S).value A

noncomputable def TowerValue.decode {S : CarrierSystem} (v : TowerValue S.next) : TowerType S :=
  v.cast (TowerType.nextUniverse S).code

/-- Every old realized type, including its candidate family, survives encoding. -/
@[simp] theorem TowerValue.decode_encode {S : CarrierSystem} (A : TowerType S) :
    (TowerValue.encode A).decode = A := TowerValue.cast_mk _ _

theorem TowerValue.encode_decode {S : CarrierSystem} (v : TowerValue S.next)
    (h : v.code = (TowerType.nextUniverse S).code) :
    TowerValue.encode v.decode = v := v.mk_cast h

/-- Universe encoding is faithful at every finite stage of the tower. -/
theorem tower_universe_roundtrip (k : Nat) (A : TowerType (normalizationTower k)) :
    (TowerValue.encode A).decode = A := TowerValue.decode_encode A

theorem tower_universe_injective (k : Nat)
    (A B : TowerType (normalizationTower k))
    (h : TowerValue.encode A = TowerValue.encode B) : A = B := by
  have he := congrArg TowerValue.decode h
  simpa only [TowerValue.decode_encode] using he

/-- The first successor represents precisely the existing fiber type data. -/
theorem fiber_universe_roundtrip (A : FiberType) :
    (TowerValue.encode A.toTowerType).decode.toFiberType = A := by
  rw [TowerValue.decode_encode, FiberType.toTowerType_toFiberType]

end Submission.Helpers
