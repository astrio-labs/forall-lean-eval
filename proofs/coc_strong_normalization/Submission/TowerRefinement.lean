import Submission.TowerCandidates

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- One source argument has an upper value `x` and lower data `y`. Both
components are consumed by a single source application. The output carrier
depends on `x`; its candidate may also depend on `y`. -/
def TowerType.refinementPi {S : CarrierSystem} (a : S.Code)
    (D : S.El a → TowerType S.dependent) (b : S.El a → DependentCode S)
    (B : (x : S.El a) → (D x).Carrier → (b x).El S → Candidate) :
    TowerType S.dependent where
  code := .all a (fun x => .arrow (D x).code (b x))
  realizes f := Candidate.inter (fun z : (x : S.El a) × (D x).Carrier =>
    ((D z.1).realizes z.2).arrow (B z.1 z.2 (f z.1 z.2)))

theorem TowerType.refinementPi_apply {S : CarrierSystem} (a : S.Code)
    (D : S.El a → TowerType S.dependent) (b : S.El a → DependentCode S)
    (B : (x : S.El a) → (D x).Carrier → (b x).El S → Candidate)
    {f : (TowerType.refinementPi a D b B).Carrier} {x : S.El a} {y : (D x).Carrier}
    (hf : ((TowerType.refinementPi a D b B).realizes f).contains t)
    (ha : ((D x).realizes y).contains arg) :
    (B x y (f x y)).contains (.app t arg) := (hf.2 ⟨x, y⟩).2 arg ha

theorem TowerType.refinementPi_lambda {S : CarrierSystem} (a : S.Code)
    (D : S.El a → TowerType S.dependent) (b : S.El a → DependentCode S)
    (B : (x : S.El a) → (D x).Carrier → (b x).El S → Candidate)
    (f : (TowerType.refinementPi a D b B).Carrier) (hC : SN C)
    (hb : ∀ x y arg, ((D x).realizes y).contains arg →
      (B x y (f x y)).contains (subst 0 arg body)) :
    ((TowerType.refinementPi a D b B).realizes f).contains (.lam C body) := by
  have h (z : (x : S.El a) × (D x).Carrier) :=
    Candidate.lambda ((D z.1).realizes z.2) (B z.1 z.2 (f z.1 z.2)) hC (hb z.1 z.2)
  exact ⟨(h ⟨S.point a, (D (S.point a)).point⟩).1, h⟩

noncomputable def TowerValue.refinementLambda {S : CarrierSystem} (a : S.Code)
    (D B : S.El a → DependentCode S)
    (f : S.El a → TowerValue S.dependent → TowerValue S.dependent) :
    TowerValue S.dependent :=
  ⟨.all a (fun x => .arrow (D x) (B x)), fun x y => (f x ⟨D x, y⟩).cast (B x)⟩

noncomputable def TowerValue.refinementApply {S : CarrierSystem} (a : S.Code)
    (D B : S.El a → DependentCode S) (f : TowerValue S.dependent)
    (x : S.El a) (y : TowerValue S.dependent) : TowerValue S.dependent :=
  ⟨B x, f.cast (.all a (fun x => .arrow (D x) (B x))) x (y.cast (D x))⟩

theorem TowerValue.refinementBeta {S : CarrierSystem} (a : S.Code)
    (D B : S.El a → DependentCode S)
    (f : S.El a → TowerValue S.dependent → TowerValue S.dependent)
    (x : S.El a) (y : TowerValue S.dependent)
    (hy : y.code = D x) (hf : (f x y).code = B x) :
    TowerValue.refinementApply a D B (TowerValue.refinementLambda a D B f) x y =
      f x y := by
  unfold TowerValue.refinementApply TowerValue.refinementLambda
  erw [TowerValue.cast_mk]
  rw [y.mk_cast hy]
  exact (f x y).mk_cast hf

/-- The candidate atom is retained when further universes and carriers are added. -/
structure CandidateAtom (S : CarrierSystem) where
  code : S.Code
  encode : Candidate → S.El code
  decode : S.El code → Candidate
  decode_encode : ∀ C, decode (encode C) = C
  encode_decode : ∀ x, encode (decode x) = x

def CandidateAtom.raise {S : CarrierSystem} (p : CandidateAtom S) : CandidateAtom S.next where
  code := .old (.atom (.old p.code))
  encode := p.encode
  decode := p.decode
  decode_encode := p.decode_encode
  encode_decode := p.encode_decode

def fiberCandidateAtom : CandidateAtom fiberCarrierSystem where
  code := .small .prop
  encode := id
  decode := id
  decode_encode _ := rfl
  encode_decode _ := rfl

def towerCandidateAtom : (k : Nat) → CandidateAtom (normalizationTower k)
  | 0 => fiberCandidateAtom
  | k + 1 => (towerCandidateAtom k).raise

/-- Once an upper carrier code is fixed, the entire lower candidate family has
a code. No assumption that this carrier is a singleton is used. -/
def CandidateAtom.familyCode {S : CarrierSystem} (p : CandidateAtom S) (a : S.Code) :
    DependentCode S := .arrow (.old a) (.old p.code)

def CandidateAtom.encodeFamily {S : CarrierSystem} (p : CandidateAtom S) (a : S.Code)
    (C : S.El a → Candidate) : TowerValue S.dependent :=
  ⟨p.familyCode a, fun x => p.encode (C x)⟩

noncomputable def CandidateAtom.decodeFamily {S : CarrierSystem} (p : CandidateAtom S)
    (a : S.Code) (v : TowerValue S.dependent) : S.El a → Candidate :=
  fun x => p.decode (v.cast (p.familyCode a) x)

theorem CandidateAtom.decode_encode_family {S : CarrierSystem} (p : CandidateAtom S)
    (a : S.Code) (C : S.El a → Candidate) :
    p.decodeFamily a (p.encodeFamily a C) = C := by
  funext x
  unfold CandidateAtom.decodeFamily CandidateAtom.encodeFamily
  erw [TowerValue.cast_mk]
  exact p.decode_encode (C x)

theorem CandidateAtom.encode_decode_family {S : CarrierSystem} (p : CandidateAtom S)
    (a : S.Code) (v : TowerValue S.dependent) (hv : v.code = p.familyCode a) :
    p.encodeFamily a (p.decodeFamily a v) = v := by
  unfold CandidateAtom.encodeFamily CandidateAtom.decodeFamily
  have he : (fun x => p.encode (p.decode (v.cast (p.familyCode a) x))) =
      v.cast (p.familyCode a) := by
    funext x
    exact p.encode_decode _
  rw [he]
  exact v.mk_cast hv

/-- Exact universe decoding for candidate families is uniform in tower depth. -/
theorem tower_candidate_family_roundtrip (k : Nat)
    (a : (normalizationTower k).Code)
    (C : (normalizationTower k).El a → Candidate) :
    (towerCandidateAtom k).decodeFamily a ((towerCandidateAtom k).encodeFamily a C) = C :=
  (towerCandidateAtom k).decode_encode_family a C

theorem tower_candidate_family_injective (k : Nat)
    (a : (normalizationTower k).Code)
    (C D : (normalizationTower k).El a → Candidate)
    (h : (towerCandidateAtom k).encodeFamily a C =
      (towerCandidateAtom k).encodeFamily a D) : C = D := by
  have he := congrArg ((towerCandidateAtom k).decodeFamily a) h
  simpa only [CandidateAtom.decode_encode_family] using he

/-- At every successor, a single source binder may consume both an upper value
and lower data. This is the product operation used by the fiber model. -/
theorem tower_refinement_abstraction (k : Nat)
    (a : (normalizationTower k).withUniverse.simple.Code)
    (D : (normalizationTower k).withUniverse.simple.El a → TowerType (normalizationTower (k + 1)))
    (b : (normalizationTower k).withUniverse.simple.El a →
      DependentCode (normalizationTower k).withUniverse.simple)
    (B : (x : (normalizationTower k).withUniverse.simple.El a) →
      (D x).Carrier → (b x).El (normalizationTower k).withUniverse.simple → Candidate)
    (f : (TowerType.refinementPi a D b B).Carrier) (hC : SN C)
    (hb : ∀ x y arg, ((D x).realizes y).contains arg →
      (B x y (f x y)).contains (subst 0 arg body)) :
    ((TowerType.refinementPi a D b B).realizes f).contains (.lam C body) :=
  TowerType.refinementPi_lambda a D b B f hC hb

end Submission.Helpers
