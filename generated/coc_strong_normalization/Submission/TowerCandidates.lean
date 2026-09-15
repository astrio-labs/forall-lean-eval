import Submission.TowerCodes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A dependent product over an old carrier has a code in the completion.
The family may change both its carrier code and its realizability predicate. -/
def TowerType.depPi {S : CarrierSystem} (A : TowerType S)
    (B : A.Carrier → TowerType S.dependent) : TowerType S.dependent where
  code := .all A.code (fun x => (B x).code)
  realizes f := Candidate.inter (fun x =>
    (A.realizes x).arrow ((B x).realizes (f x)))

theorem TowerType.depPi_apply {S : CarrierSystem} (A : TowerType S)
    (B : A.Carrier → TowerType S.dependent)
    {f : (A.depPi B).Carrier} {x : A.Carrier}
    (hf : ((A.depPi B).realizes f).contains t) (hx : (A.realizes x).contains a) :
    ((B x).realizes (f x)).contains (.app t a) := (hf.2 x).2 a hx

theorem TowerType.depPi_lambda {S : CarrierSystem} (A : TowerType S)
    (B : A.Carrier → TowerType S.dependent) (f : (A.depPi B).Carrier)
    (hD : SN D) (hb : ∀ x a, (A.realizes x).contains a →
      ((B x).realizes (f x)).contains (subst 0 a b)) :
    ((A.depPi B).realizes f).contains (.lam D b) := by
  have h (x : A.Carrier) := Candidate.lambda _ _ hD (hb x)
  exact ⟨(h A.point).1, h⟩

/-- Functions within one new stage may have arbitrary argument-dependent
candidate predicates while their codomain carrier is fixed. -/
def TowerType.shapePi {S : CarrierSystem} (A : TowerType S.dependent)
    (b : DependentCode S)
    (B : A.Carrier → S.dependent.El b → Candidate) : TowerType S.dependent where
  code := .arrow A.code b
  realizes f := Candidate.inter (fun x => (A.realizes x).arrow (B x (f x)))

theorem TowerType.shapePi_apply {S : CarrierSystem} (A : TowerType S.dependent)
    (b : DependentCode S) (B : A.Carrier → S.dependent.El b → Candidate)
    {f : (A.shapePi b B).Carrier} {x : A.Carrier}
    (hf : ((A.shapePi b B).realizes f).contains t) (hx : (A.realizes x).contains a) :
    (B x (f x)).contains (.app t a) := (hf.2 x).2 a hx

theorem TowerType.shapePi_lambda {S : CarrierSystem} (A : TowerType S.dependent)
    (b : DependentCode S) (B : A.Carrier → S.dependent.El b → Candidate)
    (f : (A.shapePi b B).Carrier) (hD : SN D)
    (hb : ∀ x a, (A.realizes x).contains a → (B x (f x)).contains (subst 0 a body)) :
    ((A.shapePi b B).realizes f).contains (.lam D body) := by
  have h (x : A.Carrier) := Candidate.lambda _ _ hD (hb x)
  exact ⟨(h A.point).1, h⟩

/-- Quantification over all old realized types is available in the successor. -/
def TowerType.universePi (S : CarrierSystem)
    (B : TowerType S → TowerType S.next) : TowerType S.next :=
  (TowerType.universe S).intoSimple.depPi B

theorem TowerType.universePi_apply (S : CarrierSystem)
    (B : TowerType S → TowerType S.next)
    {f : (TowerType.universePi S B).Carrier} {A : TowerType S}
    (hf : ((TowerType.universePi S B).realizes f).contains t) (ha : SN a) :
    ((B A).realizes (f A)).contains (.app t a) :=
  TowerType.depPi_apply (TowerType.universe S).intoSimple B hf ha

theorem TowerType.universePi_lambda (S : CarrierSystem)
    (B : TowerType S → TowerType S.next) (f : (TowerType.universePi S B).Carrier)
    (hD : SN D) (hb : ∀ A a, SN a →
      ((B A).realizes (f A)).contains (subst 0 a body)) :
    ((TowerType.universePi S B).realizes f).contains (.lam D body) :=
  TowerType.depPi_lambda (TowerType.universe S).intoSimple B f hD hb

/-- Dependent abstraction stores the exact family of output carrier codes. -/
noncomputable def TowerValue.depLambda {S : CarrierSystem} (A : S.Code)
    (B : S.El A → DependentCode S)
    (f : (x : S.El A) → TowerValue S.dependent) : TowerValue S.dependent :=
  ⟨.all A B, fun x => (f x).cast (B x)⟩

noncomputable def TowerValue.depApply {S : CarrierSystem} (A : S.Code)
    (B : S.El A → DependentCode S)
    (f : TowerValue S.dependent) (x : S.El A) : TowerValue S.dependent :=
  ⟨B x, f.cast (.all A B) x⟩

theorem TowerValue.depBeta {S : CarrierSystem} (A : S.Code)
    (B : S.El A → DependentCode S) (f : S.El A → TowerValue S.dependent)
    (x : S.El A) (hf : (f x).code = B x) :
    TowerValue.depApply A B (TowerValue.depLambda A B f) x = f x := by
  unfold TowerValue.depApply TowerValue.depLambda
  erw [TowerValue.cast_mk]
  exact (f x).mk_cast hf

theorem TowerValue.depLambda_congr {S : CarrierSystem} (A : S.Code)
    (B : S.El A → DependentCode S) (f g : S.El A → TowerValue S.dependent)
    (h : ∀ x, f x = g x) :
    TowerValue.depLambda A B f = TowerValue.depLambda A B g := by
  rw [funext h]

theorem TowerType.depPi_value_apply {S : CarrierSystem} (A : TowerType S)
    (B : A.Carrier → TowerType S.dependent) (f : (A.depPi B).Carrier)
    (x : A.Carrier) :
    TowerValue.depApply A.code (fun x => (B x).code) ((A.depPi B).value f) x =
      (B x).value (f x) := by
  unfold TowerValue.depApply TowerType.value
  change TowerValue.mk (S := S.dependent) (B x).code
    ((TowerValue.mk (S := S.dependent) (.all A.code (fun x => (B x).code)) f).cast
      (.all A.code (fun x => (B x).code)) x) = _
  erw [TowerValue.cast_mk]

/-- The universe's full lower type data is substituted before choosing the
output carrier. This is not replacement by a singleton upper shape. -/
noncomputable def TowerValue.universeApply {S : CarrierSystem}
    (B : TowerType S → TowerType S.next) (f a : TowerValue S.next) : TowerValue S.next :=
  TowerValue.depApply (S := S.withUniverse.simple) (.atom .universe) (fun A => (B A).code) f a.decode

noncomputable def TowerValue.universeLambda {S : CarrierSystem}
    (B : TowerType S → TowerType S.next) (f : TowerType S → TowerValue S.next) :
    TowerValue S.next :=
  TowerValue.depLambda (S := S.withUniverse.simple) (.atom .universe) (fun A => (B A).code) f

theorem TowerValue.universeBeta {S : CarrierSystem}
    (B : TowerType S → TowerType S.next) (f : TowerType S → TowerValue S.next)
    (A : TowerType S) (hf : (f A).code = (B A).code) :
    TowerValue.universeApply B (TowerValue.universeLambda B f) (TowerValue.encode A) =
      f A := by
  unfold TowerValue.universeApply TowerValue.universeLambda
  rw [TowerValue.decode_encode]
  exact TowerValue.depBeta (S := S.withUniverse.simple) (.atom .universe)
    (fun A => (B A).code) f A hf

theorem TowerType.universePi_value_apply {S : CarrierSystem}
    (B : TowerType S → TowerType S.next) (f : (TowerType.universePi S B).Carrier)
    (A : TowerType S) :
    TowerValue.universeApply B ((TowerType.universePi S B).value f) (TowerValue.encode A) =
      (B A).value (f A) := by
  unfold TowerValue.universeApply
  rw [TowerValue.decode_encode]
  exact TowerType.depPi_value_apply (TowerType.universe S).intoSimple B f A

/-- A family with varying carriers already exists at each successor: the
universe-indexed product of the types themselves. -/
def TowerType.universalElements (S : CarrierSystem) : TowerType S.next :=
  TowerType.universePi S TowerType.raise

theorem tower_dependent_application (k : Nat)
    (B : TowerType (normalizationTower k) → TowerType (normalizationTower (k + 1)))
    {f : (TowerType.universePi (normalizationTower k) B).Carrier}
    {A : TowerType (normalizationTower k)}
    (hf : ((TowerType.universePi (normalizationTower k) B).realizes f).contains t)
    (ha : SN a) : ((B A).realizes (f A)).contains (.app t a) :=
  TowerType.universePi_apply (normalizationTower k) B hf ha

theorem tower_dependent_abstraction (k : Nat)
    (B : TowerType (normalizationTower k) → TowerType (normalizationTower (k + 1)))
    (f : (TowerType.universePi (normalizationTower k) B).Carrier)
    (hD : SN D) (hb : ∀ A a, SN a →
      ((B A).realizes (f A)).contains (subst 0 a body)) :
    ((TowerType.universePi (normalizationTower k) B).realizes f).contains (.lam D body) :=
  TowerType.universePi_lambda (normalizationTower k) B f hD hb

theorem tower_dependent_beta (k : Nat)
    (B : TowerType (normalizationTower k) → TowerType (normalizationTower (k + 1)))
    (f : TowerType (normalizationTower k) → TowerValue (normalizationTower (k + 1)))
    (A : TowerType (normalizationTower k)) (hf : (f A).code = (B A).code) :
    TowerValue.universeApply B (TowerValue.universeLambda B f) (TowerValue.encode A) =
      f A := TowerValue.universeBeta B f A hf

end Submission.Helpers
