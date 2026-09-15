import Submission.CarrierGridRepresentation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def CarrierFunction.toRetraction (F : CarrierFunction X Y Z) :
    CarrierRetraction ((x : X) → Y x) Z :=
  ⟨F.lambda, F.apply, fun f => funext (F.beta f)⟩

def CarrierRetraction.curry (X : Type) (Y : X → Type) (Z : (Σ x, Y x) → Type) :
    CarrierRetraction ((z : Σ x, Y x) → Z z) ((x : X) → (y : Y x) → Z ⟨x, y⟩) where
  encode f x y := f ⟨x, y⟩
  decode f z := f z.1 z.2
  roundtrip _ := rfl

/-- A finite, dependent sequence may draw each argument from a different
coordinate. Its branch structure is inductive even when a carrier is infinite. -/
inductive CarrierTelescope (S : Nat → CarrierSystem) where
  | nil
  | cons (i : Nat) (A : (S i).Code) : ((S i).El A → CarrierTelescope S) → CarrierTelescope S

def CarrierTelescope.El {S : Nat → CarrierSystem} : CarrierTelescope S → Type
  | .nil => Unit
  | .cons i A B => (x : (S i).El A) × (B x).El

def CarrierTelescope.point {S : Nat → CarrierSystem} : (T : CarrierTelescope S) → T.El
  | .nil => ()
  | .cons i A B => ⟨(S i).point A, (B ((S i).point A)).point⟩

def CarrierTelescope.Within {S : Nat → CarrierSystem} (e : Nat) : CarrierTelescope S → Prop
  | .nil => True
  | .cons i _ B => i ≤ e ∧ ∀ x, (B x).Within e

/-- All preceding coordinates are represented in the fixed quantifier index
before dependent quantification is performed. -/
noncomputable def carrierGridTelescopeCode (r e : Nat) (he : e < r + 1) :
    (T : CarrierTelescope (carrierGrid (r + 1))) → T.Within e →
    (T.El → (carrierGrid (r + 1) (e + 1)).Code) → (carrierGrid (r + 1) (e + 1)).Code
  | .nil, _, C => C ()
  | .cons i A B, h, C =>
    let R := carrierGridPrefixRepresentation (r + 1) i e h.1 he
    (carrierGridQuantifiers r e).code (R.code A) (fun x =>
      carrierGridTelescopeCode r e he (B ((R.values A).decode x)) (h.2 _)
        (fun y => C ⟨(R.values A).decode x, y⟩))

noncomputable def carrierGridTelescopeRetraction (r e : Nat) (he : e < r + 1) :
    (T : CarrierTelescope (carrierGrid (r + 1))) → (h : T.Within e) →
    (C : T.El → (carrierGrid (r + 1) (e + 1)).Code) →
    CarrierRetraction ((x : T.El) → (carrierGrid (r + 1) (e + 1)).El (C x))
      ((carrierGrid (r + 1) (e + 1)).El (carrierGridTelescopeCode r e he T h C))
  | .nil, _, C =>
    (CarrierFunction.singletonDomain () (inferInstanceAs (Subsingleton Unit))
      (fun x => (carrierGrid (r + 1) (e + 1)).El (C x))).toRetraction
  | .cons i A B, h, C =>
    let R := carrierGridPrefixRepresentation (r + 1) i e h.1 he
    let D := fun x => (y : (B x).El) → (carrierGrid (r + 1) (e + 1)).El (C ⟨x, y⟩)
    let E := fun x => (carrierGrid (r + 1) (e + 1)).El
      (carrierGridTelescopeCode r e he (B x) (h.2 x) (fun y => C ⟨x, y⟩))
    ((CarrierRetraction.curry ((carrierGrid (r + 1) i).El A) (fun x => (B x).El)
      (fun z => (carrierGrid (r + 1) (e + 1)).El (C z))).comp
        (CarrierRetraction.pi (R.values A) D E (fun x =>
          carrierGridTelescopeRetraction r e he (B x) (h.2 x) (fun y => C ⟨x, y⟩)))).comp
      (((carrierGridQuantifiers r e).functions (R.code A) (fun x =>
        carrierGridTelescopeCode r e he (B ((R.values A).decode x)) (h.2 _)
          (fun y => C ⟨(R.values A).decode x, y⟩))).toRetraction)

noncomputable def carrierGridTelescopeLambda (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (C : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (f : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (C x)) :
    (carrierGrid (r + 1) (e + 1)).El (carrierGridTelescopeCode r e he T h C) :=
  (carrierGridTelescopeRetraction r e he T h C).encode f

noncomputable def carrierGridTelescopeApply (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (C : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (f : (carrierGrid (r + 1) (e + 1)).El (carrierGridTelescopeCode r e he T h C))
    (x : T.El) : (carrierGrid (r + 1) (e + 1)).El (C x) :=
  (carrierGridTelescopeRetraction r e he T h C).decode f x

theorem carrierGrid_telescope_beta (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (C : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (f : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (C x)) (x : T.El) :
    carrierGridTelescopeApply r e he T h C (carrierGridTelescopeLambda r e he T h C f) x = f x :=
  congrFun ((carrierGridTelescopeRetraction r e he T h C).roundtrip f) x

noncomputable def carrierGridBinderCode (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code) : (carrierGrid (r + 1) (e + 1)).Code :=
  carrierGridTelescopeCode r e he T h (fun x => (carrierGridArrows (r + 1) (e + 1)).code (D x) (B x))

noncomputable def carrierGridBinderLambda (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (f : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) →
      (carrierGrid (r + 1) (e + 1)).El (B x)) :
    (carrierGrid (r + 1) (e + 1)).El (carrierGridBinderCode r e he T h D B) :=
  carrierGridTelescopeLambda r e he T h _
    (fun x => ((carrierGridArrows (r + 1) (e + 1)).functions (D x) (B x)).lambda (f x))

noncomputable def carrierGridBinderApply (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (f : (carrierGrid (r + 1) (e + 1)).El (carrierGridBinderCode r e he T h D B))
    (x : T.El) (y : (carrierGrid (r + 1) (e + 1)).El (D x)) :
    (carrierGrid (r + 1) (e + 1)).El (B x) :=
  ((carrierGridArrows (r + 1) (e + 1)).functions (D x) (B x)).apply
    (carrierGridTelescopeApply r e he T h _ f x) y

/-- A binder consumes its entire preceding semantic environment and its
current value. This beta law is uniform in the number of coordinates. -/
theorem carrierGrid_binder_beta (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (h : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (f : (x : T.El) → (carrierGrid (r + 1) (e + 1)).El (D x) →
      (carrierGrid (r + 1) (e + 1)).El (B x)) (x : T.El)
    (y : (carrierGrid (r + 1) (e + 1)).El (D x)) :
    carrierGridBinderApply r e he T h D B (carrierGridBinderLambda r e he T h D B f) x y = f x y := by
  unfold carrierGridBinderApply carrierGridBinderLambda
  rw [carrierGrid_telescope_beta, carrierGrid_arrow_beta]

end Submission.Helpers
