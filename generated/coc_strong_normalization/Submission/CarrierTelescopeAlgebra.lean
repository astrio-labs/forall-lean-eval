import Submission.CarrierUniverseIteration

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A telescope uses only indices for which the supplied representation exists. -/
def CarrierTelescope.All {V : Nat → CarrierSystem} (P : Nat → Prop) : CarrierTelescope V → Prop
  | .nil => True
  | .cons i _ B => P i ∧ ∀ x, (B x).All P

/-- Dependent carrier objects can be abstracted over a telescope of any finite
length. Every binder uses its own checked representation into the quantifier
index, so no equality of source carriers is assumed. -/
noncomputable def CarrierTelescope.representPi {V : Nat → CarrierSystem} {I S : CarrierSystem}
    {P : Nat → Prop} (Q : CarrierQuantifiers I S)
    (R : ∀ i, P i → CarrierRepresentation (V i) I) :
    (T : CarrierTelescope V) → T.All P → (X : T.El → Type) →
      ((x : T.El) → CarrierObject S (X x)) → CarrierObject S ((x : T.El) → X x)
  | .nil, _, X, O => CarrierObject.pullback
      ((CarrierFunction.singletonDomain () (inferInstanceAs (Subsingleton Unit)) X).toRetraction) (O ())
  | .cons i A B, h, X, O =>
    CarrierObject.pullback (CarrierRetraction.curry ((V i).El A) (fun x => (B x).El) X)
      (Q.representPi ((R i h.1).code A) ((R i h.1).values A) (fun x =>
        (B x).representPi Q R (h.2 x) (fun y => X ⟨x, y⟩) (fun y => O ⟨x, y⟩)))

theorem CarrierTelescope.representPi_roundtrip {V : Nat → CarrierSystem} {I S : CarrierSystem}
    {P : Nat → Prop} (Q : CarrierQuantifiers I S) (R : ∀ i, P i → CarrierRepresentation (V i) I)
    (T : CarrierTelescope V) (h : T.All P) (X : T.El → Type) (O : (x : T.El) → CarrierObject S (X x))
    (f : (x : T.El) → X x) :
    (T.representPi Q R h X O).values.decode ((T.representPi Q R h X O).values.encode f) = f :=
  (T.representPi Q R h X O).roundtrip f

/-- The old numerical bound is the special case of the general index predicate. -/
theorem CarrierTelescope.within_all {V : Nat → CarrierSystem} (T : CarrierTelescope V) (e : Nat) :
    T.Within e ↔ T.All (fun i => i ≤ e) := by
  induction T with
  | nil => rfl
  | cons i A B ih =>
    change (i ≤ e ∧ ∀ x, (B x).Within e) ↔ (i ≤ e ∧ ∀ x, (B x).All (fun i => i ≤ e))
    exact and_congr_right (fun _ => forall_congr' (fun x => ih x))

end Submission.Helpers
