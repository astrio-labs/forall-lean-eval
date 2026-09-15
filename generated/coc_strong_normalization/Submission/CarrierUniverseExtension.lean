import Submission.CarrierGridImageFactorization

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Add a value whose carrier depends on the entire preceding telescope. -/
def CarrierTelescope.snoc {S : Nat → CarrierSystem} :
    (T : CarrierTelescope S) → (i : Nat) → (T.El → (S i).Code) → CarrierTelescope S
  | .nil, i, A => .cons i (A ()) (fun _ => .nil)
  | .cons j B C, i, A => .cons j B (fun x => (C x).snoc i (fun y => A ⟨x, y⟩))

def CarrierTelescope.snocEncode {S : Nat → CarrierSystem} :
    (T : CarrierTelescope S) → (i : Nat) → (A : T.El → (S i).Code) →
      ((x : T.El) × (S i).El (A x)) → (T.snoc i A).El
  | .nil, _, _, x => ⟨x.2, ()⟩
  | .cons _ _ C, i, A, x => ⟨x.1.1, (C x.1.1).snocEncode i (fun y => A ⟨x.1.1, y⟩) ⟨x.1.2, x.2⟩⟩

def CarrierTelescope.snocDecode {S : Nat → CarrierSystem} :
    (T : CarrierTelescope S) → (i : Nat) → (A : T.El → (S i).Code) →
      (T.snoc i A).El → ((x : T.El) × (S i).El (A x))
  | .nil, _, _, x => ⟨(), x.1⟩
  | .cons _ _ C, i, A, x =>
    let y := (C x.1).snocDecode i (fun y => A ⟨x.1, y⟩) x.2
    ⟨⟨x.1, y.1⟩, y.2⟩

theorem CarrierTelescope.snoc_roundtrip {S : Nat → CarrierSystem}
    (T : CarrierTelescope S) (i : Nat) (A : T.El → (S i).Code)
    (x : (x : T.El) × (S i).El (A x)) :
    T.snocDecode i A (T.snocEncode i A x) = x := by
  induction T with
  | nil => obtain ⟨⟨⟩, y⟩ := x; rfl
  | cons j B C ih =>
    obtain ⟨⟨x, y⟩, z⟩ := x
    simp only [snocEncode, snocDecode]
    erw [ih x (fun y => A ⟨x, y⟩) ⟨y, z⟩]

def CarrierTelescope.snocFunctions {S : Nat → CarrierSystem} (T : CarrierTelescope S)
    (i : Nat) (A : T.El → (S i).Code) (Y : Type) :
    CarrierRetraction ((x : T.El) → (S i).El (A x) → Y) ((T.snoc i A).El → Y) where
  encode f z := let x := T.snocDecode i A z; f x.1 x.2
  decode f x y := f (T.snocEncode i A ⟨x, y⟩)
  roundtrip f := by
    funext x y
    dsimp only
    erw [T.snoc_roundtrip i A ⟨x, y⟩]

theorem CarrierTelescope.snoc_all {S : Nat → CarrierSystem} {P : Nat → Prop}
    (T : CarrierTelescope S) (h : T.All P) (i : Nat) (hi : P i) (A : T.El → (S i).Code) :
    (T.snoc i A).All P := by
  induction T with
  | nil => exact ⟨hi, fun _ => True.intro⟩
  | cons j B C ih => exact ⟨h.1, fun x => ih x (h.2 x) _⟩

theorem CarrierTelescope.all_mono {S : Nat → CarrierSystem} {P Q : Nat → Prop}
    (T : CarrierTelescope S) (h : T.All P) (hPQ : ∀ i, P i → Q i) : T.All Q := by
  induction T with
  | nil => trivial
  | cons i A B ih => exact ⟨hPQ i h.1, fun x => ih x (h.2 x)⟩

/-- A universe can be extended by another dependent value at each available
column. The old telescope may have any finite length and may mix rows. -/
noncomputable def carrierGridUniverseExtend (r e : Nat) (he : e + 1 < r)
    (upper : Nat → Bool) (depth : Nat → Nat)
    (T : CarrierTelescope (carrierGridUniverseSources r upper depth))
    (h : T.All (fun i => depth i ≤ e)) (i : Nat) (hi : depth i ≤ e + 1)
    (A : T.El → (carrierGridUniverseSources r upper depth i).Code) :
    CarrierObject (carrierGrid (r + 1) (e + 2))
      ((x : T.El) → (carrierGridUniverseSources r upper depth i).El (A x) →
        (carrierGrid r (e + 2)).Code) :=
  CarrierObject.pullback (T.snocFunctions i A _)
    (carrierGridUniverseTelescope r (e + 1) he upper depth (T.snoc i A)
      (T.snoc_all (T.all_mono h (fun _ hi => by omega)) i hi A))

theorem carrierGrid_universe_extend_roundtrip (r e : Nat) (he : e + 1 < r)
    (upper : Nat → Bool) (depth : Nat → Nat)
    (T : CarrierTelescope (carrierGridUniverseSources r upper depth))
    (h : T.All (fun i => depth i ≤ e)) (i : Nat) (hi : depth i ≤ e + 1)
    (A : T.El → (carrierGridUniverseSources r upper depth i).Code)
    (C : (x : T.El) → (carrierGridUniverseSources r upper depth i).El (A x) →
      (carrierGrid r (e + 2)).Code) :
    (carrierGridUniverseExtend r e he upper depth T h i hi A).values.decode
      ((carrierGridUniverseExtend r e he upper depth T h i hi A).values.encode C) = C :=
  (carrierGridUniverseExtend r e he upper depth T h i hi A).roundtrip C

end Submission.Helpers
