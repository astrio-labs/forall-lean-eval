import Submission.CarrierUniverseExtension

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Universe arguments occur in increasing coordinate order. In particular,
the bottom coordinate can only be the final argument. -/
def CarrierTelescope.Ordered {S : Nat → CarrierSystem} (lo hi : Nat) : CarrierTelescope S → Prop
  | .nil => True
  | .cons i _ B => lo ≤ i ∧ i < hi ∧ ∀ x, (B x).Ordered (i + 1) hi

theorem CarrierTelescope.Ordered.all {S : Nat → CarrierSystem} {T : CarrierTelescope S}
    (h : T.Ordered lo hi) : T.All (fun i => i < hi) := by
  induction T generalizing lo with
  | nil => trivial
  | cons i A B ih => exact ⟨h.2.1, fun x => ih x (h.2.2 x)⟩

theorem CarrierTelescope.Ordered.empty {S : Nat → CarrierSystem} {T : CarrierTelescope S}
    (h : T.Ordered lo hi) (hh : hi ≤ lo) : T = .nil := by
  cases T with
  | nil => rfl
  | cons i A B => have h1 := h.1; have h2 := h.2.1; omega

theorem CarrierTelescope.Ordered.snoc {S : Nat → CarrierSystem} {T : CarrierTelescope S}
    (h : T.Ordered lo hi) (hl : lo ≤ hi) (A : T.El → (S hi).Code) :
    (T.snoc hi A).Ordered lo (hi + 1) := by
  induction T generalizing lo with
  | nil => exact ⟨hl, Nat.lt_succ_self _, fun _ => True.intro⟩
  | cons i B C ih =>
    have hh := h.2.1
    exact ⟨h.1, by omega, fun x => ih x (h.2.2 x) (by omega) _⟩

/-- A prefix describes the part of a lower-row type already decoded from
preceding universe values. It carries no source typing or SN assumption. -/
structure UniversePrefix (r d : Nat) where
  telescope : CarrierTelescope (carrierGrid r)
  ordered : telescope.Ordered 0 d

def UniversePrefix.El (P : UniversePrefix r d) : Type := P.telescope.El

def UniversePrefix.empty (r : Nat) : UniversePrefix r 0 := ⟨.nil, True.intro⟩

def UniversePrefix.next (P : UniversePrefix r d) (A : P.El → (carrierGrid r d).Code) :
    UniversePrefix r (d + 1) :=
  ⟨P.telescope.snoc d A, P.ordered.snoc (Nat.zero_le _) A⟩

def UniversePrefix.nextValues (P : UniversePrefix r d) (A : P.El → (carrierGrid r d).Code) :
    CarrierRetraction ((x : P.El) × (carrierGrid r d).El (A x)) (P.next A).El :=
  ⟨P.telescope.snocEncode d A, P.telescope.snocDecode d A, P.telescope.snoc_roundtrip d A⟩

theorem UniversePrefix.next_roundtrip (P : UniversePrefix r d)
    (A : P.El → (carrierGrid r d).Code) (x : P.El) (y : (carrierGrid r d).El (A x)) :
    (P.nextValues A).decode ((P.nextValues A).encode ⟨x, y⟩) = ⟨x, y⟩ :=
  (P.nextValues A).roundtrip _

end Submission.Helpers
