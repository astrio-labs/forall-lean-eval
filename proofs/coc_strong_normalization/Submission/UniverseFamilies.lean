import Submission.RetractedFamilies

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- A lower type code crosses the first small inclusion and every additional
universe offset. -/
def universeOutputCodes (r d : Nat) : (k : Nat) →
    CarrierRetraction (carrierGrid r d).Code (carrierGrid (r + 1 + k) (d + 1 + k)).Code
  | 0 => ⟨LayerCode.small, LayerCode.asSmall, fun _ => rfl⟩
  | k + 1 => (universeOutputCodes r d k).comp ⟨LayerCode.small, LayerCode.asSmall, fun _ => rfl⟩

def universeOutputValues (r d : Nat) : (k : Nat) → (A : (carrierGrid r d).Code) →
    CarrierRetraction ((carrierGrid r d).El A)
      ((carrierGrid (r + 1 + k) (d + 1 + k)).El ((universeOutputCodes r d k).encode A))
  | 0, _ => CarrierRetraction.identity _
  | k + 1, A => universeOutputValues r d k A

def universeArgumentSystems (r k i : Nat) := carrierGrid (r + 1 + k) (i + 1 + k)

def universeArgumentRepresentation (r k i : Nat) :
    CarrierRepresentation (carrierGrid r i) (universeArgumentSystems r k i) :=
  ⟨(universeOutputCodes r i k).encode, universeOutputValues r i k⟩

noncomputable def UniversePrefix.arguments (P : UniversePrefix r d) (k : Nat) :
    CarrierRetraction P.El (TowerFamily (universeArgumentSystems r k)) :=
  P.telescope.valuesRetraction (universeArgumentRepresentation r k) P.ordered

def UniverseOutput (r d k : Nat) : Type :=
  if d ≤ r then (carrierGrid (r + 1 + k) (d + 1 + k)).Code else Candidate

def universeOutputs (r d k : Nat) : CarrierRetraction (UniversePayload r d) (UniverseOutput r d k) := by
  by_cases h : d ≤ r
  · simpa only [UniversePayload, UniverseOutput, if_pos h] using universeOutputCodes r d k
  · simpa only [UniversePayload, UniverseOutput, if_neg h] using CarrierRetraction.identity Candidate

theorem universeOutputCodes_image (r d k : Nat) (A : (carrierGrid r d).Code) :
    GridCodeImage (r + 1 + k) (d + 1 + k) (k + 1) ((universeOutputCodes r d k).encode A) := by
  induction k with
  | zero => exact .small (.base A)
  | succ k ih => exact .small ih

theorem universeOutputCodes_image_iff (r d k : Nat)
    (A : (carrierGrid (r + 1 + k) (d + 1 + k)).Code) :
    (universeOutputCodes r d k).encode ((universeOutputCodes r d k).decode A) = A ↔
      GridCodeImage (r + 1 + k) (d + 1 + k) (k + 1) A := by
  constructor
  · intro h; rw [← h]; exact universeOutputCodes_image r d k _
  · intro h
    induction k with
    | zero => exact h.small_eq.symm
    | succ k ih => exact (congrArg LayerCode.small (ih A.asSmall h.peel)).trans h.small_eq.symm

theorem universeOutputCodes_formed (r d k : Nat)
    (A : (carrierGrid (r + 1 + k) (d + 1 + k)).Code)
    (h : GridFormation (r + 1 + k) (d + 1 + k) (.type r) A) :
    (universeOutputCodes r d k).encode ((universeOutputCodes r d k).decode A) = A := by
  apply (universeOutputCodes_image_iff r d k A).mpr
  exact h.image.mono (by simp only [sortRank]; omega)

def UniversePrefix.Family (P : UniversePrefix r d) (k : Nat) :=
  {C : TowerFamily (universeArgumentSystems r k) → UniverseOutput r d k //
    FamilyAdmissible (P.arguments k) (universeOutputs r d k) C}

/-- A universe represents exactly the canonical families of the required
image depth. At its bottom these are candidate families, with no image loss. -/
noncomputable def UniversePrefix.familyObject (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat) :
    CarrierObject (carrierGrid (r + 1 + k) (d + k)) (P.Family k) :=
  CarrierObject.pullback ((P.arguments k).families (universeOutputs r d k)) (P.shiftObject hd k)

theorem UniversePrefix.family_roundtrip (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat)
    (C : P.Family k) :
    (P.familyObject hd k).values.decode ((P.familyObject hd k).values.encode C) = C :=
  (P.familyObject hd k).roundtrip C

end Submission.Helpers
