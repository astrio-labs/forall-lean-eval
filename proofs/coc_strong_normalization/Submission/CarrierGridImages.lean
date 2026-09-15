import Submission.CarrierUniverseTelescope

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Exact membership in an iterated small-code image. The index records
semantic code embeddings only; it says nothing about a source typing bound. -/
inductive GridCodeImage : (r d k : Nat) → (carrierGrid r d).Code → Prop where
  | base {r d : Nat} (A : (carrierGrid r d).Code) : GridCodeImage r d 0 A
  | small {r d k : Nat} {A : (carrierGrid r d).Code} :
      GridCodeImage r d k A → GridCodeImage (r + 1) (d + 1) (k + 1) (.small A)

theorem GridCodeImage.indices (h : GridCodeImage r d k A) : k ≤ r ∧ k ≤ d := by
  induction h with
  | base => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | small h ih => exact ⟨Nat.succ_le_succ ih.1, Nat.succ_le_succ ih.2⟩

theorem GridCodeImage.mono (h : GridCodeImage r d k A) (hl : l ≤ k) : GridCodeImage r d l A := by
  induction h generalizing l with
  | base A =>
    have he : l = 0 := by omega
    subst l
    exact .base A
  | small h ih =>
    cases l with
    | zero => exact .base _
    | succ l => exact .small (ih (Nat.le_of_succ_le_succ hl))

theorem GridCodeImage.peel {A : (carrierGrid (r + 1) (d + 1)).Code}
    (h : GridCodeImage (r + 1) (d + 1) (k + 1) A) : GridCodeImage r d k A.asSmall := by
  cases h with
  | small h => exact h

theorem GridCodeImage.small_eq {A : (carrierGrid (r + 1) (d + 1)).Code}
    (h : GridCodeImage (r + 1) (d + 1) (k + 1) A) : A = .small A.asSmall := by
  cases h with
  | small h => rfl

theorem GridCodeImage.one_iff {A : (carrierGrid (r + 1) (d + 1)).Code} :
    GridCodeImage (r + 1) (d + 1) 1 A ↔ A.IsSmall := by
  constructor
  · intro h; exact ⟨_, h.small_eq⟩
  · rintro ⟨a, rfl⟩; exact .small (.base a)

theorem gridCodeImage_default (hr : k ≤ r) (hd : k ≤ d) :
    GridCodeImage r d k (carrierGrid r d).defaultCode := by
  induction k generalizing r d with
  | zero => exact .base _
  | succ k ih =>
    cases r with
    | zero => omega
    | succ r =>
      cases d with
      | zero => omega
      | succ d => exact .small (ih (by omega) (by omega))

/-- Compact arrows preserve every exact image depth, uniformly across the grid. -/
theorem gridCodeImage_arrow (hA : GridCodeImage r d k A) (hB : GridCodeImage r d k B) :
    GridCodeImage r d k ((carrierGridArrows r d).code A B) := by
  induction hA with
  | base A => exact .base _
  | @small r d k A hA ih =>
    cases hB with
    | @small _ _ _ B hB =>
      rw [carrierGrid_arrow_small]
      exact .small (ih hB)

/-- Dependent quantification also preserves every image depth. The row
inequality excludes the free bottom-row quantifier, whose data cannot be
replaced by an arbitrary smaller carrier. -/
theorem gridCodeImage_all (hk : k ≤ r)
    (A : (carrierGrid (r + 1) d).Code)
    (B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code)
    (hA : GridCodeImage (r + 1) d k A)
    (hB : ∀ x, GridCodeImage (r + 1) (d + 1) k (B x)) :
    GridCodeImage (r + 1) (d + 1) k ((carrierGridQuantifiers r d).code A B) := by
  induction k generalizing r d with
  | zero => exact .base _
  | succ k ih =>
    cases r with
    | zero => omega
    | succ r =>
      cases d with
      | zero => have hi := hA.indices; omega
      | succ d =>
        cases hA with
        | @small _ _ _ A hA =>
          have he : B = fun x => .small (B x).asSmall := funext (fun x => (hB x).small_eq)
          erw [he, carrierGrid_all_small r d]
          exact .small (ih (by omega) A (fun x => (B x).asSmall) hA (fun x => (hB x).peel))

theorem gridCodeImage_pi (hk : k ≤ r)
    (A : (carrierGrid (r + 1) d).Code)
    (D B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code)
    (hA : GridCodeImage (r + 1) d k A)
    (hD : ∀ x, GridCodeImage (r + 1) (d + 1) k (D x))
    (hB : ∀ x, GridCodeImage (r + 1) (d + 1) k (B x)) :
    GridCodeImage (r + 1) (d + 1) k
      ((carrierGridQuantifiers r d).pi (carrierGridArrows (r + 1) (d + 1)) A D B) :=
  gridCodeImage_all hk A _ hA (fun x => gridCodeImage_arrow (hD x) (hB x))

end Submission.Helpers
