import Submission.CarrierGridHorizontalFormation
import Submission.SecondLayerSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The first source coordinate satisfies the same formation predicate used
by every row and coordinate of the abstract grid. -/
theorem firstGridShape_formation (h : BoundedTyping (r + 3) Γ A (.srt s))
    (hρ : ShapeContext (.type (r + 1)) Γ ρ) :
    GridFormation (r + 2) 1 s (firstGridShape r Γ ρ A u) := by
  refine ⟨fun hs => firstGridShape_lower h (by change sortRank s < r + 2; omega), ?_⟩
  by_cases hs : sortRank s ≤ r + 2
  · have hk : min 1 ((r + 2) + 1 - sortRank s) = 1 := by omega
    rw [hk, firstGridShape_small h (by simpa only [sortRank] using hs) hρ]
    exact .small (.base _)
  · have hk : min 1 ((r + 2) + 1 - sortRank s) = 0 := by omega
    rw [hk]
    exact .base _

theorem UpperGridForm.grid {C : UpperGridCode r} (h : UpperGridForm r s C) :
    GridFormation (r + 3) 2 s C := by
  refine ⟨fun hs => h.lower (by omega), ?_⟩
  by_cases hs : sortRank s ≤ r + 2
  · obtain ⟨a, ha⟩ := h.arity hs
    have hk : min 2 ((r + 3) + 1 - sortRank s) = 2 := by omega
    rw [hk, ha]
    exact .small (.small (.base (r := r + 1) (d := 0) a))
  · by_cases hs' : sortRank s ≤ r + 3
    · obtain ⟨a, ha⟩ := h.small hs'
      have hk : min 2 ((r + 3) + 1 - sortRank s) = 1 := by omega
      rw [hk, ha]
      exact .small (.base a)
    · have hk : min 2 ((r + 3) + 1 - sortRank s) = 0 := by omega
      rw [hk]
      exact .base _

theorem upperGridSemantics_formation (h : BoundedTyping (r + 4) Γ A (.srt s))
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    GridFormation (r + 3) 2 s ((upperGridSemantics r Γ ρ δ A).2 u f) :=
  (upperGridSemantics_form h hρ).grid

theorem SecondLayerForm.grid {C : SecondLayerCode r} (h : SecondLayerForm r s C) :
    GridFormation (r + 4) 3 s C := by
  refine ⟨fun hs => h.lower (by omega), ?_⟩
  by_cases hs : sortRank s ≤ r + 2
  · obtain ⟨a, ha⟩ := h.arity hs
    have hk : min 3 ((r + 4) + 1 - sortRank s) = 3 := by omega
    rw [hk, ha]
    exact .small (.small (.small (.base (r := r + 1) (d := 0) a)))
  · by_cases hs' : sortRank s ≤ r + 3
    · obtain ⟨a, ha⟩ := h.smallTwo hs'
      have hk : min 3 ((r + 4) + 1 - sortRank s) = 2 := by omega
      rw [hk, ha]
      exact .small (.small (.base a))
    · by_cases hs'' : sortRank s ≤ r + 4
      · obtain ⟨a, ha⟩ := h.small hs''
        have hk : min 3 ((r + 4) + 1 - sortRank s) = 1 := by omega
        rw [hk, ha]
        exact .small (.base a)
      · have hk : min 3 ((r + 4) + 1 - sortRank s) = 0 := by omega
        rw [hk]
        exact .base _

/-- Source formation at the unchanged arbitrary bound `r + 5` now has a
coordinate-independent statement, ready for telescope composition. -/
theorem secondLayerSemantics_formation (h : BoundedTyping (r + 5) Γ A (.srt s))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) :
    GridFormation (r + 4) 3 s ((secondLayerSemantics r Γ ρ δ ε A).2 u f g) :=
  (secondLayerSemantics_form h hρ).grid

end Submission.Helpers
