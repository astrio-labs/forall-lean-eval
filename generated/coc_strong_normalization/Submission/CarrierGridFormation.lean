import Submission.CarrierGridImages

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Source-universe formation has a uniform description at every coordinate:
strictly lower universes are terminal, and all others occupy the exact image
depth dictated by the difference from the finite source bound. -/
structure GridFormation (r d : Nat) (s : Srt) (A : (carrierGrid r d).Code) : Prop where
  lower : sortRank s + d < r + 1 → A = (carrierGrid r d).defaultCode
  image : GridCodeImage r d (min d (r + 1 - sortRank s)) A

theorem gridFormation_default (hd : d ≤ r) (s : Srt) :
    GridFormation r d s (carrierGrid r d).defaultCode :=
  ⟨fun _ => rfl, gridCodeImage_default (Nat.le_trans (Nat.min_le_left _ _) hd) (Nat.min_le_left _ _)⟩

theorem gridRule_domain (h : Rl sA sB sC) : sC = .prop ∨ sortRank sA ≤ sortRank sC := by
  cases sC with
  | prop => exact .inl rfl
  | type j => exact .inr (rule_predicative_domain h)

/-- Arrow formation preserves the original impredicative and predicative
universe rules at every coordinate. -/
theorem gridFormation_arrow (hd : d ≤ r) (hr : Rl sA sB sC)
    (hA : GridFormation r d sA A) (hB : GridFormation r d sB B) :
    GridFormation r d sC ((carrierGridArrows r d).code A B) := by
  have hb := rule_codomain_le hr
  have hl (h : sortRank sC + d < r + 1) :
      (carrierGridArrows r d).code A B = (carrierGrid r d).defaultCode := by
    rw [hB.lower (by omega), (carrierGridArrows r d).trivial]
  refine ⟨hl, ?_⟩
  rcases gridRule_domain hr with hprop | ha
  · subst sC
    rw [hl (by simp only [sortRank, Nat.zero_add]; omega)]
    exact (gridFormation_default hd .prop).image
  · apply gridCodeImage_arrow
    · exact hA.image.mono (by omega)
    · exact hB.image.mono (by omega)

/-- A dependent quantifier either factors through the same lower row or has
a terminal index. This treats all finite image depths in a single proof. -/
theorem gridFormation_all (hd : d ≤ r)
    (hdom : sC = .prop ∨ sortRank sA ≤ sortRank sC) (hcod : sortRank sB ≤ sortRank sC)
    (A : (carrierGrid (r + 1) d).Code)
    (B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code)
    (hA : GridFormation (r + 1) d sA A)
    (hB : ∀ x, GridFormation (r + 1) (d + 1) sB (B x)) :
    GridFormation (r + 1) (d + 1) sC ((carrierGridQuantifiers r d).code A B) := by
  have hl (h : sortRank sC + (d + 1) < (r + 1) + 1) :
      (carrierGridQuantifiers r d).code A B = (carrierGrid (r + 1) (d + 1)).defaultCode :=
    (carrierGridQuantifiers r d).trivial A B (fun x => (hB x).lower (by omega))
  refine ⟨hl, ?_⟩
  rcases hdom with hprop | hdom
  · subst sC
    rw [hl (by simp only [sortRank, Nat.zero_add]; omega)]
    exact (gridFormation_default (Nat.succ_le_succ hd) .prop).image
  · let k := min (d + 1) ((r + 1) + 1 - sortRank sC)
    change GridCodeImage (r + 1) (d + 1) k _
    have hk1 : k ≤ d + 1 := Nat.min_le_left _ _
    have hk2 : k ≤ (r + 1) + 1 - sortRank sC := Nat.min_le_right _ _
    by_cases hk : k ≤ d
    · apply gridCodeImage_all (Nat.le_trans hk hd) A B
      · exact hA.image.mono (by omega)
      · intro x; exact (hB x).image.mono (by omega)
    · have he := hA.lower (by omega)
      subst A
      rw [(carrierGridQuantifiers r d).single]
      exact (hB _).image.mono (by omega)

/-- Uniform closure of complete dependent products, including the final
same-coordinate arrow, under every trusted source product rule. -/
theorem gridFormation_pi (hd : d ≤ r) (hr : Rl sA sB sC)
    (A : (carrierGrid (r + 1) d).Code)
    (D B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code)
    (hA : GridFormation (r + 1) d sA A)
    (hD : ∀ x, GridFormation (r + 1) (d + 1) sA (D x))
    (hB : ∀ x, GridFormation (r + 1) (d + 1) sB (B x)) :
    GridFormation (r + 1) (d + 1) sC
      ((carrierGridQuantifiers r d).pi (carrierGridArrows (r + 1) (d + 1)) A D B) :=
  gridFormation_all hd (gridRule_domain hr) (Nat.le_refl _) A _ hA
    (fun x => gridFormation_arrow (Nat.succ_le_succ hd) hr (hD x) (hB x))

end Submission.Helpers
