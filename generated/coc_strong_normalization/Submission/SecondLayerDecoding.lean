import Submission.SecondLayerUniverse

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 2000000

variable {r : Nat} {δ : Nat → UpperGridValue (r + 1)} {ε : Nat → SecondLayerValue r}
  {u : ShapeValue} {f : UpperGridValue (r + 1)} {g : SecondLayerValue r}

theorem secondLayerDecode_lower (r : Nat) (s : Srt) (hs : sortRank s < r + 2)
    (k : Arity) (m : UpperGridValue (r + 1)) (v : SecondLayerValue r)
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerDecode r (some s) k m v u f g = .small (.small (.small .unit)) := by
  classical
  have h2 : sortRank s ≠ r + 2 := by omega
  have h3 : sortRank s ≠ r + 3 := by omega
  have h4 : sortRank s ≠ r + 4 := by omega
  unfold secondLayerDecode
  simp only [Option.map_some, Option.some.injEq]
  erw [if_neg h2, if_neg h3, if_neg h4]

theorem secondLayerSemantics_pi_decode_low (h : BoundedTyping (r + 5) Γ (.pi A B) (.srt (.type (r + 1))))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε (.pi A B)).2 u f g =
      secondLayerDecode r (some (.type (r + 1))) (nextArity (r + 5) (r + 3) Γ ρ (.pi A B))
        (upperGridSemantics (r + 1) Γ ρ δ (.pi A B)).1 (secondLayerSemantics r Γ ρ δ ε (.pi A B)).1 u f g := by
  rw [secondLayerSemantics_pi_value h hρ hδ, secondLayerDecode_encode_low]
  rw [secondLayer_small_asArity ((secondLayerSemantics_form h hρ).arity (Nat.le_refl _))]
  rw [secondLayerSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type (r + 3)) rfl (by change r + 2 < r + 5; omega)]
  simp only [firstGridShape_lower h (show sortRank (.type (r + 1)) < sortRank (.type (r + 3)) from by
    change r + 2 < r + 4; omega)]
  erw [secondLayerCanonical_unit, secondLayerCanonical_unit]
  simp only [upperGridForce_unit (r + 1), secondGridShape_lower (r := r) h (by change r + 2 < r + 3; omega) hρ, secondLayerForce_unit r]

theorem secondLayerSemantics_pi_decode_middle (h : BoundedTyping (r + 5) Γ (.pi A B) (.srt (.type (r + 2))))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε (.pi A B)).2 u f g =
      secondLayerDecode r (some (.type (r + 2))) (nextArity (r + 5) (r + 3) Γ ρ (.pi A B))
        (upperGridSemantics (r + 1) Γ ρ δ (.pi A B)).1 (secondLayerSemantics r Γ ρ δ ε (.pi A B)).1 u f g := by
  rw [secondLayerSemantics_pi_value h hρ hδ, secondLayerDecode_encode_middle]
  rw [secondLayer_small_asSmallTwo ((secondLayerSemantics_form h hρ).smallTwo (Nat.le_refl _))]
  rw [secondLayerSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type (r + 3)) rfl (by change r + 3 < r + 5; omega)]
  simp only [firstGridShape_lower h (show sortRank (.type (r + 2)) < sortRank (.type (r + 3)) from by
    change r + 3 < r + 4; omega)]
  erw [secondLayerCanonical_unit, secondLayerCanonical_unit]
  simp only [upperGridForce_unit (r + 1), secondGridShape_middle (r := r) h hρ]
  erw [TowerValue.force_force (S := carrierGrid (r + 4) 2)]

theorem secondLayerSemantics_pi_decode_high (h : BoundedTyping (r + 5) Γ (.pi A B) (.srt (.type (r + 3))))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε (.pi A B)).2 u f g =
      secondLayerDecode r (some (.type (r + 3))) (nextArity (r + 5) (r + 3) Γ ρ (.pi A B))
        (upperGridSemantics (r + 1) Γ ρ δ (.pi A B)).1 (secondLayerSemantics r Γ ρ δ ε (.pi A B)).1 u f g := by
  rw [secondLayerSemantics_pi_value h hρ hδ, secondLayerDecode_encode_high]
  rw [secondLayer_small_asSmall ((secondLayerSemantics_form h hρ).small (Nat.le_refl _))]
  rw [secondLayerSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type (r + 3)) rfl (by change r + 4 < r + 5; omega)]
  simp only [firstGridShape_at_universe h]
  erw [secondLayerCanonical_unit, secondLayerCanonical_unit]
  simp only [secondGridShape_high (r := r) h hρ]
  erw [TowerValue.force_force (S := carrierGrid (r + 4) 1),
    TowerValue.cast_force (S := carrierGrid (r + 4) 1),
    TowerValue.force_force (S := carrierGrid (r + 4) 2)]

theorem secondLayerSort_low (r : Nat) (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerSort r (.type r) u f g = .small (.small (.small .prop)) := by
  classical
  unfold secondLayerSort
  simp only [sortRank, ↓reduceIte]
  rfl

theorem secondLayerSort_middle (r : Nat) (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerSort r (.type (r + 1)) u f g = .small (.small (.atom (g.cast (.small (.small .prop))))) := by
  classical
  have hn : r + 2 ≠ r + 1 := by omega
  unfold secondLayerSort
  simp only [sortRank]
  erw [if_neg hn]
  rfl

theorem secondLayerSort_high (r : Nat) (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerSort r (.type (r + 2)) u f g =
      .small (carrierGridUniverseNext (r + 2) 0 (by omega) (f.cast (.small .prop))
        (g.cast (.small (.atom (f.cast (.small .prop)))))).code := by
  classical
  have hn : r + 3 ≠ r + 1 := by omega
  have hn' : r + 3 ≠ r + 2 := by omega
  unfold secondLayerSort
  simp only [sortRank]
  erw [if_neg hn, if_neg hn']
  rfl

theorem upperGridSemantics_sort_arity {p : Nat} {δ : Nat → UpperGridValue p}
    (h : BoundedTyping (p + 4) Γ (.srt (.type p)) (.srt (.type (p + 1))))
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) :
    (upperGridSemantics p Γ ρ δ (.srt (.type p))).1 = ⟨.small .prop, .prop⟩ := by
  rw [upperGridSemantics_sort_value h hρ]
  unfold upperGridEncode
  simp only [Option.map_some, sortRank, ↓reduceIte]
  erw [upperGridSort_low]
  rfl

theorem upperGridSemantics_sort_family {p : Nat} {δ : Nat → UpperGridValue p}
    (h : BoundedTyping (p + 4) Γ (.srt (.type (p + 1))) (.srt (.type (p + 2))))
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) :
    (upperGridSemantics p Γ ρ δ (.srt (.type (p + 1)))).1 = ⟨.atom .prop, fun l => .atom l⟩ := by
  rw [upperGridSemantics_sort_value h hρ, nextArity_predecessor h.wf (.type (p + 1)) rfl]
  have hn : p + 3 ≠ p + 2 := by omega
  unfold upperGridEncode
  simp only [Option.map_some, sortRank, Option.some.injEq]
  erw [if_neg hn]
  simp only [ite_true]
  congr 1
  funext l
  erw [upperGridSort_middle]
  change (LayerCode.atom (TowerValue.cast (S := carrierGrid (p + 3) 1) (TowerValue.mk (.small .prop) l) (.small .prop)) : (carrierGrid (p + 2) 1).Code) = LayerCode.atom l
  erw [TowerValue.cast_mk (S := carrierGrid (p + 3) 1)]

/-- Faithful universe decoding for the second intermediate coordinate, at
all source bounds at least five. No normalization premise is used. -/
theorem secondLayerSemantics_decode (h : BoundedTyping (r + 5) Γ A (.srt s)) (hs : sortRank s < r + 5)
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε A).2 u f g = secondLayerDecode r (some s)
      (nextArity (r + 5) (r + 3) Γ ρ A) (upperGridSemantics (r + 1) Γ ρ δ A).1
      (secondLayerSemantics r Γ ρ δ ε A).1 u f g := by
  by_cases hl : sortRank s < r + 2
  · exact ((secondLayerSemantics_form h hρ).lower hl).trans (secondLayerDecode_lower r s hl _ _ _ _ _ _).symm
  · cases A with
    | var j =>
      change secondLayerDecode r (typeSort (r + 5) Γ (.var j)) _ _ _ u f g = _
      rw [typeSort_eq h]; rfl
    | app t a =>
      change secondLayerDecode r (typeSort (r + 5) Γ (.app t a)) _ _ _ u f g = _
      rw [typeSort_eq h]; rfl
    | lam D b =>
      obtain ⟨B, s', hPi, hb, hr, hc⟩ := h.generation
      exact (not_conv_pi_srt hc).elim
    | pi D B =>
      by_cases h2 : sortRank s = r + 2
      · have he : s = .type (r + 1) := sortRank_injective h2
        subst s; exact secondLayerSemantics_pi_decode_low h hρ hδ
      · by_cases h3 : sortRank s = r + 3
        · have he : s = .type (r + 2) := sortRank_injective h3
          subst s; exact secondLayerSemantics_pi_decode_middle h hρ hδ
        · have he : s = .type (r + 3) := sortRank_injective (by change sortRank s = r + 4; omega)
          subst s; exact secondLayerSemantics_pi_decode_high h hρ hδ
    | srt t =>
      obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
      have heq := conv_srt_inj hc
      subst s'
      have hax := ax_rank ha
      by_cases h2 : sortRank s = r + 2
      · have he : s = .type (r + 1) := sortRank_injective h2
        have ht : t = .type r := sortRank_injective (by change sortRank t = r + 1; omega)
        subst s; subst t
        rw [secondLayerSemantics_sort_value h hρ hδ, secondLayerDecode_encode_low]
        change secondLayerSort r (.type r) u f g = _
        rw [secondLayerSort_low, secondLayerSort_low]
        rfl
      · by_cases h3 : sortRank s = r + 3
        · have he : s = .type (r + 2) := sortRank_injective h3
          have ht : t = .type (r + 1) := sortRank_injective (by change sortRank t = r + 2; omega)
          subst s; subst t
          rw [secondLayerSemantics_sort_value h hρ hδ, secondLayerDecode_encode_middle,
            upperGridSemantics_sort_arity h hρ]
          change secondLayerSort r (.type (r + 1)) u f g = _
          erw [TowerValue.cast_mk, secondLayerSort_middle, secondLayerSort_middle]
          simp only [LayerCode.asSmall]
          erw [TowerValue.cast_force (S := carrierGrid (r + 4) 2)]
        · have he : s = .type (r + 3) := sortRank_injective (by change sortRank s = r + 4; omega)
          have ht : t = .type (r + 2) := sortRank_injective (by change sortRank t = r + 3; omega)
          subst s; subst t
          rw [secondLayerSemantics_sort_value h hρ hδ, secondLayerDecode_encode_high,
            upperGridSemantics_sort_family h hρ, nextArity_predecessor h.wf (.type (r + 2)) rfl]
          change secondLayerSort r (.type (r + 2)) u f g = _
          erw [TowerValue.cast_mk, secondLayerSort_high, secondLayerSort_high]
          simp only [LayerCode.asSmall]
          erw [TowerValue.cast_force (S := carrierGrid (r + 4) 1), TowerValue.cast_force (S := carrierGrid (r + 4) 2)]

end Submission.Helpers
