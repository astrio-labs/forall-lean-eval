import Submission.UpperGridUniverse

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem upperGridDecode_lower (r : Nat) (s : Srt) (hs : sortRank s < r + 2)
    (k : Arity) (v : UpperGridValue r) (u : ShapeValue) (f : UpperGridValue r) :
    upperGridDecode r (some s) k v u f = .small (.small .unit) := by
  classical
  have h1 : sortRank s ≠ r + 2 := by omega
  have h2 : sortRank s ≠ r + 3 := by omega
  unfold upperGridDecode
  simp only [Option.map_some, Option.some.injEq]
  erw [if_neg h1, if_neg h2]

theorem upperGridSort_low (r : Nat) (u : ShapeValue) (f : UpperGridValue r) :
    upperGridSort r (.type r) u f = .small (.small .prop) := by
  classical
  unfold upperGridSort
  simp only [sortRank, ↓reduceIte]
  rfl

theorem upperGridSort_middle (r : Nat) (u : ShapeValue) (f : UpperGridValue r) :
    upperGridSort r (.type (r + 1)) u f = .small (.atom (f.cast (.small .prop))) := by
  classical
  have hn : r + 2 ≠ r + 1 := by omega
  unfold upperGridSort
  simp only [sortRank]
  erw [if_neg hn, if_pos True.intro]

theorem upperGridSemantics_pi_decode_low {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A B : Tm} {u : ShapeValue} {f : UpperGridValue r}
    (h : BoundedTyping (r + 4) Γ (.pi A B) (.srt (.type (r + 1))))
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ (.pi A B)).2 u f =
      upperGridDecode r (some (.type (r + 1))) (nextArity (r + 4) (r + 2) Γ ρ (.pi A B))
        (upperGridSemantics r Γ ρ δ (.pi A B)).1 u f := by
  rw [upperGridSemantics_pi_value h hρ, upperGridDecode_encode_low]
  rw [upperGrid_small_asArity ((upperGridSemantics_form h hρ).arity (Nat.le_refl _))]
  rw [upperGridSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type (r + 2)) rfl (by change r + 2 < r + 4; omega)]
  simp only [firstGridShape_lower h (show sortRank (.type (r + 1)) < sortRank (.type (r + 2)) from by
    change r + 2 < r + 3; omega)]
  erw [upperGridCanonical_unit]

theorem upperGridSemantics_pi_decode_high {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A B : Tm} {u : ShapeValue} {f : UpperGridValue r}
    (h : BoundedTyping (r + 4) Γ (.pi A B) (.srt (.type (r + 2))))
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ (.pi A B)).2 u f =
      upperGridDecode r (some (.type (r + 2))) (nextArity (r + 4) (r + 2) Γ ρ (.pi A B))
        (upperGridSemantics r Γ ρ δ (.pi A B)).1 u f := by
  rw [upperGridSemantics_pi_value h hρ, upperGridDecode_encode_high]
  rw [upperGrid_small_asSmall ((upperGridSemantics_form h hρ).small (Nat.le_refl _))]
  rw [upperGridSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type (r + 2)) rfl (by change r + 3 < r + 4; omega)]
  simp only [firstGridShape_at_universe h]
  erw [upperGridCanonical_unit, upperGridCanonical_unit, TowerValue.force_force]

/-- The first value faithfully determines the next carrier of every formed
type below the top sort, uniformly at all source bounds at least four. -/
theorem upperGridSemantics_decode {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A : Tm} {s : Srt} {u : ShapeValue} {f : UpperGridValue r}
    (h : BoundedTyping (r + 4) Γ A (.srt s)) (hs : sortRank s < r + 4)
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ A).2 u f = upperGridDecode r (some s)
      (nextArity (r + 4) (r + 2) Γ ρ A) (upperGridSemantics r Γ ρ δ A).1 u f := by
  by_cases hl : sortRank s < r + 2
  · exact ((upperGridSemantics_form h hρ).lower hl).trans (upperGridDecode_lower r s hl _ _ _ _).symm
  · cases A with
    | var j =>
      change upperGridDecode r (typeSort (r + 4) Γ (.var j)) _ _ u f = _
      rw [typeSort_eq h]
      rfl
    | app g a =>
      change upperGridDecode r (typeSort (r + 4) Γ (.app g a)) _ _ u f = _
      rw [typeSort_eq h]
      rfl
    | lam D b =>
      obtain ⟨B, s', hPi, hb, hr, hc⟩ := h.generation
      exact (not_conv_pi_srt hc).elim
    | pi D B =>
      by_cases he : sortRank s = r + 2
      · have hst : s = .type (r + 1) := sortRank_injective he
        subst s
        exact upperGridSemantics_pi_decode_low h hρ
      · have he' : sortRank s = r + 3 := by omega
        have hst : s = .type (r + 2) := sortRank_injective he'
        subst s
        exact upperGridSemantics_pi_decode_high h hρ
    | srt t =>
      obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
      have heq := conv_srt_inj hc
      subst s'
      have hax := ax_rank ha
      by_cases he : sortRank s = r + 2
      · have hst : s = .type (r + 1) := sortRank_injective he
        have htt : t = .type r := sortRank_injective (by change sortRank t = r + 1; omega)
        subst s
        subst t
        rw [upperGridSemantics_sort_value h hρ, upperGridDecode_encode_low]
        change upperGridSort r (.type r) u f =
          .small (.small (upperGridAsArity r (upperGridSort r (.type r) .unit (upperGridUnit r))))
        rw [upperGridSort_low, upperGridSort_low]
        rfl
      · have he' : sortRank s = r + 3 := by omega
        have hst : s = .type (r + 2) := sortRank_injective he'
        have htt : t = .type (r + 1) := sortRank_injective (by change sortRank t = r + 2; omega)
        subst s
        subst t
        rw [upperGridSemantics_sort_value h hρ, upperGridDecode_encode_high,
          nextArity_predecessor h.wf (.type (r + 1)) rfl]
        change upperGridSort r (.type (r + 1)) u f =
          .small (upperGridSort r (.type (r + 1)) .unit (f.force (.small .prop))).asSmall
        rw [upperGridSort_middle, upperGridSort_middle]
        exact congrArg (fun a : Arity => (LayerCode.small (LayerCode.atom a) : UpperGridCode r))
          (TowerValue.cast_mk (S := carrierGrid (r + 3) 1) (.small .prop) (f.cast (.small .prop))).symm

end Submission.Helpers
