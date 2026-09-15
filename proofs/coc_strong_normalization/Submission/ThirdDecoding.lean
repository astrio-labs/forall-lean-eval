import Submission.ThirdUniverse

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem thirdShape_at_prop (h : BoundedTyping 3 Γ A (.srt .prop))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    thirdShape Γ ρ δ A u f = .small (.small .unit) := middleSemantics_form h hρ

theorem thirdShape_at_type_zero (h : BoundedTyping 3 Γ A (.srt (.type 0)))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    thirdShape Γ ρ δ A u f = .small (.small ((middleSemantics Γ ρ δ A).1.cast (.small .prop))) :=
  middleSemantics_decode h (by decide) hρ

theorem thirdShape_at_type_one (h : BoundedTyping 3 Γ A (.srt (.type 1)))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    thirdShape Γ ρ δ A u f = .small ((middleSemantics Γ ρ δ A).1.cast
      (.universe (nextArity 3 1 Γ ρ A)) (f.cast (.small (nextArity 3 1 Γ ρ A)))) :=
  middleSemantics_decode h (by decide) hρ

theorem thirdSemantics_pi_decode_prop (h : BoundedTyping 3 Γ (.pi A B) (.srt .prop))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.pi A B)).2 u f g =
      thirdDecode (some .prop) (nextArity 3 1 Γ ρ (.pi A B)) (middleSemantics Γ ρ δ (.pi A B)).1
        (thirdSemantics Γ ρ δ ε (.pi A B)).1 u f g := by
  rw [thirdSemantics_pi_value h hρ hδ, thirdDecode_encode_prop]
  rw [thirdSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type 1) rfl (by decide)]
  simp only [middleShape_lower (i := 1) h (by decide)]
  rw [thirdCanonical_unit, thirdCanonical_unit]
  simp only [MiddleValue.force_unit, thirdShape_at_prop h hρ, ThirdValue.force_unit]

theorem thirdSemantics_pi_decode_type_zero (h : BoundedTyping 3 Γ (.pi A B) (.srt (.type 0)))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.pi A B)).2 u f g =
      thirdDecode (some (.type 0)) (nextArity 3 1 Γ ρ (.pi A B)) (middleSemantics Γ ρ δ (.pi A B)).1
        (thirdSemantics Γ ρ δ ε (.pi A B)).1 u f g := by
  rw [thirdSemantics_pi_value h hρ hδ, thirdDecode_encode_type_zero]
  rw [thirdSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type 1) rfl (by decide)]
  simp only [middleShape_lower (i := 1) h (by decide)]
  rw [thirdCanonical_unit, thirdCanonical_unit]
  simp only [MiddleValue.force_unit, thirdShape_at_type_zero h hρ, ThirdValue.force_force]

theorem thirdSemantics_pi_decode_type_one (h : BoundedTyping 3 Γ (.pi A B) (.srt (.type 1)))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.pi A B)).2 u f g =
      thirdDecode (some (.type 1)) (nextArity 3 1 Γ ρ (.pi A B)) (middleSemantics Γ ρ δ (.pi A B)).1
        (thirdSemantics Γ ρ δ ε (.pi A B)).1 u f g := by
  rw [thirdSemantics_pi_value h hρ hδ, thirdDecode_encode_type_one]
  rw [thirdSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type 1) rfl (by decide)]
  simp only [middleShape_at_universe h]
  rw [thirdCanonical_unit, thirdCanonical_unit]
  simp only [MiddleValue.force_force, thirdShape_at_type_one h hρ, MiddleValue.cast_force, ThirdValue.force_force]

theorem thirdSemantics_decode (h : BoundedTyping 3 Γ A (.srt s)) (hs : sortRank s < 3)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε A).2 u f g =
      thirdDecode (some s) (nextArity 3 1 Γ ρ A) (middleSemantics Γ ρ δ A).1
        (thirdSemantics Γ ρ δ ε A).1 u f g := by
  cases A with
  | var j =>
    change thirdDecode (typeSort 3 Γ (.var j)) _ _ _ u f g = _
    rw [typeSort_eq h]
    rfl
  | app t a =>
    change thirdDecode (typeSort 3 Γ (.app t a)) _ _ _ u f g = _
    rw [typeSort_eq h]
    rfl
  | lam D b =>
    obtain ⟨B, r, hPi, hb, hr, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | srt r =>
    obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    cases ha with
    | prop =>
      rw [thirdSemantics_sort_value h hρ hδ, thirdDecode_encode_type_zero]
      rfl
    | type j =>
      have hj : j = 0 := by simp only [sortRank] at hs; omega
      subst j
      rw [thirdSemantics_sort_value h hρ hδ, thirdDecode_encode_type_one]
      rfl
  | pi D B =>
    cases s with
    | prop => exact thirdSemantics_pi_decode_prop h hρ hδ
    | type j => cases j with
      | zero => exact thirdSemantics_pi_decode_type_zero h hρ hδ
      | succ j =>
        have hj : j = 0 := by simp only [sortRank] at hs; omega
        subst j
        exact thirdSemantics_pi_decode_type_one h hρ hδ

end Submission.Helpers
