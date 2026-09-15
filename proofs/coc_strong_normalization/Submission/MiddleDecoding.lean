import Submission.MiddleForms

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem ThirdCode.small_asFiber {C : ThirdCode} (h : C.IsFiber) : .small C.asFiber = C := by
  obtain ⟨A, rfl⟩ := h
  rfl

theorem ThirdCode.small_asArity {C : ThirdCode} (h : C.IsArity) :
    .small (.small C.asFiber.asArity) = C := by
  obtain ⟨A, rfl⟩ := h
  rfl

theorem middleDecode_encode_type_zero (k : Arity) (C : ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue) :
    middleDecode (some (.type 0)) k (middleEncode (some (.type 0)) k C) u f =
      .small (.small (C .unit .unit).asFiber.asArity) := by
  exact congrArg (fun a : Arity => ThirdCode.small (.small a))
    (MiddleValue.cast_mk (.small .prop) (C .unit .unit).asFiber.asArity)

theorem middleDecode_encode_type_one (k : Arity) (C : ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue) :
    middleDecode (some (.type 1)) k (middleEncode (some (.type 1)) k C) u f =
      .small (C .unit (f.force (.small k))).asFiber := by
  exact congrArg ThirdCode.small (congrFun (MiddleValue.cast_mk (.universe k)
    (fun z => (C .unit ⟨.small k, z⟩).asFiber)) (f.cast (.small k)))

theorem middleSemantics_pi_decode_type_zero
    (h : BoundedTyping 3 Γ (.pi A B) (.srt (.type 0)))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ (.pi A B)).2 u f =
      middleDecode (some (.type 0)) (nextArity 3 1 Γ ρ (.pi A B))
        (middleSemantics Γ ρ δ (.pi A B)).1 u f := by
  rw [middleSemantics_pi_value h hρ, middleDecode_encode_type_zero,
    ThirdCode.small_asArity (middleSemantics_form h hρ)]
  rw [middleSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type 1) rfl (by decide)]
  simp only [middleShape_lower (i := 1) h (by decide)]
  rw [middleCanonical_unit, middleCanonical_unit, MiddleValue.force_unit, MiddleValue.force_unit]

theorem middleSemantics_pi_decode_type_one
    (h : BoundedTyping 3 Γ (.pi A B) (.srt (.type 1)))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ (.pi A B)).2 u f =
      middleDecode (some (.type 1)) (nextArity 3 1 Γ ρ (.pi A B))
        (middleSemantics Γ ρ δ (.pi A B)).1 u f := by
  rw [middleSemantics_pi_value h hρ, middleDecode_encode_type_one,
    ThirdCode.small_asFiber (middleSemantics_form h hρ)]
  rw [middleSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type 1) rfl (by decide)]
  simp only [middleShape_at_universe h]
  rw [middleCanonical_unit, middleCanonical_unit, MiddleValue.force_force]

/-- Formed types below `Type 2` are faithfully represented by their middle
values: decoding reconstructs the third carrier at every semantic input. -/
theorem middleSemantics_decode (h : BoundedTyping 3 Γ A (.srt s)) (hs : sortRank s < 3)
    (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ A).2 u f =
      middleDecode (some s) (nextArity 3 1 Γ ρ A) (middleSemantics Γ ρ δ A).1 u f := by
  cases A with
  | var j =>
    change middleDecode (typeSort 3 Γ (.var j)) _ _ u f = _
    rw [typeSort_eq h]
    rfl
  | srt r =>
    obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    cases ha with
    | prop =>
      rw [middleSemantics_sort_value h hρ, middleDecode_encode_type_zero]
      rfl
    | type j =>
      have hj : j = 0 := by simp only [sortRank] at hs; omega
      subst j
      rw [middleSemantics_sort_value h hρ, middleDecode_encode_type_one,
        nextArity_predecessor h.wf (.type 0) rfl]
      change ThirdCode.small (FiberCode.small (.fn (f.cast (.small .prop)) .prop)) =
        ThirdCode.small (FiberCode.small (.fn ((f.force (.small .prop)).cast (.small .prop)) .prop))
      simp only [MiddleValue.force, MiddleValue.cast_mk]
  | app g a =>
    change middleDecode (typeSort 3 Γ (.app g a)) _ _ u f = _
    rw [typeSort_eq h]
    rfl
  | lam D b =>
    obtain ⟨B, r, hPi, hb, hr, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | pi D B =>
    cases s with
    | prop => exact middleSemantics_form h hρ
    | type j => cases j with
      | zero => exact middleSemantics_pi_decode_type_zero h hρ
      | succ j =>
        have hj : j = 0 := by simp only [sortRank] at hs; omega
        subst j
        exact middleSemantics_pi_decode_type_one h hρ

end Submission.Helpers
