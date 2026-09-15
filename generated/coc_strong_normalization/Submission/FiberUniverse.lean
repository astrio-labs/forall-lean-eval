import Submission.FiberSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem fiberShape_prop (hw : BoundedWf 2 Γ) :
    fiberShape 2 0 Γ ρ (.srt .prop) u = .small .prop := by
  have h : BoundedTyping 2 Γ (.srt .prop) (.srt (.type 0)) :=
    .srt hw .prop (by decide) (by decide)
  rw [fiberShape_at_universe h, nextArity_predecessor hw .prop rfl]

theorem fiberShape_type_zero (hw : BoundedWf 2 Γ) :
    fiberShape 2 0 Γ ρ (.srt (.type 0)) u = .small (.fn u.asArity .prop) := by
  have h : BoundedTyping 2 Γ (.srt (.type 0)) (.srt (.type 1)) :=
    .srt hw (.type 0) (by decide) (by decide)
  rw [fiberShape_top h rfl rfl]
  rfl

def fiberSortCode : Srt → Arity → FiberCode
  | .prop, _ => .small .prop
  | .type 0, k => .small (.fn k .prop)
  | _, _ => .small .unit

theorem inferredFiber_sort (h : BoundedTyping 2 Γ t (.srt s))
    (hρ : ShapeContext (.type 0) Γ ρ) :
    inferredFiber 2 0 Γ ρ t = fiberSortCode s (nextArity 2 0 Γ ρ t) := by
  rw [inferredFiber_eq h rfl hρ]
  cases s with
  | prop => exact fiberShape_prop h.wf
  | type j =>
    cases j with
    | zero => exact fiberShape_type_zero h.wf
    | succ j =>
      have hs := h.sort_bound
      have hj : j = 0 := by simp only [sortRank] at hs; omega
      subst j
      exact fiberShape_untypable_sort (by decide) rfl

theorem fiberEncode_code (s : Srt) (k : Arity) (C : ShapeValue → FiberValue → Candidate) :
    (fiberEncode (some s) k C).code = fiberSortCode s k := by
  cases s with
  | prop => rfl
  | type j => cases j <;> rfl

theorem fiberEncode_typed_code (h : BoundedTyping 2 Γ t (.srt s))
    (hρ : ShapeContext (.type 0) Γ ρ) (C : ShapeValue → FiberValue → Candidate) :
    (fiberEncode (some s) (nextArity 2 0 Γ ρ t) C).code = inferredFiber 2 0 Γ ρ t := by
  rw [fiberEncode_code, inferredFiber_sort h hρ]

theorem fiberSemantics_pi_value (h : BoundedTyping 2 Γ (.pi A B) (.srt s))
    (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ (.pi A B)).1 =
      fiberEncode (some s) (nextArity 2 0 Γ ρ (.pi A B)) (fiberSemantics Γ ρ δ (.pi A B)).2 := by
  change FiberValue.force _ (fiberEncode _ _ _) = _
  rw [typeSort_eq h]
  exact FiberValue.force_eq _ (fiberEncode_typed_code h hρ _)

theorem fiberSemantics_sort_value (h : BoundedTyping 2 Γ (.srt r) (.srt s))
    (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ (.srt r)).1 =
      fiberEncode (some s) (nextArity 2 0 Γ ρ (.srt r)) (fun _ _ => Candidate.sn) := by
  change FiberValue.force _ (fiberEncode _ _ _) = _
  rw [typeSort_eq h]
  exact FiberValue.force_eq _ (fiberEncode_typed_code h hρ _)

theorem fiberDecode_encode_prop (k : Arity) (C : ShapeValue → FiberValue → Candidate)
    (u : ShapeValue) (f : FiberValue) :
    fiberDecode (some .prop) k (fiberEncode (some .prop) k C) u f = C .unit .unit := by
  unfold fiberDecode fiberEncode
  exact FiberValue.cast_mk _ _

theorem fiberDecode_encode_type_zero (k : Arity) (C : ShapeValue → FiberValue → Candidate)
    (u : ShapeValue) (f : FiberValue) :
    fiberDecode (some (.type 0)) k (fiberEncode (some (.type 0)) k C) u f =
      C .unit (f.force (.small k)) := by
  exact congrFun (FiberValue.cast_mk (.small (.fn k .prop))
    (fun z => C .unit ⟨.small k, z⟩)) (f.cast (.small k))

theorem FiberValue.force_unit (f : FiberValue) : f.force (.small .unit) = .unit := by
  have he : f.cast (.small .unit) = (Unit.unit : Unit) :=
    @Subsingleton.elim Unit inferInstance _ _
  change FiberValue.mk (.small .unit) (f.cast (.small .unit)) = _
  rw [he]
  rfl

@[simp] theorem FiberValue.force_force (f : FiberValue) (D : FiberCode) :
    (f.force D).force D = f.force D :=
  FiberValue.force_eq _ rfl

theorem fiberCanonical_unit (D : FiberCode) (C : ShapeValue → FiberValue → Candidate)
    (u : ShapeValue) (f : FiberValue) :
    fiberCanonical .unit (fun _ => D) C u f = C .unit (f.force D) := by
  unfold fiberCanonical
  rw [ShapeValue.eq_unit (u.force .unit) rfl]

theorem fiberSemantics_pi_decode_prop (h : BoundedTyping 2 Γ (.pi A B) (.srt .prop))
    (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ (.pi A B)).2 u f =
      fiberDecode (some .prop) (nextArity 2 0 Γ ρ (.pi A B))
        (fiberSemantics Γ ρ δ (.pi A B)).1 u f := by
  rw [fiberSemantics_pi_value h hρ, fiberDecode_encode_prop]
  rw [fiberSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type 0) rfl (by decide)]
  simp only [fiberShape_lower (i := 0) h (by decide)]
  rw [fiberCanonical_unit, fiberCanonical_unit, FiberValue.force_unit, FiberValue.force_unit]

theorem fiberSemantics_pi_decode_type_zero
    (h : BoundedTyping 2 Γ (.pi A B) (.srt (.type 0)))
    (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ (.pi A B)).2 u f =
      fiberDecode (some (.type 0)) (nextArity 2 0 Γ ρ (.pi A B))
        (fiberSemantics Γ ρ δ (.pi A B)).1 u f := by
  rw [fiberSemantics_pi_value h hρ, fiberDecode_encode_type_zero]
  rw [fiberSemantics]
  dsimp only
  rw [h.below_top_kind (q := .type 0) rfl (by decide)]
  simp only [fiberShape_at_universe h]
  rw [fiberCanonical_unit, fiberCanonical_unit]
  rw [FiberValue.force_force]

/-- Every formed type below the top is represented by its encoded candidate family. -/
theorem fiberSemantics_decode (h : BoundedTyping 2 Γ A (.srt s)) (hs : sortRank s < 2)
    (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ A).2 u f =
      fiberDecode (some s) (nextArity 2 0 Γ ρ A) (fiberSemantics Γ ρ δ A).1 u f := by
  cases A with
  | var j =>
    change fiberDecode (typeSort 2 Γ (.var j)) _ _ u f = _
    rw [typeSort_eq h]
    rfl
  | srt r =>
    obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    cases ha with
    | prop =>
      rw [fiberSemantics_sort_value h hρ, fiberDecode_encode_type_zero]
      rfl
    | type j => simp only [sortRank] at hs; omega
  | app g a =>
    change fiberDecode (typeSort 2 Γ (.app g a)) _ _ u f = _
    rw [typeSort_eq h]
    rfl
  | lam D b =>
    obtain ⟨B, r, hPi, hb, hr, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | pi D B =>
    cases s with
    | prop => exact fiberSemantics_pi_decode_prop h hρ
    | type j =>
      have hj : j = 0 := by simp only [sortRank] at hs; omega
      subst j
      exact fiberSemantics_pi_decode_type_zero h hρ

end Submission.Helpers
