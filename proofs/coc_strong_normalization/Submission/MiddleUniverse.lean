import Submission.MiddleSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem middleShape_prop (hw : BoundedWf 3 Γ) :
    middleShape 3 1 Γ ρ (.srt .prop) u = .small .unit := by
  exact middleShape_lower (.srt hw .prop (by decide) (by decide)) (by decide)

theorem middleShape_type_zero (hw : BoundedWf 3 Γ) :
    middleShape 3 1 Γ ρ (.srt (.type 0)) u = .small .prop := by
  have h : BoundedTyping 3 Γ (.srt (.type 0)) (.srt (.type 1)) :=
    .srt hw (.type 0) (by decide) (by decide)
  rw [middleShape_at_universe h, nextArity_predecessor hw (.type 0) rfl]

theorem middleShape_type_one (hw : BoundedWf 3 Γ) :
    middleShape 3 1 Γ ρ (.srt (.type 1)) u = .universe u.asArity := by
  have h : BoundedTyping 3 Γ (.srt (.type 1)) (.srt (.type 2)) :=
    .srt hw (.type 1) (by decide) (by decide)
  rw [middleShape_top h rfl rfl]
  rfl

def middleSortCode : Srt → Arity → MiddleCode
  | .type 0, _ => .small .prop
  | .type 1, k => .universe k
  | _, _ => .small .unit

theorem inferredMiddle_sort (h : BoundedTyping 3 Γ t (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    inferredMiddle 3 1 Γ ρ t = middleSortCode s (nextArity 3 1 Γ ρ t) := by
  rw [inferredMiddle_eq h rfl hρ]
  cases s with
  | prop => exact middleShape_prop h.wf
  | type j =>
    cases j with
    | zero => exact middleShape_type_zero h.wf
    | succ j =>
      cases j with
      | zero => exact middleShape_type_one h.wf
      | succ j =>
        have hs := h.sort_bound
        have hj : j = 0 := by simp only [sortRank] at hs; omega
        subst j
        exact middleShape_untypable_sort (by decide) rfl

theorem middleEncode_code (s : Srt) (k : Arity) (C : ShapeValue → MiddleValue → ThirdCode) :
    (middleEncode (some s) k C).code = middleSortCode s k := by
  cases s with
  | prop => rfl
  | type j => cases j with
    | zero => rfl
    | succ j => cases j <;> rfl

theorem middleEncode_typed_code (h : BoundedTyping 3 Γ t (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (C : ShapeValue → MiddleValue → ThirdCode) :
    (middleEncode (some s) (nextArity 3 1 Γ ρ t) C).code = inferredMiddle 3 1 Γ ρ t := by
  rw [middleEncode_code, inferredMiddle_sort h hρ]

theorem middleSemantics_pi_value (h : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ (.pi A B)).1 =
      middleEncode (some s) (nextArity 3 1 Γ ρ (.pi A B)) (middleSemantics Γ ρ δ (.pi A B)).2 := by
  change MiddleValue.force _ (middleEncode _ _ _) = _
  rw [typeSort_eq h]
  exact MiddleValue.force_eq _ (middleEncode_typed_code h hρ _)

theorem middleSemantics_sort_value (h : BoundedTyping 3 Γ (.srt r) (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ (.srt r)).1 =
      middleEncode (some s) (nextArity 3 1 Γ ρ (.srt r)) (thirdSort r) := by
  change MiddleValue.force _ (middleEncode _ _ _) = _
  rw [typeSort_eq h]
  exact MiddleValue.force_eq _ (middleEncode_typed_code h hρ _)

theorem MiddleValue.force_unit (f : MiddleValue) : f.force (.small .unit) = .unit := by
  have he : f.cast (.small .unit) = (Unit.unit : Unit) :=
    @Subsingleton.elim Unit inferInstance _ _
  change MiddleValue.mk (.small .unit) (f.cast (.small .unit)) = _
  rw [he]
  rfl

@[simp] theorem MiddleValue.force_force (f : MiddleValue) (D : MiddleCode) :
    (f.force D).force D = f.force D := MiddleValue.force_eq _ rfl

theorem middleCanonical_unit (D : MiddleCode) (C : ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue) :
    middleCanonical .unit (fun _ => D) C u f = C .unit (f.force D) := by
  unfold middleCanonical
  rw [ShapeValue.eq_unit (u.force .unit) rfl]

end Submission.Helpers
