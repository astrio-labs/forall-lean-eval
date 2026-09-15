import Submission.ThirdSoundness
import Submission.BoundedModel

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

abbrev ThirdModelValue := ShapeValue × MiddleValue × ThirdValue

def thirdModelUpper (ρ : Nat → ThirdModelValue) : Nat → ShapeValue := fun j => (ρ j).1
def thirdModelMiddle (ρ : Nat → ThirdModelValue) : Nat → MiddleValue := fun j => (ρ j).2.1
def thirdModelLower (ρ : Nat → ThirdModelValue) : Nat → ThirdValue := fun j => (ρ j).2.2

@[simp] theorem thirdModelUpper_push (x : ThirdModelValue) (ρ : Nat → ThirdModelValue) :
    thirdModelUpper (push x ρ) = push x.1 (thirdModelUpper ρ) := by funext j; cases j <;> rfl

@[simp] theorem thirdModelMiddle_push (x : ThirdModelValue) (ρ : Nat → ThirdModelValue) :
    thirdModelMiddle (push x ρ) = push x.2.1 (thirdModelMiddle ρ) := by funext j; cases j <;> rfl

@[simp] theorem thirdModelLower_push (x : ThirdModelValue) (ρ : Nat → ThirdModelValue) :
    thirdModelLower (push x ρ) = push x.2.2 (thirdModelLower ρ) := by funext j; cases j <;> rfl

def thirdModelAdmissible (Γ : List Tm) (ρ : Nat → ThirdModelValue) : Prop :=
  ShapeContext (.type 1) Γ (thirdModelUpper ρ) ∧
    MiddleContext 3 1 Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) ∧
    ThirdContext Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) (thirdModelLower ρ)

noncomputable def thirdModelValid (Γ : List Tm) (ρ : Nat → ThirdModelValue) (A : Tm)
    (x : ThirdModelValue) : Prop :=
  x.1.code = arityAt (.type 1) A ∧
    x.2.1.code = middleShape 3 1 Γ (thirdModelUpper ρ) A x.1 ∧
    x.2.2.code = thirdShape Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) A x.1 x.2.1

noncomputable def thirdModelEval (Γ : List Tm) (ρ : Nat → ThirdModelValue) (t : Tm) : ThirdModelValue :=
  (shapeEval 3 1 Γ (thirdModelUpper ρ) t,
    (middleSemantics Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) t).1,
    (thirdSemantics Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) (thirdModelLower ρ) t).1)

noncomputable def thirdModelCandidate (Γ : List Tm) (ρ : Nat → ThirdModelValue)
    (A : Tm) (x : ThirdModelValue) : Candidate :=
  (thirdSemantics Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) (thirdModelLower ρ) A).2 x.1 x.2.1 x.2.2

noncomputable def thirdModelApply (Γ : List Tm) (ρ : Nat → ThirdModelValue)
    (A B : Tm) (f x : ThirdModelValue) : ThirdModelValue :=
  let D := fun x => middleShape 3 1 Γ (thirdModelUpper ρ) A x
  let E := fun x z => middleShape 3 1 (A :: Γ) (push x (thirdModelUpper ρ)) B z
  let d := thirdShape Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) A
  let c := fun x y => thirdShape (A :: Γ) (push x (thirdModelUpper ρ)) (push y (thirdModelMiddle ρ)) B
  (f.1.apply x.1, middleApply (arityAt (.type 1) A) D E f.1 f.2.1 x.1 x.2.1,
    thirdApply (arityAt (.type 1) A) D E d c f.1 f.2.1 f.2.2 x.1 x.2.1 x.2.2)

def thirdDefaultUpper (Γ : List Tm) (j : Nat) : ShapeValue :=
  match Γ[j]? with
  | some A => ⟨arityAt (.type 1) A, (arityAt (.type 1) A).shapePoint⟩
  | none => .unit

noncomputable def thirdDefaultMiddle (Γ : List Tm) (ρ : Nat → ShapeValue) (j : Nat) : MiddleValue :=
  match Γ[j]? with
  | some A => let D := middleShape 3 1 Γ ρ (lift (j + 1) 0 A) (ρ j); ⟨D, D.point⟩
  | none => .unit

noncomputable def thirdDefaultLower (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → MiddleValue) (j : Nat) : ThirdValue :=
  match Γ[j]? with
  | some A => let D := thirdShape Γ ρ δ (lift (j + 1) 0 A) (ρ j) (δ j); ⟨D, D.point⟩
  | none => .unit

theorem thirdDefaultUpper_admissible (Γ : List Tm) : ShapeContext (.type 1) Γ (thirdDefaultUpper Γ) := by
  intro j A hj; simp only [thirdDefaultUpper, hj]

theorem thirdDefaultMiddle_admissible (Γ : List Tm) (ρ : Nat → ShapeValue) :
    MiddleContext 3 1 Γ ρ (thirdDefaultMiddle Γ ρ) := by
  intro j A hj; simp only [thirdDefaultMiddle, hj]

theorem thirdDefaultLower_admissible (Γ : List Tm) (ρ : Nat → ShapeValue) (δ : Nat → MiddleValue) :
    ThirdContext Γ ρ δ (thirdDefaultLower Γ ρ δ) := by
  intro j A hj; simp only [thirdDefaultLower, hj]

theorem thirdModel_extend (hA : BoundedTyping 3 Γ A (.srt s))
    (hρ : thirdModelAdmissible Γ ρ) (hx : thirdModelValid Γ ρ A x) :
    thirdModelAdmissible (A :: Γ) (push x ρ) := by
  simp only [thirdModelAdmissible, thirdModelUpper_push, thirdModelMiddle_push, thirdModelLower_push]
  exact ⟨hρ.1.up hx.1, hρ.2.1.up hA rfl hx.2.1, hρ.2.2.up hA hρ.1 hx.1 hx.2.2⟩

theorem thirdModel_product (_hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (_hρ : thirdModelAdmissible Γ ρ) (hf : thirdModelValid Γ ρ (.pi A B) f) :
    thirdModelCandidate Γ ρ (.pi A B) f =
      Candidate.inter (fun x : {x : ThirdModelValue // thirdModelValid Γ ρ A x} =>
        (thirdModelCandidate Γ ρ A x.1).arrow
          (thirdModelCandidate (A :: Γ) (push x.1 ρ) B (thirdModelApply Γ ρ A B f x.1))) := by
  unfold thirdModelCandidate
  rw [thirdSemantics_pi hf.1 hf.2.1 hf.2.2]
  apply Candidate.ext
  intro t
  rw [thirdCandidatePi_contains]
  constructor
  · rintro ⟨hsn, hh⟩
    refine ⟨hsn, fun x => ?_⟩
    simpa only [thirdModelUpper_push, thirdModelMiddle_push, thirdModelLower_push, thirdModelApply] using
      hh x.1.1 x.2.1 x.1.2.1 x.2.2.1 x.1.2.2 x.2.2.2
  · intro h
    refine ⟨h.1, fun x hx y hy z hz => ?_⟩
    simpa only [thirdModelUpper_push, thirdModelMiddle_push, thirdModelLower_push, thirdModelApply] using
      h.2 ⟨(x, y, z), ⟨hx, hy, hz⟩⟩

theorem thirdModel_abstraction (hPi : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 3 (A :: Γ) b B) (hρ : thirdModelAdmissible Γ ρ)
    (hx : thirdModelValid Γ ρ A x) :
    thirdModelApply Γ ρ A B (thirdModelEval Γ ρ (.lam A b)) x =
      thirdModelEval (A :: Γ) (push x ρ) b := by
  unfold thirdModelApply thirdModelEval
  simp only [thirdModelUpper_push, thirdModelMiddle_push, thirdModelLower_push]
  apply Prod.ext
  · exact middleShapeEval_lam_apply hb hρ.1 hx.1
  · apply Prod.ext
    · exact middleSemantics_lam_apply hPi hb hρ.1 hx.1 hx.2.1
    · dsimp only
      rw [thirdSemantics_lam hPi hb hρ.1 hρ.2.1]
      apply thirdBeta _ _ _ _ _ _ _ _ _ _ _ hx.1 hx.2.1 hx.2.2
      rw [middleShapeEval_lam_apply hb hρ.1 hx.1,
        middleSemantics_lam_apply hPi hb hρ.1 hx.1 hx.2.1]
      obtain ⟨sA, hA, _⟩ := hPi.pi_domain
      exact thirdSemantics_typed_code hb (hρ.1.up hx.1) (hρ.2.1.up hA rfl hx.2.1)

/-- The three-layer interpretation is a source model for bound three. Its
construction uses carrier and candidate laws, with no normalization premise. -/
noncomputable def thirdBoundedModel : BoundedModel 3 where
  Value := ThirdModelValue
  eval := thirdModelEval
  candidate := thirdModelCandidate
  admissible := thirdModelAdmissible
  valid := thirdModelValid
  apply := thirdModelApply
  environment Γ := by
    let ρ := thirdDefaultUpper Γ
    let δ := thirdDefaultMiddle Γ ρ
    let ε := thirdDefaultLower Γ ρ δ
    exact ⟨fun j => (ρ j, δ j, ε j), thirdDefaultUpper_admissible Γ,
      thirdDefaultMiddle_admissible Γ ρ, thirdDefaultLower_admissible Γ ρ δ⟩
  point := by
    intro Γ ρ A s hA hρ
    let x : ShapeValue := ⟨arityAt (.type 1) A, (arityAt (.type 1) A).shapePoint⟩
    let D := middleShape 3 1 Γ (thirdModelUpper ρ) A x
    let y : MiddleValue := ⟨D, D.point⟩
    let E := thirdShape Γ (thirdModelUpper ρ) (thirdModelMiddle ρ) A x y
    exact ⟨(x, y, ⟨E, E.point⟩), rfl, rfl, rfl⟩
  extend := thirdModel_extend
  typed := by
    intro Γ ρ t A ht hρ
    exact ⟨shapeEval_typed_code ht rfl hρ.1, middleSemantics_typed_code ht hρ.1,
      thirdSemantics_typed_code ht hρ.1 hρ.2.1⟩
  variable_value := by
    intro Γ ρ j A hw hj hρ
    exact Prod.ext rfl (Prod.ext (middleSemantics_var hρ.2.1 hw hj hρ.1)
      (thirdSemantics_var hρ.2.2 hw hj hρ.1 hρ.2.1))
  sort := by intro Γ ρ s x; rfl
  weaken := by
    intro Γ ρ A s C r x hA hC hρ hx
    funext v
    unfold thirdModelCandidate
    simp only [thirdModelUpper_push, thirdModelMiddle_push, thirdModelLower_push]
    rw [(thirdSemantics_ren (ε := thirdModelLower ρ) (ε' := push x.2.2 (thirdModelLower ρ))
      hC (.cons hA.wf hA) (.weaken Γ A)
      hρ.1 (hρ.1.up hx.1) hρ.2.1 (hρ.2.1.up hA rfl hx.2.1)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).2 r hC]
  product := thirdModel_product
  application := by
    intro Γ ρ f a A B hf ha hρ
    exact Prod.ext rfl (Prod.ext (middleSemantics_app hf ha hρ.1)
      (thirdSemantics_app hf ha hρ.1 hρ.2.1))
  abstraction := thirdModel_abstraction
  substitution := by
    intro Γ ρ A B a sA sB hA hB ha hρ
    funext v
    unfold thirdModelCandidate
    simp only [thirdModelUpper_push, thirdModelMiddle_push, thirdModelLower_push, thirdModelEval]
    rw [thirdSemantics_subst_candidate hB ha hA hρ.1 hρ.2.1 hρ.2.2]
  conversion := by
    intro Γ ρ t A B s ht hB hc hρ
    funext v
    unfold thirdModelCandidate
    rw [type_thirdSemantics_conv ht hB hρ.1 hρ.2.1 hρ.2.2 hc]

/-- Fundamental reducibility for all realizing substitutions in the concrete model. -/
theorem bound_three_fundamental (h : BoundedTyping 3 Γ t A)
    (hρ : thirdModelAdmissible Γ ρ) (hσ : thirdBoundedModel.RealizesContext Γ ρ σ) :
    (thirdModelCandidate Γ ρ A (thirdModelEval Γ ρ t)).contains (sub σ t) :=
  bounded_model_fundamental thirdBoundedModel h hρ hσ

/-- Unconditional strong normalization of original derivations at bound three. -/
theorem bound_three_normalization (h : BoundedTyping 3 Γ t A) : SN t :=
  bounded_model_normalization thirdBoundedModel h

/-- The checked three-layer model discharges all source bounds at most three. -/
theorem normalization_of_models_above_three
    (models : ∀ n, 4 ≤ n → Nonempty (BoundedModel n)) (h : Typing Γ t A) : SN t := by
  apply normalization_of_bounded ?_ h
  intro n Δ u B hu
  by_cases hn : n ≤ 3
  · exact bound_three_normalization (hu.mono hn)
  · obtain ⟨M⟩ := models n (by omega)
    exact bounded_model_normalization M hu

end Submission.Helpers
