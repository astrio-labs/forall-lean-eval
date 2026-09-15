import Submission.BoundedModel

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

abbrev FiberModelValue := ShapeValue × FiberValue

def fiberModelUpper (ρ : Nat → FiberModelValue) : Nat → ShapeValue := fun j => (ρ j).1
def fiberModelLower (ρ : Nat → FiberModelValue) : Nat → FiberValue := fun j => (ρ j).2

@[simp] theorem fiberModelUpper_push (x : FiberModelValue) (ρ : Nat → FiberModelValue) :
    fiberModelUpper (push x ρ) = push x.1 (fiberModelUpper ρ) := by
  funext j
  cases j <;> rfl

@[simp] theorem fiberModelLower_push (x : FiberModelValue) (ρ : Nat → FiberModelValue) :
    fiberModelLower (push x ρ) = push x.2 (fiberModelLower ρ) := by
  funext j
  cases j <;> rfl

def fiberModelAdmissible (Γ : List Tm) (ρ : Nat → FiberModelValue) : Prop :=
  ShapeContext (.type 0) Γ (fiberModelUpper ρ) ∧
    FiberContext 2 0 Γ (fiberModelUpper ρ) (fiberModelLower ρ)

def fiberModelValid (Γ : List Tm) (ρ : Nat → FiberModelValue) (A : Tm)
    (x : FiberModelValue) : Prop :=
  x.1.code = arityAt (.type 0) A ∧
    x.2.code = fiberShape 2 0 Γ (fiberModelUpper ρ) A x.1

noncomputable def fiberModelEval (Γ : List Tm) (ρ : Nat → FiberModelValue)
    (t : Tm) : FiberModelValue :=
  (shapeEval 2 0 Γ (fiberModelUpper ρ) t,
    (fiberSemantics Γ (fiberModelUpper ρ) (fiberModelLower ρ) t).1)

noncomputable def fiberModelCandidate (Γ : List Tm) (ρ : Nat → FiberModelValue)
    (A : Tm) (x : FiberModelValue) : Candidate :=
  (fiberSemantics Γ (fiberModelUpper ρ) (fiberModelLower ρ) A).2 x.1 x.2

noncomputable def fiberModelApply (Γ : List Tm) (ρ : Nat → FiberModelValue)
    (A B : Tm) (f x : FiberModelValue) : FiberModelValue :=
  (f.1.apply x.1, fiberApply (arityAt (.type 0) A)
    (fun x => fiberShape 2 0 Γ (fiberModelUpper ρ) A x)
    (fun x z => fiberShape 2 0 (A :: Γ) (push x (fiberModelUpper ρ)) B z)
    f.1 f.2 x.1 x.2)

theorem fiberModel_extend (hA : BoundedTyping 2 Γ A (.srt s))
    (hρ : fiberModelAdmissible Γ ρ) (hx : fiberModelValid Γ ρ A x) :
    fiberModelAdmissible (A :: Γ) (push x ρ) := by
  simp only [fiberModelAdmissible, fiberModelUpper_push, fiberModelLower_push]
  exact ⟨hρ.1.up hx.1, hρ.2.up hA rfl hx.2⟩

theorem fiberModel_product (_hPi : BoundedTyping 2 Γ (.pi A B) (.srt s))
    (_hρ : fiberModelAdmissible Γ ρ) (hf : fiberModelValid Γ ρ (.pi A B) f) :
    fiberModelCandidate Γ ρ (.pi A B) f =
      Candidate.inter (fun x : {x : FiberModelValue // fiberModelValid Γ ρ A x} =>
        (fiberModelCandidate Γ ρ A x.1).arrow
          (fiberModelCandidate (A :: Γ) (push x.1 ρ) B
            (fiberModelApply Γ ρ A B f x.1))) := by
  unfold fiberModelCandidate
  rw [fiberSemantics_pi hf.1 hf.2]
  apply Candidate.ext
  intro t
  rw [fiberCandidatePi_contains]
  constructor
  · rintro ⟨hsn, hh⟩
    refine ⟨hsn, fun x => ?_⟩
    simpa only [fiberModelUpper_push, fiberModelLower_push, fiberModelApply] using
      hh x.1.1 x.2.1 x.1.2 x.2.2
  · intro h
    refine ⟨h.1, fun x hx y hy => ?_⟩
    simpa only [fiberModelUpper_push, fiberModelLower_push, fiberModelApply] using
      h.2 ⟨(x, y), ⟨hx, hy⟩⟩

theorem fiberModel_abstraction (hPi : BoundedTyping 2 Γ (.pi A B) (.srt s))
    (hb : BoundedTyping 2 (A :: Γ) b B) (hρ : fiberModelAdmissible Γ ρ)
    (hx : fiberModelValid Γ ρ A x) :
    fiberModelApply Γ ρ A B (fiberModelEval Γ ρ (.lam A b)) x =
      fiberModelEval (A :: Γ) (push x ρ) b := by
  unfold fiberModelApply fiberModelEval
  simp only [fiberModelUpper_push, fiberModelLower_push]
  apply Prod.ext
  · exact shapeEval_lam_apply hb hρ.1 hx.1
  · dsimp only
    rw [fiberSemantics_lam hPi hb hρ.1]
    apply fiberBeta _ _ _ _ _ _ _ hx.1 hx.2
    rw [shapeEval_lam_apply hb hρ.1 hx.1]
    exact fiberSemantics_typed_code hb (hρ.1.up hx.1)

/-- The checked two-layer interpretation satisfies the uniform source interface.
This construction uses its interpretation laws, not its normalization theorem. -/
noncomputable def fiberBoundedModel : BoundedModel 2 where
  Value := FiberModelValue
  eval := fiberModelEval
  candidate := fiberModelCandidate
  admissible := fiberModelAdmissible
  valid := fiberModelValid
  apply := fiberModelApply
  environment Γ := by
    let ρ := defaultShapeEnv Γ
    let δ := defaultFiberEnv Γ ρ
    exact ⟨fun j => (ρ j, δ j), defaultShapeEnv_admissible Γ,
      defaultFiberEnv_admissible Γ ρ⟩
  point := by
    intro Γ ρ A s hA hρ
    let x : ShapeValue := ⟨arityAt (.type 0) A, (arityAt (.type 0) A).shapePoint⟩
    let D := fiberShape 2 0 Γ (fiberModelUpper ρ) A x
    exact ⟨(x, ⟨D, D.point⟩), rfl, rfl⟩
  extend := fiberModel_extend
  typed := by
    intro Γ ρ t A ht hρ
    exact ⟨shapeEval_typed_code ht rfl hρ.1, fiberSemantics_typed_code ht hρ.1⟩
  variable_value := by
    intro Γ ρ j A hw hj hρ
    apply Prod.ext
    · rfl
    · exact fiberSemantics_var hρ.2 hw hj hρ.1
  sort := by intro Γ ρ s x; rfl
  weaken := by
    intro Γ ρ A s C r x hA hC hρ hx
    funext v
    unfold fiberModelCandidate
    simp only [fiberModelUpper_push, fiberModelLower_push]
    rw [(fiberSemantics_ren (δ := fiberModelLower ρ) (δ' := push x.2 (fiberModelLower ρ))
      hC (.cons hA.wf hA) (.weaken Γ A)
      hρ.1 (hρ.1.up hx.1) (fun _ => rfl) (fun _ => rfl)).2 r hC]
  product := fiberModel_product
  application := by
    intro Γ ρ f a A B hf ha hρ
    apply Prod.ext
    · rfl
    · exact fiberSemantics_app hf ha hρ.1
  abstraction := fiberModel_abstraction
  substitution := by
    intro Γ ρ A B a sA sB hA hB ha hρ
    funext v
    unfold fiberModelCandidate
    simp only [fiberModelUpper_push, fiberModelLower_push, fiberModelEval]
    rw [fiberSemantics_subst_candidate hB ha hA hρ.1 hρ.2]
  conversion := by
    intro Γ ρ t A B s ht hB hc hρ
    funext v
    unfold fiberModelCandidate
    rw [type_fiberSemantics_conv ht hB hρ.1 hρ.2 hc]

/-- A concrete instantiation checks that the uniform interface is inhabited. -/
theorem fiber_model_normalization (h : BoundedTyping 2 Γ t A) : SN t :=
  bounded_model_normalization fiberBoundedModel h

end Submission.Helpers
