import Submission.FiberSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Product elimination lands in the candidate of the syntactically substituted
codomain, including when that codomain is formed at the top sort. -/
theorem fiberCandidatePi_apply_subst
    (hB : BoundedTyping 2 (A :: Γ) B (.srt sB))
    (ha : BoundedTyping 2 Γ a A) (hA : BoundedTyping 2 Γ A (.srt sA))
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hf : (fiberCandidatePi (arityAt (.type 0) A)
      (fun x => fiberShape 2 0 Γ ρ A x)
      (fun x z => fiberShape 2 0 (A :: Γ) (push x ρ) B z)
      (fiberSemantics Γ ρ δ A).2
      (fun x y => (fiberSemantics (A :: Γ) (push x ρ) (push y δ) B).2)
      u f).contains t)
    (harg : ((fiberSemantics Γ ρ δ A).2
      (shapeEval 2 0 Γ ρ a) (fiberSemantics Γ ρ δ a).1).contains arg) :
    ((fiberSemantics Γ ρ δ (subst 0 a B)).2
      (u.apply (shapeEval 2 0 Γ ρ a))
      (fiberApply (arityAt (.type 0) A)
        (fun x => fiberShape 2 0 Γ ρ A x)
        (fun x z => fiberShape 2 0 (A :: Γ) (push x ρ) B z)
        u f (shapeEval 2 0 Γ ρ a) (fiberSemantics Γ ρ δ a).1)).contains (.app t arg) := by
  rw [fiberSemantics_subst_candidate hB ha hA hρ hδ]
  exact fiberCandidatePi_apply _ _ _ _ _ u f _ _
    (shapeEval_typed_code ha rfl hρ) (fiberSemantics_typed_code ha hρ) hf harg

/-- The application case of candidate soundness, assuming the two input
realizations. The realizing terms may differ from the terms being interpreted. -/
theorem fiberSemantics_app_candidate
    (hf : BoundedTyping 2 Γ f (.pi A B)) (ha : BoundedTyping 2 Γ a A)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (ht : ((fiberSemantics Γ ρ δ (.pi A B)).2
      (shapeEval 2 0 Γ ρ f) (fiberSemantics Γ ρ δ f).1).contains t)
    (harg : ((fiberSemantics Γ ρ δ A).2
      (shapeEval 2 0 Γ ρ a) (fiberSemantics Γ ρ δ a).1).contains arg) :
    ((fiberSemantics Γ ρ δ (subst 0 a B)).2
      (shapeEval 2 0 Γ ρ (.app f a))
      (fiberSemantics Γ ρ δ (.app f a)).1).contains (.app t arg) := by
  obtain ⟨s, hPi⟩ := hf.pi_type
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  rw [fiberSemantics_pi (shapeEval_typed_code hf rfl hρ)
    (fiberSemantics_typed_code hf hρ)] at ht
  rw [shapeEval, fiberSemantics_app hf ha hρ]
  exact fiberCandidatePi_apply_subst hB ha hA hρ hδ ht harg

end Submission.Helpers
