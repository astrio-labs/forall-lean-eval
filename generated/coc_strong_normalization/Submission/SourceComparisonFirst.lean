import Submission.SourceBetaFirst

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem sourceGridValid_arity (hv : (sourceGridInterpretation r Γ ρ A).Valid v) :
    (v ⟨0, by omega⟩).code = arityAt (.type r) A := by
  have hh := hv 0 (Nat.zero_lt_succ _)
  rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hh
  exact hh

theorem sourceGridEval_application_compare_first
    (hf : BoundedTyping (r + 2) Γ f (.pi A B)) (ha : BoundedTyping (r + 2) Γ a A)
    (hf' : BoundedTyping (r + 2) Δ f' (.pi A' B')) (ha' : BoundedTyping (r + 2) Δ a' A')
    (ρ δ : GridEnvironment (r + 1))
    (hD : arityAt (.type r) A = arityAt (.type r) A')
    (hC : arityAt (.type r) B = arityAt (.type r) B')
    (hF : FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ f) (sourceGridEval r Δ δ f'))
    (hArg : FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ a) (sourceGridEval r Δ δ a')) :
    FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ (.app f a)) (sourceGridEval r Δ δ (.app f' a')) := by
  have hp := chosenProduct_arity_components hf (q := .type r) rfl
  have hp' := chosenProduct_arity_components hf' (q := .type r) rfl
  have hOp : FiniteGridValue.Agree 1 (sourceGridNativeApp r Γ ρ f a) (sourceGridNativeApp r Δ δ f' a') := by
    unfold sourceGridNativeApp
    apply finiteTypeApplication_prefix_congr r 1 (by omega)
    · exact sourceGridCode_first_of_arity r _ _ _ _ _ _ (hp.1.trans (hD.trans hp'.1.symm))
    · intro x hx
      exact sourceGridCode_first_of_arity r _ _ _ _ _ _ (hp.2.trans (hC.trans hp'.2.symm))
    · exact hF
    · exact hArg
  apply FiniteGridValue.agree_one
  exact (sourceGridEval_app_native_zero hf ha ρ).trans
    ((hOp ⟨0, by omega⟩ (Nat.zero_lt_succ 0)).trans (sourceGridEval_app_native_zero hf' ha' δ).symm)

theorem sourceGridEval_lambda_compare_first
    (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s)) (hb : BoundedTyping (r + 2) (A :: Γ) b B)
    (hPi' : BoundedTyping (r + 2) Δ (.pi A' B') (.srt s')) (hb' : BoundedTyping (r + 2) (A' :: Δ) b' B')
    (ρ δ : GridEnvironment (r + 1))
    (hD : arityAt (.type r) A = arityAt (.type r) A')
    (hC : arityAt (.type r) B = arityAt (.type r) B')
    (hBody : ∀ x, (sourceGridInterpretation r Γ ρ A).Valid x →
      FiniteGridValue.Agree 1 (sourceGridEval r (A :: Γ) (push x ρ) b)
        (sourceGridEval r (A' :: Δ) (push x δ) b')) :
    FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ (.lam A b)) (sourceGridEval r Δ δ (.lam A' b')) := by
  have hOp : FiniteGridValue.Agree 1 (sourceGridNativeLambda r Γ ρ A b) (sourceGridNativeLambda r Δ δ A' b') := by
    unfold sourceGridNativeLambda
    apply finiteTypeLambda_prefix_congr r 1 (by omega)
    · exact sourceGridCode_first_of_arity r _ _ _ _ _ _ hD
    · intro x hx
      exact sourceGridCode_first_of_arity r _ _ _ _ _ _
        ((inferredArityAt_eq hb rfl).trans (hC.trans (inferredArityAt_eq hb' rfl).symm))
    · exact hBody
  apply FiniteGridValue.agree_one
  exact (sourceGridEval_lam_native_zero hPi hb ρ).trans
    ((hOp ⟨0, by omega⟩ (Nat.zero_lt_succ 0)).trans (sourceGridEval_lam_native_zero hPi' hb' δ).symm)

theorem sourceGridEval_encoded_compare_first (h : BoundedTyping (r + 2) Γ t (.srt s))
    (h' : BoundedTyping (r + 2) Δ t' (.srt s)) (ht : SourceGridEncodedTerm t) (ht' : SourceGridEncodedTerm t')
    (ρ δ : GridEnvironment (r + 1))
    (hT : SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ t) (sourceGridInterpretation r Δ δ t')) :
    FiniteGridValue.Agree 1 (sourceGridEval r Γ ρ t) (sourceGridEval r Δ δ t') := by
  apply FiniteGridValue.agree_one
  rw [sourceGridEval_encode_zero h ht ρ, sourceGridEval_encode_zero h' ht' δ]
  exact uniformUniverseEncode_prefix_conversion (r + 1) 1 (by omega) s _ _ hT
    (sourceGridInterpretation_formed h ρ) ⟨0, by omega⟩ (Nat.zero_lt_succ 0)

end Submission.Helpers
