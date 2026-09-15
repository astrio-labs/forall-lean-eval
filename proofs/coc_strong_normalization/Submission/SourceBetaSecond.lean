import Submission.SourceNativePrefixes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Actual beta equality through two value coordinates at every finite
source bound, with all type choices, casts and substitution discharged. -/
theorem sourceGridEval_beta_second (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridCompatible r 2 Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.app (.lam A b) a))
      (sourceGridEval r Γ ρ (subst 0 a b)) := by
  have hf : BoundedTyping (r + 2) Γ (.lam A b) (.pi A B) := .lam hPi hb hPi.sort_bound
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  have hp := sourceGridChosenProduct_first hf hρ.first
  have hOp : FiniteGridValue.Agree 2 (sourceGridNativeApp r Γ ρ (.lam A b) a)
      (sourceGridApply r Γ ρ A (chosenType (r + 2) (A :: Γ) b)
        (sourceGridNativeLambda r Γ ρ A b) (sourceGridEval r Γ ρ a)) := by
    unfold sourceGridNativeApp sourceGridApply
    apply finiteTypeApplication_prefix_congr r 2 (by omega)
    · exact hp.1.code
    · intro x hx
      have hxA := hp.1.code.coherent_forward 1 (by omega) (by omega) _
        (hx.mono (hd := Nat.le_refl (r + 2)) (by omega))
      have hctx : SourceGridContextFirst r (A :: Γ) (push x ρ) := by
        apply hρ.first.up
        have hh := hxA 0 (Nat.zero_lt_succ 0)
        rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hh
        exact hh
      have hB := sourceGrid_type_conv_first hb.type_expression (chosenType_typing hb).type_expression hctx
        (typing_unique hb.forget (chosenType_typing hb).forget)
      exact ((hp.2 x hx).trans hB).code
    · exact sourceGridEval_lam_native_second hPi hb hρ.first
    · intro i hi; rfl
  have hBeta := sourceGridNativeLambda_beta_prefix r 2 (by omega) Γ ρ A b _
    (sourceGridEval_coherent_second ha hρ.first)
  have hSub := (sourceGrid_subst_second hb hA ha hρ).1
  have hApp := sourceGridEval_app_native_second hf ha hρ.first
  exact fun i hi => (hApp i hi).trans ((hOp i hi).trans ((hBeta i hi).trans (hSub i hi).symm))

end Submission.Helpers
