import Submission.SourceNativeSuccessor

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Actual beta equality at the successor of any completed stage.
All type choices, casts and substitution follow from the preceding laws. -/
theorem SourceTransportStage.beta_next (S : SourceTransportStage r d) (hd : d + 1 ≤ r + 2) (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridCompatible r (d + 1) Γ ρ) :
    FiniteGridValue.Agree (d + 1) (sourceGridEval r Γ ρ (.app (.lam A b) a))
      (sourceGridEval r Γ ρ (subst 0 a b)) := by
  have hf : BoundedTyping (r + 2) Γ (.lam A b) (.pi A B) := .lam hPi hb hPi.sort_bound
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  have hp := S.chosen_product hf (hρ.mono (Nat.le_succ d))
  have hOp : FiniteGridValue.Agree (d + 1) (sourceGridNativeApp r Γ ρ (.lam A b) a)
      (sourceGridApply r Γ ρ A (chosenType (r + 2) (A :: Γ) b)
        (sourceGridNativeLambda r Γ ρ A b) (sourceGridEval r Γ ρ a)) := by
    unfold sourceGridNativeApp sourceGridApply
    apply finiteTypeApplication_prefix_congr r (d + 1) hd
    · exact hp.1.code
    · intro x hx
      have hxA := hp.1.code.coherent_forward d S.depth (by omega) _
        (hx.mono (hd := Nat.le_refl (r + 2)) S.depth)
      have hctx := S.extend hA (hρ.mono (Nat.le_succ d)) hxA
      have hB := S.conversion_law hb.type_expression (chosenType_typing hb).type_expression hctx
        (typing_unique hb.forget (chosenType_typing hb).forget)
      exact ((hp.2 x hx).trans hB).code
    · exact S.lam_native_next hd hPi hb (hρ.mono (Nat.le_succ d))
    · intro i hi; rfl
  have hBeta := sourceGridNativeLambda_beta_prefix r (d + 1) hd Γ ρ A b _
    (S.typed_coherent_next hd ha (hρ.mono (Nat.le_succ d)))
  have hSub := (S.single_next hd hb hA ha hρ).1
  have hApp := S.app_native_next hd hf ha (hρ.mono (Nat.le_succ d))
  exact fun i hi => (hApp i hi).trans ((hOp i hi).trans ((hBeta i hi).trans (hSub i hi).symm))

end Submission.Helpers
