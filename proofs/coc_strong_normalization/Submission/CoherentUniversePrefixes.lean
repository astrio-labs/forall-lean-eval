import Submission.CoherentLambdaPrefixes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem FiniteGridCodeEqBelow.universePrefix (r k e : Nat)
    {A B : FiniteGridType (r + 1 + k)} (h : FiniteGridCodeEqBelow (e + 1) A B)
    (hA : A.Formed (.type r)) (d : Nat) (hd : d ≤ r + 1) (hde : d + k ≤ e) :
    universeTypePrefix r k A.carrier d hd = universeTypePrefix r k B.carrier d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [universeTypePrefix, universeTypePrefix, ← ih (by omega) (by omega)]
    congr 1
    funext x
    apply congrArg (universeOutputCodes r d k).decode
    exact h (d + 1 + k) (by omega) (by omega) _
      (universeTypePrefix_section_coherent r k A.carrier hA d (by omega) x)

theorem FiniteGridCodeEqBelow.universeReify_proper (r k e : Nat)
    {A B : FiniteGridType (r + 1 + k)} (h : FiniteGridCodeEqBelow (e + 1) A B)
    (hA : A.Formed (.type r)) (d : Nat) (hd : d ≤ r) (hde : d + k < e) :
    universeReify r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) d =
      universeReify r k B.carrier (CausalGridPredicate.ofFinite _ B.candidate) d := by
  rw [Submission.Helpers.universeReify_proper r k _ _ d hd,
    Submission.Helpers.universeReify_proper r k _ _ d hd]
  unfold universeTypeField
  rw [← h.universePrefix r k e hA d (by omega) (by omega)]
  congr 1
  funext x
  apply congrArg (universeOutputCodes r d k).decode
  exact h (d + 1 + k) (by omega) (by omega) _
    (universeTypePrefix_section_coherent r k A.carrier hA d (by omega) x)

/-- Before the final candidate coordinate, encoding reads just one more
carrier coordinate. No equality of candidate functions is assumed. -/
theorem FiniteGridCodeEqBelow.reify_prefix (r k e : Nat) (he : e ≤ r + 1 + k)
    {A B : FiniteGridType (r + 1 + k)} (h : FiniteGridCodeEqBelow (e + 1) A B)
    (hA : A.Formed (.type r)) : FiniteGridValue.Agree e (A.reify r k) (B.reify r k) := by
  intro i hi
  change universeReifyValues r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) i.val =
    universeReifyValues r k B.carrier (CausalGridPredicate.ofFinite _ B.candidate) i.val
  unfold universeReifyValues
  split
  · rw [h.universeReify_proper r k e hA _ (by omega) (by omega)]
  · rfl

end Submission.Helpers
