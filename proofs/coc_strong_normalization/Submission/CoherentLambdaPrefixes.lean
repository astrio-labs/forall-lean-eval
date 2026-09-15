import Submission.CoherentPiPrefixes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem finiteGridMap_eq_partial_below (d : Nat) (A : FiniteGridType R) (F G : FiniteGridMap R)
    (h : ∀ a, A.Valid a → FiniteGridValue.Agree d (F.eval a) (G.eval a)) (j : Nat) (hj : j ≤ R) (hjd : j < d)
    (a : TowerFamily (carrierGrid R)) (ha : A.carrier.Coherent (j + 1) (by omega) a) :
    F.toCausal.eval a j = G.toCausal.eval a j := by
  let b := A.carrier.normalize (R + 1) (Nat.le_refl _) a
  have hb : A.carrier.Coherent (R + 1) (Nat.le_refl _) b := A.carrier.normalize_coherent _ _ a
  have hba : TowerFamily.AgreeBelow (j + 1) b a := A.carrier.complete_recover (j + 1) (by omega) a ha
  exact (F.toCausal.causal j hj b a hba).symm.trans
    (((h (FiniteGridValue.ofTower R b) (A.carrier.valid_ofTower b hb)).toTower j hjd).trans
      (G.toCausal.causal j hj b a hba))

theorem finiteLambdaAt_below_eq (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (F G : FiniteGridMap (r + 1)) (hBody : ∀ a, A.Valid a → FiniteGridValue.Agree d (F.eval a) (G.eval a))
    (j : Nat) (hj : j ≤ r + 1) (hjd : j < d) (f : TowerFamily (carrierGrid (r + 1))) :
    gridLambdaAt r A.carrier B.toCausal F.toCausal j hj f =
      gridLambdaAt r A'.carrier B'.toCausal G.toCausal j hj f := by
  have he := finiteApplicationPrefix_below_eq r d A A' B B' hA hB j (by omega) (by omega)
  have hD := funext (coherentPi_domain_field_below r d hA j hj hjd)
  have hE := coherentPi_codomain_fields_below r d A A' B B' hB j hj hjd he f
  rw [gridLambdaAt_fields, gridLambdaAt_fields, ← hA.telescopeAt j (by omega) (by omega)]
  dsimp only [CausalGridType.arguments, UniversePrefix.rowArguments] at hD hE ⊢
  rw [← hD, ← hE]
  apply prefixLambdaFields_congr
  intro x y
  apply finiteGridMap_eq_partial_below d A F G hBody j hj hjd
  exact A.carrier.coherent_extend j hj _ (A.carrier.section_coherent j (by omega) x) _ rfl


/-- Abstraction at a retained prefix uses only carrier and body equality
at that prefix, with body equality restricted to valid arguments. -/
theorem finiteLambdaPrefix_below_eq (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (F G : FiniteGridMap (r + 1))
    (hBody : ∀ a, A.Valid a → FiniteGridValue.Agree d (F.eval a) (G.eval a))
    (e : Nat) (he : e ≤ r + 2) (hed : e ≤ d) :
    gridLambdaPrefix r A.carrier B.toCausal F.toCausal e he =
      gridLambdaPrefix r A'.carrier B'.toCausal G.toCausal e he := by
  induction e with
  | zero => rfl
  | succ e ih =>
    change (gridLambdaPrefix r A.carrier B.toCausal F.toCausal e (by omega)).set e _ =
      (gridLambdaPrefix r A'.carrier B'.toCausal G.toCausal e (by omega)).set e _
    rw [← ih (by omega) (by omega)]
    rw [finiteLambdaAt_below_eq r d A A' B B' hA hB F G hBody e (by omega) (by omega)]

end Submission.Helpers
