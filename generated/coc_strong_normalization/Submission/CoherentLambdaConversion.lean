import Submission.CoherentPiConversion

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem finiteGridMap_eq_partial (A : FiniteGridType R) (F G : FiniteGridMap R)
    (h : ∀ a, A.Valid a → F.eval a = G.eval a) (j : Nat) (hj : j ≤ R)
    (a : TowerFamily (carrierGrid R)) (ha : A.carrier.Coherent (j + 1) (by omega) a) :
    F.toCausal.eval a j = G.toCausal.eval a j := by
  let b := A.carrier.normalize (R + 1) (Nat.le_refl _) a
  have hb : A.carrier.Coherent (R + 1) (Nat.le_refl _) b := A.carrier.normalize_coherent _ _ a
  have hba : TowerFamily.AgreeBelow (j + 1) b a := A.carrier.complete_recover (j + 1) (by omega) a ha
  exact (F.toCausal.causal j hj b a hba).symm.trans
    ((congrArg (fun v => FiniteGridValue.toTower R v j) (h (FiniteGridValue.ofTower R b) (A.carrier.valid_ofTower b hb))).trans
      (G.toCausal.causal j hj b a hba))

noncomputable def prefixLambdaFields (r j : Nat) (hj : j ≤ r + 1) (P : UniversePrefix (r + 1) j)
    (D E : P.El → (carrierGrid (r + 1) j).Code)
    (H : TowerFamily (carrierGrid (r + 1)) → TowerValue (carrierGrid (r + 1) j)) :
    TowerValue (carrierGrid (r + 1) j) :=
  let O := prefixBindingObject r j hj P D E
  ⟨O.code, O.values.encode (fun x y => (H ((P.rowArguments.encode x).set j ⟨D x, y⟩)).cast (E x))⟩

theorem prefixLambdaFields_congr (r j : Nat) (hj : j ≤ r + 1) (P : UniversePrefix (r + 1) j)
    (D E : P.El → (carrierGrid (r + 1) j).Code)
    (H K : TowerFamily (carrierGrid (r + 1)) → TowerValue (carrierGrid (r + 1) j))
    (h : ∀ x y, H ((P.rowArguments.encode x).set j ⟨D x, y⟩) = K ((P.rowArguments.encode x).set j ⟨D x, y⟩)) :
    prefixLambdaFields r j hj P D E H = prefixLambdaFields r j hj P D E K := by
  unfold prefixLambdaFields
  apply congrArg (TowerValue.mk _)
  apply congrArg (prefixBindingObject r j hj P D E).values.encode
  funext x y
  exact congrArg (fun v => v.cast (E x)) (h x y)

theorem gridLambdaAt_fields (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1)) (j : Nat) (hj : j ≤ r + 1) (f : TowerFamily (carrierGrid (r + 1))) :
    gridLambdaAt r A B F j hj f = prefixLambdaFields r j hj (A.telescopeAt j (by omega))
      (fun x => A.code j hj ((A.telescopeAt j (by omega)).rowArguments.encode x))
      (fun x => (B.fiber ((A.telescopeAt j (by omega)).rowArguments.encode x)).code j hj
        ((gridApplicationPrefix r A B j (by omega)).eval f ((A.telescopeAt j (by omega)).rowArguments.encode x)))
      (fun a => F.eval a j) := by
  unfold gridLambdaAt
  dsimp only
  rw [gridBindingObject_prefix]
  rfl

theorem finiteLambdaAt_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (F G : FiniteGridMap (r + 1)) (hBody : ∀ a, A.Valid a → F.eval a = G.eval a)
    (j : Nat) (hj : j ≤ r + 1) (f : TowerFamily (carrierGrid (r + 1))) :
    gridLambdaAt r A.carrier B.toCausal F.toCausal j hj f =
      gridLambdaAt r A'.carrier B'.toCausal G.toCausal j hj f := by
  have he := finiteApplicationPrefix_coherent_eq r A A' B B' hA hB j (by omega)
  have hD := funext (coherentPi_domain_field r hA j hj)
  have hE := coherentPi_codomain_fields r A A' B B' hB j hj he f
  rw [gridLambdaAt_fields, gridLambdaAt_fields, ← hA.telescopeAt j (by omega)]
  dsimp only [CausalGridType.arguments, UniversePrefix.rowArguments] at hD hE ⊢
  rw [← hD, ← hE]
  apply prefixLambdaFields_congr
  intro x y
  apply finiteGridMap_eq_partial A F G hBody j hj
  exact A.carrier.coherent_extend j hj _ (A.carrier.section_coherent j (by omega) x) _ rfl

theorem finiteLambdaPrefix_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (F G : FiniteGridMap (r + 1)) (hBody : ∀ a, A.Valid a → F.eval a = G.eval a)
    (d : Nat) (hd : d ≤ r + 2) :
    gridLambdaPrefix r A.carrier B.toCausal F.toCausal d hd =
      gridLambdaPrefix r A'.carrier B'.toCausal G.toCausal d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (gridLambdaPrefix r A.carrier B.toCausal F.toCausal d (by omega)).set d _ =
      (gridLambdaPrefix r A'.carrier B'.toCausal G.toCausal d (by omega)).set d _
    rw [← ih (by omega)]
    rw [finiteLambdaAt_coherent_eq r A A' B B' hA hB F G hBody d (by omega)]

/-- Abstraction respects coherent type conversion and body equality on
valid arguments. There is no equality premise on invalid body inputs. -/
theorem finiteTypeLambda_coherent_eq (r : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridTypeEq A A')
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (F G : FiniteGridMap (r + 1)) (hBody : ∀ a, A.Valid a → F.eval a = G.eval a) :
    finiteTypeLambda r A B F = finiteTypeLambda r A' B' G :=
  congrArg (FiniteGridValue.ofTower _)
    (finiteLambdaPrefix_coherent_eq r A A' B B' hA hB F G hBody (r + 2) (Nat.le_refl _))

end Submission.Helpers
