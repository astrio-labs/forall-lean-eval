import Submission.SourceGridDecoding

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- Carrier equality on coherent prefixes strictly below d. There is no
candidate equality or assertion about later coordinates. -/
def FiniteGridCodeEqBelow (d : Nat) (A A' : FiniteGridType R) : Prop :=
  ∀ j (hj : j ≤ R), j < d → ∀ v, A.carrier.Coherent j (by omega) v →
    A.carrier.code j hj v = A'.carrier.code j hj v

theorem FiniteGridTypeEq.codeEqBelow {R : Nat} {A A' : FiniteGridType R}
    (h : FiniteGridTypeEq A A') (d : Nat) : FiniteGridCodeEqBelow d A A' :=
  fun j hj _ v hv => h.code j hj v hv

theorem FiniteGridCodeEqBelow.telescopeAt {R d : Nat} {A A' : FiniteGridType R}
    (h : FiniteGridCodeEqBelow d A A') (e : Nat) (he : e ≤ R + 1) (hed : e ≤ d) :
    A.carrier.telescopeAt e he = A'.carrier.telescopeAt e he := by
  induction e with
  | zero => rfl
  | succ e ih =>
    unfold CausalGridType.telescopeAt
    rw [carrierFieldPrefix, carrierFieldPrefix]
    have hp := ih (by omega) (by omega)
    change carrierFieldPrefix R A.carrier.code e (by omega) = carrierFieldPrefix R A'.carrier.code e (by omega) at hp
    rw [← hp]
    congr 1
    funext x
    exact h e (by omega) (by omega) _ (A.carrier.section_coherent e (by omega) x)

theorem coherentPi_domain_field_below (r d : Nat) {A A' : FiniteGridType (r + 1)}
    (h : FiniteGridCodeEqBelow d A A') (j : Nat) (hj : j ≤ r + 1) (hjd : j < d)
    (x : (A.carrier.telescopeAt j (by omega)).El) :
    A.carrier.code j hj ((A.carrier.arguments j (by omega)).encode x) =
      A'.carrier.code j hj ((A.carrier.arguments j (by omega)).encode x) :=
  h j hj hjd _ (A.carrier.section_coherent j (by omega) x)

theorem coherentPi_codomain_field_below (r d : Nat) (A : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1))
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1) (hjd : j < d) (f : TowerFamily (carrierGrid (r + 1)))
    (x : (A.carrier.telescopeAt j (by omega)).El) :
    let a := (A.carrier.arguments j (by omega)).encode x
    (B.toCausal.fiber a).code j hj ((gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval f a) =
      (B'.toCausal.fiber a).code j hj ((gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval f a) := by
  let a := (A.carrier.arguments j (by omega)).encode x
  let b := A.carrier.normalize (r + 2) (Nat.le_refl _) a
  let O := gridApplicationPrefix r A.carrier B.toCausal j (by omega)
  have ha : A.carrier.Coherent j (by omega) a := A.carrier.section_coherent j (by omega) x
  have hb : A.carrier.Coherent (r + 2) (Nat.le_refl _) b := A.carrier.normalize_coherent _ _ a
  have hba : TowerFamily.AgreeBelow j b a := A.carrier.complete_recover j (by omega) a ha
  have hO := O.congr f f b a (.refl f j) hba
  have hv := gridApplicationPrefix_partial_coherent r A.carrier B.toCausal j (by omega) f b (hb.mono (by omega))
  have hv' : (B.toCausal.fiber b).Coherent j (by omega) (O.eval f a) := by
    change (B.toCausal.fiber b).Coherent j (by omega) (O.eval f b) at hv
    rw [hO] at hv
    exact hv
  have hfield := (hB (FiniteGridValue.ofTower _ b) (A.carrier.valid_ofTower b hb)) j hj hjd (O.eval f a) hv'
  change (B.toCausal.fiber a).code j hj (O.eval f a) = (B'.toCausal.fiber a).code j hj (O.eval f a)
  exact (B.toCausal.causal j hj b a hba _).symm.trans
    (hfield.trans (B'.toCausal.causal j hj b a hba _))
theorem coherentPi_codomain_fields_below (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1))
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1) (hjd : j < d)
    (he : (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval)
    (f : TowerFamily (carrierGrid (r + 1))) :
    (fun x : (A.carrier.telescopeAt j (by omega)).El =>
      let a := (A.carrier.arguments j (by omega)).encode x
      (B.toCausal.fiber a).code j hj ((gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval f a)) =
    (fun x : (A.carrier.telescopeAt j (by omega)).El =>
      let a := (A.carrier.arguments j (by omega)).encode x
      (B'.toCausal.fiber a).code j hj ((gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval f a)) := by
  funext x
  exact (coherentPi_codomain_field_below r d A B B' hB j hj hjd f x).trans
    (congrArg ((B'.toCausal.fiber ((A.carrier.arguments j (by omega)).encode x)).code j hj)
      (congrFun (congrFun he f) ((A.carrier.arguments j (by omega)).encode x)))

theorem finitePiCode_below_eq (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1) (hjd : j < d)
    (he : (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval)
    (f : TowerFamily (carrierGrid (r + 1))) :
    (finitePiType r A B).carrier.code j hj f = (finitePiType r A' B').carrier.code j hj f := by
  have hF := funext (coherentPi_domain_field_below r d hA j hj hjd)
  have hG := coherentPi_codomain_fields_below r d A A' B B' hB j hj hjd he f
  change gridPiCode r A.carrier B.toCausal j hj _ f = gridPiCode r A'.carrier B'.toCausal j hj _ f
  rw [gridPiCode_prefix, gridPiCode_prefix, ← hA.telescopeAt j (by omega) (by omega)]
  unfold prefixPiCode
  change (prefixBindingObject r j hj (A.carrier.telescopeAt j (by omega)) _ _).code = _
  dsimp only [CausalGridType.arguments, UniversePrefix.rowArguments] at hF hG ⊢
  exact prefixBindingCode_congr r j hj _ hF hG

theorem finitePiApplyAt_below_eq (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1) (hjd : j < d)
    (he : (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval)
    (f a : TowerFamily (carrierGrid (r + 1))) :
    gridPiApplyAt r A.carrier B.toCausal j hj (gridApplicationPrefix r A.carrier B.toCausal j (by omega)).eval f a =
      gridPiApplyAt r A'.carrier B'.toCausal j hj (gridApplicationPrefix r A'.carrier B'.toCausal j (by omega)).eval f a := by
  have hF := funext (coherentPi_domain_field_below r d hA j hj hjd)
  have hG := coherentPi_codomain_fields_below r d A A' B B' hB j hj hjd he f
  rw [gridPiApplyAt_prefix, gridPiApplyAt_prefix, ← hA.telescopeAt j (by omega) (by omega)]
  rw [prefixPiApply_fields, prefixPiApply_fields]
  dsimp only [CausalGridType.arguments, UniversePrefix.rowArguments] at hF hG ⊢
  rw [hF, hG]


/-- Application at a retained prefix requires only semantic type equality
at that prefix. The later carriers and candidates remain unconstrained. -/
theorem finiteApplicationPrefix_below_eq (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (e : Nat) (he : e ≤ r + 2) (hed : e ≤ d) :
    (gridApplicationPrefix r A.carrier B.toCausal e he).eval =
      (gridApplicationPrefix r A'.carrier B'.toCausal e he).eval := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have hh := ih (by omega) (by omega)
    funext f a
    change ((gridApplicationPrefix r A.carrier B.toCausal e (by omega)).eval f a).set e _ =
      ((gridApplicationPrefix r A'.carrier B'.toCausal e (by omega)).eval f a).set e _
    rw [congrFun (congrFun hh f) a,
      finitePiApplyAt_below_eq r d A A' B B' hA hB e (by omega) (by omega) hh f a]

theorem finitePiType_carrier_below_eq (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1) (hjd : j < d) (f : TowerFamily (carrierGrid (r + 1))) :
    (finitePiType r A B).carrier.code j hj f = (finitePiType r A' B').carrier.code j hj f :=
  finitePiCode_below_eq r d A A' B B' hA hB j hj hjd
    (finiteApplicationPrefix_below_eq r d A A' B B' hA hB j (by omega) (by omega)) f

end Submission.Helpers
