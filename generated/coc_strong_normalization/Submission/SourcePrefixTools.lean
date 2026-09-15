import Submission.CoherentUniversePrefixes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem CausalGridType.Agree.codeEqBelow {A B : FiniteGridType R}
    (h : CausalGridType.Agree d A.carrier B.carrier) : FiniteGridCodeEqBelow d A B :=
  fun j hj hjd v _ => congrFun (h j hj hjd) v

theorem FiniteGridCodeEqBelow.coherent_forward {A B : FiniteGridType R}
    (h : FiniteGridCodeEqBelow d A B) (e : Nat) (he : e ≤ R + 1) (hed : e ≤ d)
    (v : TowerFamily (carrierGrid R)) (hv : A.carrier.Coherent e he v) :
    B.carrier.Coherent e he v := by
  intro j hj
  exact (hv j hj).trans (h j (by omega) (by omega) v (hv.mono (by omega)))

theorem FiniteGridCodeEqBelow.coherent_backward {A B : FiniteGridType R}
    (h : FiniteGridCodeEqBelow d A B) (e : Nat) (he : e ≤ R + 1) (hed : e ≤ d)
    (v : TowerFamily (carrierGrid R)) (hv : B.carrier.Coherent e he v) :
    A.carrier.Coherent e he v := by
  induction e with
  | zero => intro i hi; omega
  | succ e ih =>
    have hp := ih (by omega) (by omega) (hv.mono (Nat.le_succ _))
    intro i hi
    by_cases hie : i < e
    · exact hp i hie
    · have hh : i = e := by omega
      subst i
      exact (hv e (Nat.lt_succ_self _)).trans (h e (by omega) (by omega) v hp).symm

theorem FiniteGridCodeEqBelow.symm {A B : FiniteGridType R}
    (h : FiniteGridCodeEqBelow d A B) : FiniteGridCodeEqBelow d B A :=
  fun j hj hjd v hv => (h j hj hjd v (h.coherent_backward j (by omega) (by omega) v hv)).symm

theorem finiteTypeApplication_prefix_congr (r d : Nat) (hd : d ≤ r + 2)
    (A A' : FiniteGridType (r + 1)) (B B' : FiniteGridFamily (r + 1))
    (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (f f' a a' : FiniteGridValue (r + 1))
    (hf : FiniteGridValue.Agree d f f') (ha : FiniteGridValue.Agree d a a') :
    FiniteGridValue.Agree d (finiteTypeApplication r A B f a) (finiteTypeApplication r A' B' f' a') := by
  intro i hi
  have he := finiteApplicationPrefix_below_eq r d A A' B B' hA hB d hd (Nat.le_refl _)
  have hv := (gridApplicationPrefix r A'.carrier B'.toCausal d hd).congr _ _ _ _ hf.toTower ha.toTower
  exact (gridApplicationPrefix_agree r A.carrier B.toCausal (r + 2) (Nat.le_refl _) d hd _ _ i.val hi).trans
    ((congrArg (fun P => P (FiniteGridValue.toTower _ f) (FiniteGridValue.toTower _ a) i.val) he).trans
      ((congrFun hv i.val).trans
        (gridApplicationPrefix_agree r A'.carrier B'.toCausal (r + 2) (Nat.le_refl _) d hd _ _ i.val hi).symm))

theorem finiteTypeLambda_prefix_congr (r d : Nat) (hd : d ≤ r + 2)
    (A A' : FiniteGridType (r + 1)) (B B' : FiniteGridFamily (r + 1))
    (hA : FiniteGridCodeEqBelow d A A')
    (hB : ∀ a, A.Valid a → FiniteGridCodeEqBelow d (B.fiber a) (B'.fiber a))
    (F G : FiniteGridMap (r + 1))
    (hBody : ∀ a, A.Valid a → FiniteGridValue.Agree d (F.eval a) (G.eval a)) :
    FiniteGridValue.Agree d (finiteTypeLambda r A B F) (finiteTypeLambda r A' B' G) := by
  intro i hi
  exact (gridLambdaPrefix_agree r A.carrier B.toCausal F.toCausal (r + 2) (Nat.le_refl _) d hd i.val hi).trans
    ((congrFun (finiteLambdaPrefix_below_eq r d A A' B B' hA hB F G hBody d hd (Nat.le_refl _)) i.val).trans
      (gridLambdaPrefix_agree r A'.carrier B'.toCausal G.toCausal (r + 2) (Nat.le_refl _) d hd i.val hi).symm)

noncomputable def FiniteGridType.forceCoordinate (A : FiniteGridType R)
    (w : FiniteGridValue R) (i : Fin (R + 1)) (v : TowerValue (carrierGrid R i.val)) :
    TowerValue (carrierGrid R i.val) :=
  let C := A.carrier.code i.val (Nat.le_of_lt_succ i.isLt) (FiniteGridValue.toTower R w)
  ⟨C, v.cast C⟩

/-- The coordinate equations characterize the existing semantic normalizer;
this theorem makes no source typing or normalization assumption. -/
theorem FiniteGridType.normalizeValue_of_coordinates (A : FiniteGridType R)
    (v w : FiniteGridValue R)
    (h : ∀ i, w i = A.forceCoordinate w i (v i)) : A.normalizeValue v = w := by
  have hp (d : Nat) (hd : d ≤ R + 1) : TowerFamily.AgreeBelow d
      (A.carrier.normalize d hd (FiniteGridValue.toTower R v)) (FiniteGridValue.toTower R w) := by
    induction d with
    | zero => intro i hi; omega
    | succ d ih =>
      have hh := ih (by omega)
      intro i hi
      change (A.carrier.normalize d (by omega) (FiniteGridValue.toTower R v)).set d _ i = _
      by_cases hid : i = d
      · subst i
        rw [TowerFamily.set_same, A.carrier.causal d (by omega) _ _ hh]
        rw [FiniteGridValue.toTower_at R v ⟨d, by omega⟩, FiniteGridValue.toTower_at R w ⟨d, by omega⟩]
        exact (h ⟨d, by omega⟩).symm
      · rw [TowerFamily.set_other _ d i _ hid]
        exact hh i (by omega)
  funext i
  exact (hp (R + 1) (Nat.le_refl _) i.val i.isLt).trans (FiniteGridValue.toTower_at R w i)

theorem FiniteGridType.normalizeValue_prefix_congr (A B : FiniteGridType R)
    (d : Nat) (hd : d ≤ R + 1) (hAB : FiniteGridCodeEqBelow d A B)
    (v w : FiniteGridValue R) (hvw : FiniteGridValue.Agree d v w) :
    FiniteGridValue.Agree d (A.normalizeValue v) (B.normalizeValue w) := by
  have hp (e : Nat) (he : e ≤ R + 1) (hed : e ≤ d) :
      A.carrier.normalize e he (FiniteGridValue.toTower R v) =
        B.carrier.normalize e he (FiniteGridValue.toTower R w) := by
    induction e with
    | zero => rfl
    | succ e ih =>
      rw [CausalGridType.normalize, CausalGridType.normalize, ← ih (by omega) (by omega)]
      rw [hAB e (by omega) (by omega) _ (A.carrier.normalize_coherent e (by omega) _),
        hvw.toTower e (by omega)]
  intro i hi
  exact (A.carrier.normalize_agree (R + 1) (Nat.le_refl _) d hd _ i.val hi).trans
    ((congrFun (hp d hd (Nat.le_refl _)) i.val).trans
      (B.carrier.normalize_agree (R + 1) (Nat.le_refl _) d hd _ i.val hi).symm)

end Submission.Helpers
