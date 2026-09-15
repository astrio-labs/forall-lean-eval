import Submission.SourceGridVariables

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem FiniteGridTypeEq.telescopeAt {R : Nat} {A A' : FiniteGridType R}
    (h : FiniteGridTypeEq A A') (d : Nat) (hd : d ≤ R + 1) :
    A.carrier.telescopeAt d hd = A'.carrier.telescopeAt d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    unfold CausalGridType.telescopeAt
    rw [carrierFieldPrefix, carrierFieldPrefix]
    have hp := ih (by omega)
    change carrierFieldPrefix R A.carrier.code d (by omega) = carrierFieldPrefix R A'.carrier.code d (by omega) at hp
    rw [← hp]
    congr 1
    funext x
    exact h.code d (by omega) _ (A.carrier.section_coherent d (by omega) x)

/-- A coherent partial argument can be completed to a valid argument without
changing the domain coordinates inspected at this stage. -/
theorem gridApplicationPrefix_partial_coherent (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) (d : Nat) (hd : d ≤ r + 2)
    (f a : TowerFamily (carrierGrid (r + 1))) (ha : A.Coherent d hd a) :
    (B.fiber a).Coherent d hd ((gridApplicationPrefix r A B d hd).eval f a) := by
  let b := A.normalize (r + 2) (Nat.le_refl _) a
  have hb : A.Coherent (r + 2) (Nat.le_refl _) b := A.normalize_coherent _ _ a
  have hba : TowerFamily.AgreeBelow d b a := A.complete_recover d hd a ha
  have hc := (gridApplication_coherent r A B f b hb).mono hd
  have he := (gridApplicationPrefix r A B d hd).congr f f b a (.refl f d) hba
  intro i hi
  have hval : gridApplication r A B f b i = (gridApplicationPrefix r A B d hd).eval f a i :=
    (gridApplicationPrefix_agree r A B (r + 2) (Nat.le_refl _) d hd f b i hi).trans (congrFun he i)
  calc
    _ = (gridApplication r A B f b i).code := congrArg TowerValue.code hval.symm
    _ = (B.fiber b).code i (by omega) (gridApplication r A B f b) := hc i hi
    _ = (B.fiber b).code i (by omega) ((gridApplicationPrefix r A B d hd).eval f a) :=
      (B.fiber b).causal i (by omega) _ _ (fun k hk =>
        (gridApplicationPrefix_agree r A B (r + 2) (Nat.le_refl _) d hd f b k (by omega)).trans (congrFun he k))
    _ = _ := B.causal i (by omega) b a (hba.mono (by omega)) _

theorem coherentPi_domain_field (r : Nat) {A A' : FiniteGridType (r + 1)}
    (h : FiniteGridTypeEq A A') (j : Nat) (hj : j ≤ r + 1)
    (x : (A.carrier.telescopeAt j (by omega)).El) :
    A.carrier.code j hj ((A.carrier.arguments j (by omega)).encode x) =
      A'.carrier.code j hj ((A.carrier.arguments j (by omega)).encode x) :=
  h.code j hj _ (A.carrier.section_coherent j (by omega) x)

theorem coherentPi_codomain_field (r : Nat) (A : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1))
    (hB : ∀ a, A.Valid a → FiniteGridTypeEq (B.fiber a) (B'.fiber a))
    (j : Nat) (hj : j ≤ r + 1) (f : TowerFamily (carrierGrid (r + 1)))
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
  have hfield := (hB (FiniteGridValue.ofTower _ b) (A.carrier.valid_ofTower b hb)).code j hj (O.eval f a) hv'
  change (B.toCausal.fiber a).code j hj (O.eval f a) = (B'.toCausal.fiber a).code j hj (O.eval f a)
  exact (B.toCausal.causal j hj b a hba _).symm.trans
    (hfield.trans (B'.toCausal.causal j hj b a hba _))

end Submission.Helpers
