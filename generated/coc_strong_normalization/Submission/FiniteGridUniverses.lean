import Submission.FiniteGridTypes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def FiniteGridType.reify (r k : Nat) (A : FiniteGridType (r + 1 + k)) :
    FiniteGridValue (r + 1 + k) := FiniteGridValue.ofTower _
  (universeReifyValues r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate))

noncomputable def finiteUniversePrefix (r k d : Nat) (hd : d ≤ r + 1)
    (u : FiniteGridValue (r + 1 + k)) : UniversePrefix r d :=
  UniversePrefix.fromValues r k d hd (fun i => FiniteGridValue.toTower _ u (i + k))

/-- The source universe decoder reads only the stored type value and the
argument. It does not have access to the original semantic type. -/
noncomputable def finiteUniverseCode (r k d : Nat) (hd : d ≤ r)
    (u v : FiniteGridValue (r + 1 + k)) : (carrierGrid (r + 1 + k) (d + 1 + k)).Code :=
  (finiteUniversePrefix r k d (by omega) u).readCodeFamily hd k
    (FiniteGridValue.toTower _ u (d + k)) (universeArgumentSlice r k (FiniteGridValue.toTower _ v))

noncomputable def finiteUniverseCandidate (r k : Nat) (u v : FiniteGridValue (r + 1 + k)) : Candidate :=
  (finiteUniversePrefix r k (r + 1) (Nat.le_refl _) u).readCandidateFamily k
    (FiniteGridValue.toTower _ u (r + 1 + k)) (universeArgumentSlice r k (FiniteGridValue.toTower _ v))

theorem FiniteGridType.reify_at (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (d : Nat) (hd : d ≤ r + 1) :
    FiniteGridValue.toTower _ (A.reify r k) (d + k) =
      universeReify r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) d := by
  exact (FiniteGridValue.toTower_at _ (A.reify r k) ⟨d + k, by omega⟩).trans
    (universeReifyValues_at r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) d)

theorem finiteUniversePrefix_reify (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (d : Nat) (hd : d ≤ r + 1) :
    finiteUniversePrefix r k d hd (A.reify r k) = universeTypePrefix r k A.carrier d hd := by
  unfold finiteUniversePrefix
  calc
    _ = UniversePrefix.fromValues r k d hd
        (universeReify r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate)) :=
      UniversePrefix.fromValues_congr r k d hd _ _ (fun i hi => A.reify_at r k i (by omega))
    _ = _ := universeReify_prefix r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) d hd

theorem FiniteGridType.reify_valid (r k : Nat) (A : FiniteGridType (r + 1 + k)) :
    (FiniteGridType.sort (r + 1 + k) (.type r)).Valid (A.reify r k) :=
  (uniformSortType _ _).valid_ofTower _
    ((universeReifyValues_typed r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate)).mono (by omega))

/-- Universe elimination recovers a formed semantic type's actual carrier
from its finite stored value on every valid argument. -/
theorem finiteUniverseCode_reify (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (hA : A.Formed (.type r)) (d : Nat) (hd : d ≤ r) (v : FiniteGridValue (r + 1 + k))
    (hv : A.Valid v) : finiteUniverseCode r k d hd (A.reify r k) v =
      A.carrier.code (d + 1 + k) (by omega) (FiniteGridValue.toTower _ v) := by
  unfold finiteUniverseCode
  rw [finiteUniversePrefix_reify, A.reify_at r k d (by omega)]
  have hvc : A.carrier.Coherent (r + 1 + k + 1) (Nat.le_refl _) (FiniteGridValue.toTower _ v) := hv
  exact universeReify_decode r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) hA d hd _
    (hvc.mono (by omega))

theorem finiteUniverseCandidate_reify (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (hA : A.Formed (.type r)) (v : FiniteGridValue (r + 1 + k)) (hv : A.Valid v) :
    finiteUniverseCandidate r k (A.reify r k) v = A.candidate v := by
  unfold finiteUniverseCandidate
  rw [finiteUniversePrefix_reify, A.reify_at r k (r + 1) (Nat.le_refl _)]
  have hvc : A.carrier.Coherent (r + 1 + k + 1) (Nat.le_refl _) (FiniteGridValue.toTower _ v) := hv
  have h := universeReify_candidate r k A.carrier (CausalGridPredicate.ofFinite _ A.candidate) hA
    (FiniteGridValue.toTower _ v) (hvc.mono (by omega))
  exact h.trans (congrArg A.candidate (FiniteGridValue.ofTower_toTower _ v))

noncomputable def FiniteGridType.reifyProp (A : FiniteGridType R) : FiniteGridValue R :=
  FiniteGridValue.ofTower R (propReifyValues R (CausalGridPredicate.ofFinite R A.candidate))

noncomputable def finitePropCandidate (R : Nat) (u : FiniteGridValue R) : Candidate :=
  propValueCandidate R (FiniteGridValue.toTower R u)

theorem finitePropCandidate_ofTower (R : Nat) (v : TowerFamily (carrierGrid R)) :
    finitePropCandidate R (FiniteGridValue.ofTower R v) = propValueCandidate R v := by
  unfold finitePropCandidate propValueCandidate
  rw [FiniteGridValue.toTower_at R _ ⟨R, Nat.lt_succ_self _⟩]
  rfl

theorem FiniteGridType.reifyProp_valid (A : FiniteGridType R) :
    (FiniteGridType.sort R .prop).Valid A.reifyProp :=
  (uniformSortType _ _).valid_ofTower _ (propReifyValues_typed _ _)

theorem finitePropCandidate_reify (A : FiniteGridType R) (hA : A.Formed .prop)
    (v : FiniteGridValue R) (hv : A.Valid v) : finitePropCandidate R A.reifyProp = A.candidate v := by
  unfold FiniteGridType.reifyProp
  rw [finitePropCandidate_ofTower]
  exact (propReifyValues_candidate R A.carrier (CausalGridPredicate.ofFinite R A.candidate) hA
    (FiniteGridValue.toTower R v) hv).trans (congrArg A.candidate (FiniteGridValue.ofTower_toTower R v))

noncomputable def positiveFinitePiType (R : Nat) (hR : 0 < R) (A : FiniteGridType R)
    (B : FiniteGridFamily R) : FiniteGridType R := by
  cases R with
  | zero => omega
  | succ r => exact finitePiType r A B

theorem positiveFinitePiType_formed (R : Nat) (hR : 0 < R) (A : FiniteGridType R) (B : FiniteGridFamily R)
    (hr : Rl sA sB sC) (hA : A.Formed sA) (hB : ∀ a, A.Valid a → (B.fiber a).Formed sB) :
    (positiveFinitePiType R hR A B).Formed sC := by
  cases R with
  | zero => omega
  | succ r => exact finitePiType_formed r A B hr hA hB

/-- The finite source-facing product carrier equation: product formation,
reification, and universe elimination agree at every active coordinate. -/
theorem finitePi_universe_code (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (B : FiniteGridFamily (r + 1 + k)) (hr : Rl sA sB (.type r))
    (hA : A.Formed sA) (hB : ∀ a, A.Valid a → (B.fiber a).Formed sB)
    (d : Nat) (hd : d ≤ r) (v : FiniteGridValue (r + 1 + k))
    (hv : (positiveFinitePiType (r + 1 + k) (by omega) A B).Valid v) :
    let P := positiveFinitePiType (r + 1 + k) (by omega) A B
    finiteUniverseCode r k d hd (P.reify r k) v =
      P.carrier.code (d + 1 + k) (by omega) (FiniteGridValue.toTower _ v) :=
  finiteUniverseCode_reify r k _ (positiveFinitePiType_formed _ _ A B hr hA hB) d hd v hv

theorem finitePi_universe_candidate (r k : Nat) (A : FiniteGridType (r + 1 + k))
    (B : FiniteGridFamily (r + 1 + k)) (hr : Rl sA sB (.type r))
    (hA : A.Formed sA) (hB : ∀ a, A.Valid a → (B.fiber a).Formed sB)
    (v : FiniteGridValue (r + 1 + k))
    (hv : (positiveFinitePiType (r + 1 + k) (by omega) A B).Valid v) :
    let P := positiveFinitePiType (r + 1 + k) (by omega) A B
    finiteUniverseCandidate r k (P.reify r k) v = P.candidate v :=
  finiteUniverseCandidate_reify r k _ (positiveFinitePiType_formed _ _ A B hr hA hB) v hv

theorem finitePi_prop_candidate (r : Nat) (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (hA : A.Formed sA) (hB : ∀ a, A.Valid a → (B.fiber a).Formed .prop)
    (v : FiniteGridValue (r + 1)) (hv : (finitePiType r A B).Valid v) :
    finitePropCandidate (r + 1) (finitePiType r A B).reifyProp = (finitePiType r A B).candidate v :=
  finitePropCandidate_reify _ (finitePiType_formed r A B (Rl.prop sA) hA hB) v hv

end Submission.Helpers
