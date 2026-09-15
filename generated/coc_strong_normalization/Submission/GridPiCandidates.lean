import Submission.PropReification

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- The product candidate quantifies over all coherent domain values. The
application operation has already been constructed by coordinate induction. -/
noncomputable def gridPiPredicate (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (p : TowerFamily (carrierGrid (r + 1)) → Candidate)
    (q : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → Candidate) :
    CausalGridPredicate (r + 1) where
  candidate f := Candidate.inter (fun x : {a // A.Coherent (r + 2) (Nat.le_refl _) a} =>
    (p x.1).arrow (q x.1 (gridApplication r A B f x.1)))
  causal f g hfg := by
    apply congrArg Candidate.inter
    funext x
    unfold gridApplication
    rw [(gridApplicationPrefix r A B (r + 2) (Nat.le_refl _)).congr f g x.1 x.1 hfg (.refl x.1 _)]

theorem gridPiPredicate_apply (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (p : TowerFamily (carrierGrid (r + 1)) → Candidate)
    (q : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → Candidate)
    (f x : TowerFamily (carrierGrid (r + 1))) (hx : A.Coherent (r + 2) (Nat.le_refl _) x)
    (ht : ((gridPiPredicate r A B p q).candidate f).contains t) (ha : (p x).contains a) :
    (q x (gridApplication r A B f x)).contains (.app t a) :=
  (ht.2 ⟨x, hx⟩).2 a ha

noncomputable def positiveGridPiType (R : Nat) (hR : 0 < R) (A : CausalGridType R)
    (B : CausalGridFamily R) : CausalGridType R := by
  cases R with
  | zero => omega
  | succ r => exact gridPiType r A B

noncomputable def positiveGridPiPredicate (R : Nat) (hR : 0 < R) (A : CausalGridType R)
    (B : CausalGridFamily R) (p : TowerFamily (carrierGrid R) → Candidate)
    (q : TowerFamily (carrierGrid R) → TowerFamily (carrierGrid R) → Candidate) : CausalGridPredicate R := by
  cases R with
  | zero => omega
  | succ r => exact gridPiPredicate r A B p q

theorem positiveGridPiType_formed (R : Nat) (hR : 0 < R) (A : CausalGridType R) (B : CausalGridFamily R)
    (hr : Rl sA sB sC) (hA : A.Formed sA)
    (hB : ∀ a, A.Coherent (R + 1) (Nat.le_refl _) a → (B.fiber a).Formed sB) :
    (positiveGridPiType R hR A B).Formed sC := by
  cases R with
  | zero => omega
  | succ r => exact gridPiType_formed_coherent r A B hr hA hB

/-- For a predicative product, reifying and then decoding its carrier is
exact on coherent function values. The original product premises discharge
formation; no projection or image hypothesis is left to the caller. -/
theorem gridPi_universe_decode (r k : Nat) (A : CausalGridType (r + 1 + k))
    (B : CausalGridFamily (r + 1 + k))
    (p : TowerFamily (carrierGrid (r + 1 + k)) → Candidate)
    (q : TowerFamily (carrierGrid (r + 1 + k)) → TowerFamily (carrierGrid (r + 1 + k)) → Candidate)
    (hr : Rl sA sB (.type r)) (hA : A.Formed sA)
    (hB : ∀ a, A.Coherent (r + 2 + k) (by omega) a → (B.fiber a).Formed sB)
    (d : Nat) (hd : d ≤ r) (f : TowerFamily (carrierGrid (r + 1 + k)))
    (hf : (positiveGridPiType (r + 1 + k) (by omega) A B).Coherent (d + 1 + k) (by omega) f) :
    let C := positiveGridPiType (r + 1 + k) (by omega) A B
    let J := positiveGridPiPredicate (r + 1 + k) (by omega) A B p q
    (universeTypePrefix r k C d (by omega)).readCodeFamily hd k
      (universeReify r k C J d) (universeArgumentSlice r k f) = C.code (d + 1 + k) (by omega) f := by
  apply universeReify_decode r k _ _ (positiveGridPiType_formed _ _ A B hr hA ?_) d hd f hf
  intro a ha
  exact hB a (ha.mono (by omega))

theorem gridPi_universe_candidate (r k : Nat) (A : CausalGridType (r + 1 + k))
    (B : CausalGridFamily (r + 1 + k))
    (p : TowerFamily (carrierGrid (r + 1 + k)) → Candidate)
    (q : TowerFamily (carrierGrid (r + 1 + k)) → TowerFamily (carrierGrid (r + 1 + k)) → Candidate)
    (hr : Rl sA sB (.type r)) (hA : A.Formed sA)
    (hB : ∀ a, A.Coherent (r + 2 + k) (by omega) a → (B.fiber a).Formed sB)
    (f : TowerFamily (carrierGrid (r + 1 + k)))
    (hf : (positiveGridPiType (r + 1 + k) (by omega) A B).Coherent (r + 2 + k) (by omega) f) :
    let C := positiveGridPiType (r + 1 + k) (by omega) A B
    let J := positiveGridPiPredicate (r + 1 + k) (by omega) A B p q
    (universeTypePrefix r k C (r + 1) (Nat.le_refl _)).readCandidateFamily k
      (universeReify r k C J (r + 1)) (universeArgumentSlice r k f) = J.candidate f := by
  apply universeReify_candidate r k _ _ (positiveGridPiType_formed _ _ A B hr hA ?_) f hf
  intro a ha
  exact hB a (ha.mono (by omega))

/-- The impredicative product case uses the same candidate and its actual
application operation, with the separate proposition universe decoder. -/
theorem gridPi_prop_candidate (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (p : TowerFamily (carrierGrid (r + 1)) → Candidate)
    (q : TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → Candidate)
    (hA : A.Formed sA)
    (hB : ∀ a, A.Coherent (r + 2) (Nat.le_refl _) a → (B.fiber a).Formed .prop)
    (f : TowerFamily (carrierGrid (r + 1))) (hf : (gridPiType r A B).Coherent (r + 2) (Nat.le_refl _) f) :
    propValueCandidate (r + 1) (propReifyValues (r + 1) (gridPiPredicate r A B p q)) =
      (gridPiPredicate r A B p q).candidate f :=
  propReifyValues_candidate (r + 1) _ _ (gridPiType_formed_coherent r A B (Rl.prop sA) hA hB) f hf

end Submission.Helpers
