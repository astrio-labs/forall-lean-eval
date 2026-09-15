import Submission.FiniteGridOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem FiniteGridValue.project_congr (R d : Nat) (hd : d ≤ R + 1)
    (v w : TowerFamily (carrierGrid R)) (h : TowerFamily.AgreeBelow d v w) :
    TowerFamily.AgreeBelow d (toTower R (ofTower R v)) (toTower R (ofTower R w)) :=
  fun i hi => (toTower_ofTower R v i (by omega)).trans
    ((h i hi).trans (toTower_ofTower R w i (by omega)).symm)

/-- The semantic data of a type consist of causal carriers and a candidate
on finite values. Formation and source typing are separate propositions. -/
structure FiniteGridType (R : Nat) where
  carrier : CausalGridType R
  candidate : FiniteGridValue R → Candidate

def FiniteGridType.Valid (A : FiniteGridType R) (v : FiniteGridValue R) : Prop := A.carrier.Valid v
def FiniteGridType.Formed (A : FiniteGridType R) (s : Srt) : Prop := A.carrier.Formed s

noncomputable def FiniteGridType.point (A : FiniteGridType R) : FiniteGridValue R := A.carrier.finitePoint

theorem FiniteGridType.point_valid (A : FiniteGridType R) : A.Valid A.point := A.carrier.finitePoint_valid

noncomputable def FiniteGridType.sort (R : Nat) (s : Srt) : FiniteGridType R where
  carrier := uniformSortType R s
  candidate _ := Candidate.sn

theorem FiniteGridType.sort_formed (R : Nat) (hAx : Ax s s') : (FiniteGridType.sort R s).Formed s' :=
  uniformSortType_formed R hAx

/-- The carrier of a dependent family at coordinate `j` only depends on
the first `j` coordinates of its domain argument. -/
structure FiniteGridFamily (R : Nat) where
  fiber : FiniteGridValue R → FiniteGridType R
  causal : ∀ j hj x y,
    TowerFamily.AgreeBelow j (FiniteGridValue.toTower R x) (FiniteGridValue.toTower R y) →
    ∀ v, (fiber x).carrier.code j hj v = (fiber y).carrier.code j hj v

def FiniteGridFamily.toCausal (B : FiniteGridFamily R) : CausalGridFamily R where
  fiber x := (B.fiber (FiniteGridValue.ofTower R x)).carrier
  causal j hj x y h v := B.causal j hj _ _ (FiniteGridValue.project_congr R j (by omega) x y h) v

noncomputable def finiteTypeApplication (r : Nat) (A : FiniteGridType (r + 1))
    (B : FiniteGridFamily (r + 1)) (f a : FiniteGridValue (r + 1)) : FiniteGridValue (r + 1) :=
  finiteGridApplication r A.carrier B.toCausal f a

noncomputable def finitePiType (r : Nat) (A : FiniteGridType (r + 1))
    (B : FiniteGridFamily (r + 1)) : FiniteGridType (r + 1) where
  carrier := gridPiType r A.carrier B.toCausal
  candidate f := Candidate.inter (fun x : {a // A.Valid a} =>
    (A.candidate x.1).arrow ((B.fiber x.1).candidate (finiteTypeApplication r A B f x.1)))

theorem finiteTypeApplication_valid (r : Nat) (A : FiniteGridType (r + 1))
    (B : FiniteGridFamily (r + 1)) (f a : FiniteGridValue (r + 1)) (ha : A.Valid a) :
    (B.fiber a).Valid (finiteTypeApplication r A B f a) := by
  have h := finiteGridApplication_valid r A.carrier B.toCausal f a ha
  change (B.fiber a).carrier.Valid (finiteGridApplication r A.carrier B.toCausal f a)
  simpa only [FiniteGridFamily.toCausal, FiniteGridValue.ofTower_toTower] using h

theorem finitePiType_formed (r : Nat) (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (hr : Rl sA sB sC) (hA : A.Formed sA) (hB : ∀ a, A.Valid a → (B.fiber a).Formed sB) :
    (finitePiType r A B).Formed sC :=
  gridPiType_formed_coherent r A.carrier B.toCausal hr hA
    (fun a ha => hB (FiniteGridValue.ofTower (r + 1) a) (A.carrier.valid_ofTower a ha))

theorem finitePiType_candidate_apply (r : Nat) (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (f x : FiniteGridValue (r + 1)) (hx : A.Valid x)
    (ht : ((finitePiType r A B).candidate f).contains t) (ha : (A.candidate x).contains a) :
    ((B.fiber x).candidate (finiteTypeApplication r A B f x)).contains (.app t a) :=
  (ht.2 ⟨x, hx⟩).2 a ha

structure FiniteGridMap (R : Nat) where
  eval : FiniteGridValue R → FiniteGridValue R
  causal : ∀ j (hj : j ≤ R) a b,
    TowerFamily.AgreeBelow (j + 1) (FiniteGridValue.toTower R a) (FiniteGridValue.toTower R b) →
    eval a ⟨j, Nat.lt_succ_of_le hj⟩ = eval b ⟨j, Nat.lt_succ_of_le hj⟩

def FiniteGridMap.toCausal (F : FiniteGridMap R) : CausalGridMap R where
  eval a := FiniteGridValue.toTower R (F.eval (FiniteGridValue.ofTower R a))
  causal j hj a b h := by
    rw [FiniteGridValue.toTower_at R _ ⟨j, Nat.lt_succ_of_le hj⟩,
      FiniteGridValue.toTower_at R _ ⟨j, Nat.lt_succ_of_le hj⟩]
    exact F.causal j hj _ _ (FiniteGridValue.project_congr R (j + 1) (by omega) a b h)

noncomputable def finiteTypeLambda (r : Nat) (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (F : FiniteGridMap (r + 1)) : FiniteGridValue (r + 1) :=
  finiteGridLambda r A.carrier B.toCausal F.toCausal

theorem finiteTypeLambda_valid (r : Nat) (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (F : FiniteGridMap (r + 1)) : (finitePiType r A B).Valid (finiteTypeLambda r A B F) :=
  finiteGridLambda_valid r A.carrier B.toCausal F.toCausal

theorem finiteTypeLambda_beta (r : Nat) (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (F : FiniteGridMap (r + 1)) (hF : ∀ a, A.Valid a → (B.fiber a).Valid (F.eval a))
    (a : FiniteGridValue (r + 1)) (ha : A.Valid a) :
    finiteTypeApplication r A B (finiteTypeLambda r A B F) a = F.eval a := by
  have hf : ∀ x, A.carrier.Coherent (r + 2) (Nat.le_refl _) x →
      (B.toCausal.fiber x).Coherent (r + 2) (Nat.le_refl _) (F.toCausal.eval x) :=
    fun x hx => hF (FiniteGridValue.ofTower (r + 1) x) (A.carrier.valid_ofTower x hx)
  have h := finiteGridLambda_beta r A.carrier B.toCausal F.toCausal hf a ha
  change finiteGridApplication r A.carrier B.toCausal
    (finiteGridLambda r A.carrier B.toCausal F.toCausal) a = F.eval a
  simpa only [FiniteGridMap.toCausal, FiniteGridValue.ofTower_toTower] using h

theorem finitePiType_candidate_lambda (r : Nat) (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (F : FiniteGridMap (r + 1)) (hF : ∀ a, A.Valid a → (B.fiber a).Valid (F.eval a))
    (hD : SN D)
    (hb : ∀ x, A.Valid x → ∀ a, (A.candidate x).contains a →
      ((B.fiber x).candidate (F.eval x)).contains (subst 0 a b)) :
    ((finitePiType r A B).candidate (finiteTypeLambda r A B F)).contains (.lam D b) := by
  have hh (x : {a // A.Valid a}) :
      ((A.candidate x.1).arrow
        ((B.fiber x.1).candidate (finiteTypeApplication r A B (finiteTypeLambda r A B F) x.1))).contains (.lam D b) := by
    rw [finiteTypeLambda_beta r A B F hF x.1 x.2]
    exact Candidate.lambda _ _ hD (hb x.1 x.2)
  exact ⟨(hh ⟨A.point, A.point_valid⟩).1, hh⟩

end Submission.Helpers
