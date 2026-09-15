import Submission.GridBeta

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

def FiniteGridValue.toTower (R : Nat) (v : FiniteGridValue R) : TowerFamily (carrierGrid R) :=
  fun i => if hi : i < R + 1 then v ⟨i, hi⟩ else TowerFamily.point (carrierGrid R) i

theorem FiniteGridValue.toTower_at (R : Nat) (v : FiniteGridValue R) (i : Fin (R + 1)) :
    toTower R v i.val = v i := by
  unfold toTower
  rw [dif_pos i.isLt]

theorem FiniteGridValue.ofTower_toTower (R : Nat) (v : FiniteGridValue R) :
    ofTower R (toTower R v) = v := funext (fun i => toTower_at R v i)

theorem FiniteGridValue.toTower_ofTower (R : Nat) (v : TowerFamily (carrierGrid R)) :
    TowerFamily.AgreeBelow (R + 1) (toTower R (ofTower R v)) v := by
  intro i hi
  exact toTower_at R (ofTower R v) ⟨i, hi⟩

theorem CausalGridType.Coherent.congr {A : CausalGridType R} {v w : TowerFamily (carrierGrid R)}
    (hv : A.Coherent d hd v) (h : TowerFamily.AgreeBelow d v w) : A.Coherent d hd w := by
  intro i hi
  exact (congrArg TowerValue.code (h i hi).symm).trans
    ((hv i hi).trans (A.causal i (by omega) v w (h.mono (by omega))))

def CausalGridType.Valid (A : CausalGridType R) (v : FiniteGridValue R) : Prop :=
  A.Coherent (R + 1) (Nat.le_refl _) (FiniteGridValue.toTower R v)

theorem CausalGridType.valid_ofTower (A : CausalGridType R) (v : TowerFamily (carrierGrid R))
    (hv : A.Coherent (R + 1) (Nat.le_refl _) v) : A.Valid (FiniteGridValue.ofTower R v) :=
  hv.congr (fun i hi => (FiniteGridValue.toTower_ofTower R v i hi).symm)

noncomputable def CausalGridType.finitePoint (A : CausalGridType R) : FiniteGridValue R :=
  FiniteGridValue.ofTower R (A.normalize (R + 1) (Nat.le_refl _) (TowerFamily.point (carrierGrid R)))

theorem CausalGridType.finitePoint_valid (A : CausalGridType R) : A.Valid A.finitePoint :=
  A.valid_ofTower _ (A.normalize_coherent _ _ _)

/-- A candidate function on finite semantic values is automatically causal
when viewed on an ambient tower. -/
def CausalGridPredicate.ofFinite (R : Nat) (p : FiniteGridValue R → Candidate) : CausalGridPredicate R where
  candidate v := p (FiniteGridValue.ofTower R v)
  causal v w h := congrArg p (FiniteGridValue.ofTower_congr R v w h)

noncomputable def finiteGridApplication (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) (f a : FiniteGridValue (r + 1)) : FiniteGridValue (r + 1) :=
  FiniteGridValue.ofTower (r + 1) (gridApplication r A B
    (FiniteGridValue.toTower (r + 1) f) (FiniteGridValue.toTower (r + 1) a))

noncomputable def finiteGridLambda (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) (F : CausalGridMap (r + 1)) : FiniteGridValue (r + 1) :=
  FiniteGridValue.ofTower (r + 1) (gridLambda r A B F)

theorem finiteGridApplication_valid (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) (f a : FiniteGridValue (r + 1)) (ha : A.Valid a) :
    (B.fiber (FiniteGridValue.toTower (r + 1) a)).Valid (finiteGridApplication r A B f a) :=
  (B.fiber _).valid_ofTower _ (gridApplication_coherent r A B _ _ ha)

theorem finiteGridLambda_valid (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) (F : CausalGridMap (r + 1)) :
    (gridPiType r A B).Valid (finiteGridLambda r A B F) :=
  (gridPiType r A B).valid_ofTower _ (gridLambda_coherent r A B F)

theorem finiteGridLambda_beta (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (F : CausalGridMap (r + 1))
    (hF : ∀ a, A.Coherent (r + 2) (Nat.le_refl _) a →
      (B.fiber a).Coherent (r + 2) (Nat.le_refl _) (F.eval a))
    (a : FiniteGridValue (r + 1)) (ha : A.Valid a) :
    finiteGridApplication r A B (finiteGridLambda r A B F) a =
      FiniteGridValue.ofTower (r + 1) (F.eval (FiniteGridValue.toTower (r + 1) a)) := by
  have he := (gridApplicationPrefix r A B (r + 2) (Nat.le_refl _)).congr
    _ (gridLambda r A B F) _ (FiniteGridValue.toTower (r + 1) a)
    (FiniteGridValue.toTower_ofTower (r + 1) (gridLambda r A B F)) (.refl _ _)
  exact (congrArg (FiniteGridValue.ofTower (r + 1)) he).trans (gridLambda_beta_finite r A B F hF _ ha)

end Submission.Helpers
