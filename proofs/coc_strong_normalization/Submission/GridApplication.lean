import Submission.GridBinding

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem TowerFamily.AgreeBelow.refl {S : Nat → CarrierSystem} (v : TowerFamily S) (d : Nat) :
    AgreeBelow d v v := fun _ _ => rfl

theorem TowerFamily.AgreeBelow.mono {S : Nat → CarrierSystem} {v w : TowerFamily S}
    (h : AgreeBelow d v w) (he : e ≤ d) : AgreeBelow e v w := fun i hi => h i (by omega)

theorem CarrierTelescope.project_congr {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (hT : T.All (fun i => i < d)) (v w : TowerFamily V) (h : TowerFamily.AgreeBelow d v w) :
    T.project R v = T.project R w := by
  induction T with
  | nil => rfl
  | cons i A B ih =>
    simp only [project]
    rw [h i hT.1]
    let x := ((R i).values A).decode ((w i).cast ((R i).code A))
    exact congrArg (fun y : (B x).El => (⟨x, y⟩ : (z : (S i).El A) × (B z).El)) (ih x (hT.2 x))

theorem CausalGridType.arguments_congr (A : CausalGridType R) (d : Nat) (hd : d ≤ R + 1)
    (v w : TowerFamily (carrierGrid R)) (h : TowerFamily.AgreeBelow d v w) :
    (A.arguments d hd).decode v = (A.arguments d hd).decode w :=
  (A.telescopeAt d hd).telescope.project_congr _ (A.telescopeAt d hd).ordered.all v w h

/-- The first `d` application values have been constructed. Each value
uses only its own and earlier function/argument coordinates. -/
structure GridApplicationPrefix (R d : Nat) where
  eval : TowerFamily (carrierGrid R) → TowerFamily (carrierGrid R) → TowerFamily (carrierGrid R)
  causal : ∀ j, j < d → ∀ f g a b,
    TowerFamily.AgreeBelow (j + 1) f g → TowerFamily.AgreeBelow (j + 1) a b → eval f a j = eval g b j
  trivial : ∀ f a j, d ≤ j → eval f a j = TowerFamily.point (carrierGrid R) j

theorem GridApplicationPrefix.congr (O : GridApplicationPrefix R d)
    (f g a b : TowerFamily (carrierGrid R))
    (hf : TowerFamily.AgreeBelow d f g) (ha : TowerFamily.AgreeBelow d a b) : O.eval f a = O.eval g b := by
  funext j
  by_cases hj : j < d
  · exact O.causal j hj f g a b (hf.mono (by omega)) (ha.mono (by omega))
  · rw [O.trivial f a j (by omega), O.trivial g b j (by omega)]

def GridApplicationPrefix.empty (R : Nat) : GridApplicationPrefix R 0 where
  eval _ _ := TowerFamily.point (carrierGrid R)
  causal _ h := by omega
  trivial _ _ _ _ := rfl

theorem gridPiCode_causal (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1) (O : GridApplicationPrefix (r + 1) j) :
    TowerFamily.DependsBelow j (gridPiCode r A B j hj O.eval) := by
  intro f g hfg
  have he : O.eval f = O.eval g := funext (fun a => O.congr f g a a hfg (.refl a j))
  unfold gridPiCode gridPiCodomain
  rw [he]

theorem gridPiApplyAt_congr (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1) (O : GridApplicationPrefix (r + 1) j)
    (f g a b : TowerFamily (carrierGrid (r + 1)))
    (hf : TowerFamily.AgreeBelow (j + 1) f g) (ha : TowerFamily.AgreeBelow (j + 1) a b) :
    gridPiApplyAt r A B j hj O.eval f a = gridPiApplyAt r A B j hj O.eval g b := by
  have hp := A.arguments_congr j (by omega) a b (ha.mono (by omega))
  have he : O.eval f = O.eval g :=
    funext (fun x => O.congr f g x x (hf.mono (by omega)) (.refl x j))
  have hE : gridPiCodomain A B j hj O.eval f = gridPiCodomain A B j hj O.eval g := by
    unfold gridPiCodomain
    rw [he]
  unfold gridPiApplyAt
  rw [hp, hE, hf j (Nat.lt_succ_self _), ha j (Nat.lt_succ_self _)]

noncomputable def GridApplicationPrefix.step (O : GridApplicationPrefix (r + 1) d)
    (hd : d ≤ r + 1) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1)) :
    GridApplicationPrefix (r + 1) (d + 1) where
  eval f a := (O.eval f a).set d (gridPiApplyAt r A B d hd O.eval f a)
  causal j hj f g a b hf ha := by
    by_cases he : j = d
    · subst j
      rw [TowerFamily.set_same, TowerFamily.set_same]
      exact gridPiApplyAt_congr r A B d hd O f g a b hf ha
    · rw [TowerFamily.set_other _ d j _ he, TowerFamily.set_other _ d j _ he]
      exact O.causal j (by omega) f g a b hf ha
  trivial f a j hj := by
    rw [TowerFamily.set_other _ d j _ (by omega)]
    exact O.trivial f a j (by omega)

/-- The application operation is built by coordinate induction, before the
product type is packaged. Every recursive call decreases the coordinate. -/
noncomputable def gridApplicationPrefix (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) : (d : Nat) → d ≤ r + 2 → GridApplicationPrefix (r + 1) d
  | 0, _ => .empty (r + 1)
  | d + 1, hd => (gridApplicationPrefix r A B d (by omega)).step (by omega) A B

noncomputable def gridPiType (r : Nat) (A : CausalGridType (r + 1))
    (B : CausalGridFamily (r + 1)) : CausalGridType (r + 1) where
  code j hj := gridPiCode r A B j hj (gridApplicationPrefix r A B j (by omega)).eval
  causal j hj := gridPiCode_causal r A B j hj _

theorem gridPiType_formed (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (hr : Rl sA sB sC) (hA : A.Formed sA) (hB : ∀ a, (B.fiber a).Formed sB) :
    (gridPiType r A B).Formed sC := fun j hj f => gridPiCode_formed r A B j hj _ f hr hA hB

noncomputable def gridApplication (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1)) :
    TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) → TowerFamily (carrierGrid (r + 1)) :=
  (gridApplicationPrefix r A B (r + 2) (Nat.le_refl _)).eval

theorem gridApplicationPrefix_agree (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (e : Nat) (he : e ≤ r + 2) (d : Nat) (hd : d ≤ e) (f a : TowerFamily (carrierGrid (r + 1))) :
    TowerFamily.AgreeBelow d ((gridApplicationPrefix r A B e he).eval f a)
      ((gridApplicationPrefix r A B d (by omega)).eval f a) := by
  induction e with
  | zero => intro i hi; omega
  | succ e ih =>
    by_cases hde : d = e + 1
    · subst d; exact .refl _ _
    · intro i hi
      change ((gridApplicationPrefix r A B e (by omega)).eval f a).set e _ i = _
      rw [TowerFamily.set_other _ e i _ (by omega)]
      exact ih (by omega) (by omega) i hi

theorem gridApplication_at (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (j : Nat) (hj : j ≤ r + 1) (f a : TowerFamily (carrierGrid (r + 1))) :
    gridApplication r A B f a j =
      gridPiApplyAt r A B j hj (gridApplicationPrefix r A B j (by omega)).eval f a := by
  have h := gridApplicationPrefix_agree r A B (r + 2) (Nat.le_refl _) (j + 1) (by omega) f a j
    (Nat.lt_succ_self j)
  exact h.trans (TowerFamily.set_same _ j _)

/-- Application has the dependent codomain's carrier at every coordinate.
The argument's coherence is expressed solely by its carrier code equations. -/
theorem gridApplication_coherent (r : Nat) (A : CausalGridType (r + 1)) (B : CausalGridFamily (r + 1))
    (f a : TowerFamily (carrierGrid (r + 1))) (ha : A.Coherent (r + 2) (Nat.le_refl _) a) :
    (B.fiber a).Coherent (r + 2) (Nat.le_refl _) (gridApplication r A B f a) := by
  intro j hj
  rw [gridApplication_at r A B j (by omega)]
  change (B.fiber ((A.arguments j (by omega)).encode ((A.arguments j (by omega)).decode a))).code j (by omega)
    ((gridApplicationPrefix r A B j (by omega)).eval f
      ((A.arguments j (by omega)).encode ((A.arguments j (by omega)).decode a))) = _
  have har := A.recover j (by omega) a (fun i hi => ha i (by omega))
  rw [B.causal j (by omega) _ a har]
  rw [(gridApplicationPrefix r A B j (by omega)).congr f f _ a (.refl f j) har]
  exact ((B.fiber a).causal j (by omega) _ _
    (gridApplicationPrefix_agree r A B (r + 2) (Nat.le_refl _) j (by omega) f a)).symm

end Submission.Helpers
