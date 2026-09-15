import Submission.SourceContextConversionFirst

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem FiniteGridType.normalizeValue_recover_prefix (A : FiniteGridType R)
    (d : Nat) (hd : d ≤ R + 1) (a : FiniteGridValue R)
    (ha : A.carrier.Coherent d hd (FiniteGridValue.toTower R a)) :
    FiniteGridValue.Agree d (A.normalizeValue a) a := by
  intro i hi
  exact (A.carrier.complete_recover d hd _ ha i.val hi).trans (FiniteGridValue.toTower_at R a i)

theorem finiteTypeLambda_beta_prefix (r d : Nat) (hd : d ≤ r + 2)
    (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1)) (F : FiniteGridMap (r + 1))
    (hF : ∀ a, A.Valid a → (B.fiber a).Valid (F.eval a))
    (a : FiniteGridValue (r + 1)) (ha : A.carrier.Coherent d hd (FiniteGridValue.toTower _ a)) :
    FiniteGridValue.Agree d (finiteTypeApplication r A B (finiteTypeLambda r A B F) a) (F.eval a) := by
  let b := A.normalizeValue a
  have hb : A.Valid b := A.normalizeValue_valid a
  have hba : FiniteGridValue.Agree d b a := A.normalizeValue_recover_prefix d hd a ha
  have hApp := finiteTypeApplication_prefix_congr r d hd A A B B
    ((FiniteGridTypeEq.refl A).codeEqBelow d) (fun x _ => (FiniteGridTypeEq.refl (B.fiber x)).codeEqBelow d)
    (finiteTypeLambda r A B F) (finiteTypeLambda r A B F) b a (fun _ _ => rfl) hba
  intro i hi
  exact (hApp i hi).symm.trans ((congrFun (finiteTypeLambda_beta r A B F hF b hb) i).trans
    (F.causal i.val (Nat.le_of_lt_succ i.isLt) b a (hba.toTower.mono (by omega))))

theorem sourceGridNativeLambda_beta_prefix (r d : Nat) (hd : d ≤ r + 2)
    (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (A b : Tm) (x : FiniteGridValue (r + 1))
    (hx : (sourceGridInterpretation r Γ ρ A).carrier.Coherent d hd (FiniteGridValue.toTower _ x)) :
    FiniteGridValue.Agree d
      (sourceGridApply r Γ ρ A (chosenType (r + 2) (A :: Γ) b) (sourceGridNativeLambda r Γ ρ A b) x)
      (sourceGridEval r (A :: Γ) (push x ρ) b) :=
  finiteTypeLambda_beta_prefix r d hd _ _ _ (fun a _ => sourceGridEval_inferred r (A :: Γ) (push a ρ) b) x hx

theorem finiteTypeApplication_zero_code (r : Nat) (A : FiniteGridType (r + 1))
    (B : FiniteGridFamily (r + 1)) (f a : FiniteGridValue (r + 1)) :
    (finiteTypeApplication r A B f a ⟨0, by omega⟩).code =
      (B.fiber a).carrier.code 0 (by omega) (TowerFamily.point (carrierGrid (r + 1))) := by
  change (gridApplication r A.carrier B.toCausal _ _ 0).code = _
  rw [gridApplication_at r A.carrier B.toCausal 0 (by omega)]
  change (B.fiber (FiniteGridValue.ofTower _ (TowerFamily.point (carrierGrid (r + 1))))).carrier.code 0 (by omega)
    (TowerFamily.point (carrierGrid (r + 1))) = _
  exact B.causal 0 (by omega) _ a (by intro i hi; omega) _

theorem sourceGridNativeApp_zero_code (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (f a : Tm) :
    (sourceGridNativeApp r Γ ρ f a ⟨0, by omega⟩).code =
      arityAt (.type r) (chosenProduct (r + 2) Γ f).2 := by
  unfold sourceGridNativeApp
  rw [finiteTypeApplication_zero_code]
  exact sourceGridInterpretation_zero r _ _ _ _

theorem sourceGridEval_app_native_zero (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (ha : BoundedTyping (r + 2) Γ a A) (ρ : GridEnvironment (r + 1)) :
    sourceGridEval r Γ ρ (.app f a) ⟨0, by omega⟩ = sourceGridNativeApp r Γ ρ f a ⟨0, by omega⟩ := by
  obtain ⟨sPi, hPi⟩ := hf.pi_type
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [sourceGridEval_app_coordinate]
  unfold FiniteGridType.forceCoordinate
  rw [sourceGridInterpretation_zero]
  have hc : arityAt (.type r) (chosenType (r + 2) Γ (.app f a)) =
      arityAt (.type r) (chosenProduct (r + 2) Γ f).2 :=
    (inferredArityAt_eq (.app hf ha) rfl).trans
      ((arityAt_subst (ha.not_kindAt hA rfl) B).trans (chosenProduct_arity_components hf rfl).2.symm)
  rw [hc]
  exact (sourceGridNativeApp r Γ ρ f a ⟨0, by omega⟩).mk_cast (sourceGridNativeApp_zero_code r Γ ρ f a)

theorem sourceGridNativeLambda_zero_code (r : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (A b : Tm) :
    (sourceGridNativeLambda r Γ ρ A b ⟨0, by omega⟩).code =
      arityAt (.type r) (.pi A (chosenType (r + 2) (A :: Γ) b)) := by
  have hv := finiteTypeLambda_valid r (sourceGridInterpretation r Γ ρ A)
    ((sourceGridMeaning r (chosenType (r + 2) (A :: Γ) b)).bodyFamily Γ ρ A)
    ((sourceGridMeaning r b).bodyMap Γ ρ A)
  have hc := hv 0 (Nat.zero_lt_succ _)
  rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, ← sourceGridInterpretation_pi,
    sourceGridInterpretation_zero] at hc
  exact hc

theorem sourceGridEval_lam_native_zero (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (ρ : GridEnvironment (r + 1)) :
    sourceGridEval r Γ ρ (.lam A b) ⟨0, by omega⟩ = sourceGridNativeLambda r Γ ρ A b ⟨0, by omega⟩ := by
  rw [sourceGridEval_lam_coordinate]
  unfold FiniteGridType.forceCoordinate
  rw [sourceGridInterpretation_zero]
  have hc : arityAt (.type r) (chosenType (r + 2) Γ (.lam A b)) =
      arityAt (.type r) (.pi A (chosenType (r + 2) (A :: Γ) b)) := by
    rw [show arityAt (.type r) (chosenType (r + 2) Γ (.lam A b)) = arityAt (.type r) (.pi A B)
      from inferredArityAt_eq (.lam hPi hb hPi.sort_bound) rfl]
    exact congrArg (fun C => (arityAt (.type r) A).arrow C) (inferredArityAt_eq hb rfl).symm
  rw [hc]
  exact (sourceGridNativeLambda r Γ ρ A b ⟨0, by omega⟩).mk_cast (sourceGridNativeLambda_zero_code r Γ ρ A b)

/-- Actual source beta equality at the first value coordinate, uniformly in
the finite universe bound. All casts and the substitution are discharged. -/
theorem sourceGridEval_beta_zero (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridContextFirst r Γ ρ) :
    sourceGridEval r Γ ρ (.app (.lam A b) a) ⟨0, by omega⟩ =
      sourceGridEval r Γ ρ (subst 0 a b) ⟨0, by omega⟩ := by
  have hf : BoundedTyping (r + 2) Γ (.lam A b) (.pi A B) := .lam hPi hb hPi.sort_bound
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  have hp := chosenProduct_arity_components hf (q := .type r) rfl
  have hOp : FiniteGridValue.Agree 1 (sourceGridNativeApp r Γ ρ (.lam A b) a)
      (sourceGridApply r Γ ρ A (chosenType (r + 2) (A :: Γ) b)
        (sourceGridNativeLambda r Γ ρ A b) (sourceGridEval r Γ ρ a)) := by
    unfold sourceGridNativeApp sourceGridApply
    apply finiteTypeApplication_prefix_congr r 1 (by omega)
    · exact sourceGridCode_first_of_arity r _ _ _ _ _ _ hp.1
    · intro x hx
      exact sourceGridCode_first_of_arity r _ _ _ _ _ _ (hp.2.trans (inferredArityAt_eq hb rfl).symm)
    · exact FiniteGridValue.agree_one (sourceGridEval_lam_native_zero hPi hb ρ)
    · intro i hi; rfl
  have hx : (sourceGridInterpretation r Γ ρ A).carrier.Coherent 1 (by omega)
      (FiniteGridValue.toTower _ (sourceGridEval r Γ ρ a)) := by
    intro j hj
    have he : j = 0 := by omega
    subst j
    rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero]
    exact sourceGridEval_arity ha ρ
  exact (sourceGridEval_app_native_zero hf ha ρ).trans
    ((hOp ⟨0, by omega⟩ (Nat.zero_lt_succ 0)).trans
      ((sourceGridNativeLambda_beta_prefix r 1 (by omega) Γ ρ A b _ hx ⟨0, by omega⟩ (Nat.zero_lt_succ 0)).trans
        (sourceGridEval_subst_zero hb hA ha hρ).symm))

end Submission.Helpers
