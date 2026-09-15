import Submission.SourceContextPrefixes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem finiteTypeApplication_prefix_coherent (r d : Nat) (hd : d ≤ r + 2)
    (A : FiniteGridType (r + 1)) (B : FiniteGridFamily (r + 1))
    (f a : FiniteGridValue (r + 1))
    (ha : A.carrier.Coherent d hd (FiniteGridValue.toTower _ a)) :
    (B.fiber a).carrier.Coherent d hd (FiniteGridValue.toTower _ (finiteTypeApplication r A B f a)) := by
  let b := A.normalizeValue a
  have hb : A.Valid b := A.normalizeValue_valid a
  have hba := A.normalizeValue_recover_prefix d hd a ha
  have hB : FiniteGridCodeEqBelow d (B.fiber b) (B.fiber a) :=
    fun j hj hjd v hv => B.causal j hj b a (hba.toTower.mono (by omega)) v
  have hv := hB.coherent_forward d hd (Nat.le_refl _) _
    ((finiteTypeApplication_valid r A B f b hb).mono (hd := Nat.le_refl (r + 2)) hd)
  have he := finiteTypeApplication_prefix_congr r d hd A A B B
    ((FiniteGridTypeEq.refl A).codeEqBelow d) (fun x _ => (FiniteGridTypeEq.refl (B.fiber x)).codeEqBelow d)
    f f b a (fun _ _ => rfl) hba
  exact hv.congr he.toTower

/-- The lambda cast is inert at any depth from preceding carrier
conversion. No source reduction or substitution at that depth is assumed. -/
theorem sourceGridEval_lam_native_prefix (F : SourceCarrierConversion r d P)
    (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hρ : P Γ ρ)
    (hExt : ∀ x, (sourceGridInterpretation r Γ ρ A).Valid x → P (A :: Γ) (push x ρ)) :
    FiniteGridValue.Agree d (sourceGridEval r Γ ρ (.lam A b)) (sourceGridNativeLambda r Γ ρ A b) := by
  have hf : BoundedTyping (r + 2) Γ (.lam A b) (.pi A B) := .lam hPi hb hPi.sort_bound
  have hChosen := chosenType_typing hf
  have hOuter := F.convert hChosen.type_expression hf.type_expression hρ
    (typing_unique hChosen.forget hf.forget)
  have hBody (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Γ ρ A).Valid x) :=
    F.convert hb.type_expression (chosenType_typing hb).type_expression (hExt x hx)
      (typing_unique hb.forget (chosenType_typing hb).forget)
  have hPiCode : FiniteGridCodeEqBelow d (sourceGridInterpretation r Γ ρ (.pi A B))
      (sourceGridInterpretation r Γ ρ (.pi A (chosenType (r + 2) (A :: Γ) b))) := by
    rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
    intro j hj hjd v hv
    exact finitePiType_carrier_below_eq r d _ _ _ _
      ((FiniteGridTypeEq.refl _).codeEqBelow d) hBody j hj hjd v
  have hNative : (sourceGridInterpretation r Γ ρ (.pi A (chosenType (r + 2) (A :: Γ) b))).Valid
      (sourceGridNativeLambda r Γ ρ A b) := by
    rw [sourceGridInterpretation_pi]
    exact finiteTypeLambda_valid r _ _ _
  rw [sourceGridEval_lam_normalize]
  exact FiniteGridType.normalizeValue_recover_prefix _ d F.depth _
    ((hOuter.trans hPiCode).coherent_backward d F.depth (Nat.le_refl _) _
      (hNative.mono (hd := Nat.le_refl (r + 2)) F.depth))

theorem sourceGridEval_lam_native_second (hPi : BoundedTyping (r + 2) Γ (.pi A B) (.srt s))
    (hb : BoundedTyping (r + 2) (A :: Γ) b B) (hρ : SourceGridContextFirst r Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.lam A b)) (sourceGridNativeLambda r Γ ρ A b) :=
  sourceGridEval_lam_native_prefix (sourceCarrierConversionFirst r) hPi hb hρ
    (fun _x hx => hρ.up (sourceGridValid_arity hx))

theorem sourceGridEval_app_native_second (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (ha : BoundedTyping (r + 2) Γ a A) (hρ : SourceGridContextFirst r Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (.app f a)) (sourceGridNativeApp r Γ ρ f a) := by
  have hF := chosenProduct_typing hf
  obtain ⟨sPi, hPi⟩ := hF.pi_type
  obtain ⟨sD, hD, hsD⟩ := hPi.pi_domain
  obtain ⟨sC, hC, hsC⟩ := hPi.pi_codomain
  have haD := BoundedTyping.conv ha hD (conv_symm (chosenProduct_conv hf).1) hsD
  have hApp := BoundedTyping.app hF haD
  have hChosen := chosenType_typing (BoundedTyping.app hf ha)
  have hOuter := sourceGrid_type_conv_first hChosen.type_expression hApp.type_expression hρ
    (typing_unique hChosen.forget hApp.forget)
  have hSub := sourceGridInterpretation_subst_first hC hD haD hρ
  have hNative := finiteTypeApplication_prefix_coherent r 2 (by omega)
    (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1)
    ((sourceGridMeaning r (chosenProduct (r + 2) Γ f).2).bodyFamily Γ ρ (chosenProduct (r + 2) Γ f).1)
    (sourceGridEval r Γ ρ f) (sourceGridEval r Γ ρ a) (sourceGridEval_coherent_second haD hρ)
  rw [sourceGridEval_app_normalize]
  exact FiniteGridType.normalizeValue_recover_prefix _ 2 (by omega) _
    ((hOuter.code.trans hSub).coherent_backward 2 (by omega) (Nat.le_refl _) _ hNative)

theorem sourceGridChosenProduct_first (hf : BoundedTyping (r + 2) Γ f (.pi A B))
    (hρ : SourceGridContextFirst r Γ ρ) :
    SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1)
      (sourceGridInterpretation r Γ ρ A) ∧
    (∀ x, (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1).Valid x →
      SourceTypeEqPrefix 1
        (sourceGridInterpretation r ((chosenProduct (r + 2) Γ f).1 :: Γ) (push x ρ) (chosenProduct (r + 2) Γ f).2)
        (sourceGridInterpretation r (A :: Γ) (push x ρ) B)) := by
  have hF := chosenProduct_typing hf
  obtain ⟨sPi, hPi⟩ := hF.pi_type
  obtain ⟨sD, hD, hsD⟩ := hPi.pi_domain
  obtain ⟨sC, hC, hsC⟩ := hPi.pi_codomain
  obtain ⟨sPi', hPi'⟩ := hf.pi_type
  obtain ⟨sA, hA, hsA⟩ := hPi'.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi'.pi_codomain
  have hc := chosenProduct_conv hf
  refine ⟨sourceGrid_type_conv_first (.inl ⟨sD, hD⟩) (.inl ⟨sA, hA⟩) hρ hc.1, ?_⟩
  intro x hx
  have hctx := hρ.up (sourceGridValid_arity hx)
  have hB' := hB.context_conv hA hD hsA (conv_symm hc.1)
  have hCod := sourceGrid_type_conv_first (.inl ⟨sC, hC⟩) (.inl ⟨sB, hB'⟩) hctx hc.2
  exact hCod.trans ((sourceGrid_context_conversion_first hB hA hD (conv_symm hc.1) hctx).2 sB hB)

end Submission.Helpers
