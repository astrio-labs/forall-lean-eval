import Submission.SourceSubstitutionBaseTools

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- Typed simultaneous substitution at the first source stage. The kind
restriction is syntactic and is discharged for typed single substitution. -/
theorem sourceGrid_substitute_first {Γ Δ : List Tm} {t T : Tm} {σ : Nat → Tm}
    {ρ δ : GridEnvironment (r + 1)} (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    (he : GridEnvironment.SubstitutedFirst r Γ Δ σ ρ δ) :
    FiniteGridValue.Agree 1 (sourceGridEval r Δ ρ (sub σ t)) (sourceGridEval r Γ δ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix 1 (sourceGridInterpretation r Δ ρ (sub σ t)) (sourceGridInterpretation r Γ δ t)) := by
  induction t generalizing Γ T Δ σ ρ δ with
  | var j =>
    obtain ⟨C, hjC, hc⟩ := h.generation
    have hv := he.variable h.wf hσ hk hjC
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' : BoundedTyping (r + 2) Δ (σ j) (.srt s) := hs.substitute hw hσ
    have hT := sourceGridInterpretation_decode_first hs' (by have hh := hs.var_below_top; omega) ρ
    have hM := sourceTypeEqPrefix_decode (r + 1) 1 (some s) _ _ hv
    have hS : SourceTypeEqPrefix 1 (sourceGridInterpretation r Γ δ (.var j))
        (uniformUniverseDecode (r + 1) (some s) (sourceGridEval r Γ δ (.var j))) := by
      apply SourceTypeEqPrefix.of_eq
      rw [sourceGridInterpretation_decode r Γ δ (.var j) (Or.inl ⟨j, rfl⟩), typeSort_eq hs]
    exact (hT.trans hM).trans hS.symm
  | srt q =>
    obtain ⟨s, hAx, hq, hs, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.srt q) (.srt s) := .srt h.wf hAx hq hs
    have ht' : BoundedTyping (r + 2) Δ (.srt q) (.srt s) := ht.substitute hw hσ
    have hTy : SourceTypeEqPrefix 1 (sourceGridInterpretation r Δ ρ (.srt q))
        (sourceGridInterpretation r Γ δ (.srt q)) := by
      rw [sourceGridInterpretation_sort, sourceGridInterpretation_sort]
      exact SourceTypeEqPrefix.of_eq 1 rfl
    refine ⟨?_, fun _ _ => hTy⟩
    change FiniteGridValue.Agree 1 (sourceGridEval r Δ ρ (.srt q)) _
    rw [sourceGridEval_encode_normalize r Δ ρ (.srt q) (Or.inl ⟨q, rfl⟩),
      sourceGridEval_encode_normalize r Γ δ (.srt q) (Or.inl ⟨q, rfl⟩)]
    apply FiniteGridType.normalizeValue_prefix_congr _ _ 1 (by omega)
      (sourceGridInferred_sub_first h hw hσ hk ρ δ)
    rw [typeSort_eq ht', typeSort_eq ht]
    exact uniformUniverseEncode_prefix_conversion (r + 1) 1 (by omega) s _ _ hTy
      (sourceGridInterpretation_formed ht' ρ)
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hp := chosenProduct_arity_components hf (q := .type r) rfl
    have hp' := chosenProduct_arity_components (hf.substitute hw hσ) (q := .type r) rfl
    have hDom : arityAt (.type r) (chosenProduct (r + 2) Δ (sub σ f)).1 =
        arityAt (.type r) (chosenProduct (r + 2) Γ f).1 :=
      hp'.1.trans ((arityAt_sub hk A).trans hp.1.symm)
    have hCod : arityAt (.type r) (chosenProduct (r + 2) Δ (sub σ f)).2 =
        arityAt (.type r) (chosenProduct (r + 2) Γ f).2 :=
      hp'.2.trans ((arityAt_sub (upSub_not_kindAt hk) B).trans hp.2.symm)
    have hv : FiniteGridValue.Agree 1 (sourceGridEval r Δ ρ (.app (sub σ f) (sub σ a)))
        (sourceGridEval r Γ δ (.app f a)) := by
      rw [sourceGridEval_app_normalize, sourceGridEval_app_normalize]
      apply FiniteGridType.normalizeValue_prefix_congr _ _ 1 (by omega)
        (sourceGridInferred_sub_first h hw hσ hk ρ δ)
      unfold sourceGridNativeApp
      apply finiteTypeApplication_prefix_congr r 1 (by omega)
      · exact sourceGridCode_first_of_arity r _ _ _ _ _ _ hDom
      · intro x hx
        exact sourceGridCode_first_of_arity r _ _ _ _ _ _ hCod
      · exact (ihf hf hw hσ hk he).1
      · exact (iha ha hw hσ hk he).1
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' : BoundedTyping (r + 2) Δ (.app (sub σ f) (sub σ a)) (.srt s) := hs.substitute hw hσ
    change SourceTypeEqPrefix 1 (sourceGridInterpretation r Δ ρ (.app (sub σ f) (sub σ a))) _
    rw [sourceGridInterpretation_decode r Δ ρ _ (Or.inr ⟨_, _, rfl⟩),
      sourceGridInterpretation_decode r Γ δ (.app f a) (Or.inr ⟨f, a, rfl⟩),
      typeSort_eq hs', typeSort_eq hs]
    exact sourceTypeEqPrefix_decode (r + 1) 1 (some s) _ _ hv
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    have hA' := hA.substitute hw hσ
    refine ⟨?_, ?_⟩
    · change FiniteGridValue.Agree 1 (sourceGridEval r Δ ρ (.lam (sub σ A) (sub (upSub σ) b))) _
      rw [sourceGridEval_lam_normalize, sourceGridEval_lam_normalize]
      apply FiniteGridType.normalizeValue_prefix_congr _ _ 1 (by omega)
        (sourceGridInferred_sub_first h hw hσ hk ρ δ)
      unfold sourceGridNativeLambda
      apply finiteTypeLambda_prefix_congr r 1 (by omega)
      · exact sourceGridCode_first_of_arity r _ _ _ _ _ _ (arityAt_sub hk A)
      · intro x hx
        exact sourceGridInferred_sub_first hb (.cons hw hA') (hσ.up hw hA')
          (upSub_not_kindAt hk) (push x ρ) (push x δ)
      · intro x hx
        exact (ihb hb (.cons hw hA') (hσ.up hw hA') (upSub_not_kindAt hk) (he.up hw hσ hA x hx)).1
    · intro q hsort
      obtain ⟨_, _, _, _, _, hh⟩ := hsort.generation
      exact (not_conv_pi_srt hh).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hs
    have ht' : BoundedTyping (r + 2) Δ (.pi (sub σ A) (sub (upSub σ) B)) (.srt s) := ht.substitute hw hσ
    have hA' := hA.substitute hw hσ
    have hDA := (ihA hA hw hσ hk he).2 sA hA
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).Valid x) :
        SourceTypeEqPrefix 1 (sourceGridInterpretation r (sub σ A :: Δ) (push x ρ) (sub (upSub σ) B))
          (sourceGridInterpretation r (A :: Γ) (push x δ) B) :=
      (ihB hB (.cons hw hA') (hσ.up hw hA') (upSub_not_kindAt hk) (he.up hw hσ hA x hx)).2 sB hB
    have hTy : SourceTypeEqPrefix 1 (sourceGridInterpretation r Δ ρ (sub σ (.pi A B)))
        (sourceGridInterpretation r Γ δ (.pi A B)) := by
      change SourceTypeEqPrefix 1 (sourceGridInterpretation r Δ ρ (.pi (sub σ A) (sub (upSub σ) B))) _
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r 1 _ _ _ _ hDA hDB
    refine ⟨?_, fun _ _ => hTy⟩
    change FiniteGridValue.Agree 1 (sourceGridEval r Δ ρ (.pi (sub σ A) (sub (upSub σ) B))) _
    rw [sourceGridEval_encode_normalize r Δ ρ _ (Or.inr ⟨_, _, rfl⟩),
      sourceGridEval_encode_normalize r Γ δ (.pi A B) (Or.inr ⟨A, B, rfl⟩)]
    apply FiniteGridType.normalizeValue_prefix_congr _ _ 1 (by omega)
      (sourceGridInferred_sub_first h hw hσ hk ρ δ)
    rw [typeSort_eq ht', typeSort_eq ht]
    exact uniformUniverseEncode_prefix_conversion (r + 1) 1 (by omega) s _ _ hTy
      (sourceGridInterpretation_formed ht' ρ)

end Submission.Helpers
