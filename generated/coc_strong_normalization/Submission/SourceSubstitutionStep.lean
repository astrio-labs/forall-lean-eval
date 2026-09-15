import Submission.SourceSubstitutionFrontier

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- The substitution successor consumes only earlier carrier comparisons,
plus renaming already proved at this stage. It produces the next value and
type prefixes, including the candidate boundary. -/
theorem sourceGrid_substitute_stage (F : SourceSubstitutionFrontier r d) {Γ Δ : List Tm} {t T : Tm} {σ : Nat → Tm}
    {ρ δ : GridEnvironment (r + 1)} (h : BoundedTyping (r + 2) Γ t T)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    (hδ : F.admissible Γ δ) (hρ : F.admissible Δ ρ)
    (he : GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ) :
    FiniteGridValue.Agree d (sourceGridEval r Δ ρ (sub σ t)) (sourceGridEval r Γ δ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix d (sourceGridInterpretation r Δ ρ (sub σ t)) (sourceGridInterpretation r Γ δ t)) := by
  induction t generalizing Γ T Δ σ ρ δ with
  | var j =>
    obtain ⟨C, hjC, hc⟩ := h.generation
    have hv := he.variable F h hw hσ hk hδ hρ hjC
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' : BoundedTyping (r + 2) Δ (σ j) (.srt s) := hs.substitute hw hσ
    have hT := sourceGridInterpretation_decode_prefix F.conversion hs' (by have hh := hs.var_below_top; omega) hρ
    have hM := sourceTypeEqPrefix_decode (r + 1) d (some s) _ _ hv
    have hS : SourceTypeEqPrefix d (sourceGridInterpretation r Γ δ (.var j))
        (uniformUniverseDecode (r + 1) (some s) (sourceGridEval r Γ δ (.var j))) := by
      apply SourceTypeEqPrefix.of_eq
      rw [sourceGridInterpretation_decode r Γ δ (.var j) (Or.inl ⟨j, rfl⟩), typeSort_eq hs]
    exact (hT.trans hM).trans hS.symm
  | srt q =>
    obtain ⟨s, hAx, hq, hs, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.srt q) (.srt s) := .srt h.wf hAx hq hs
    have ht' : BoundedTyping (r + 2) Δ (.srt q) (.srt s) := ht.substitute hw hσ
    have hTy : SourceTypeEqPrefix d (sourceGridInterpretation r Δ ρ (.srt q))
        (sourceGridInterpretation r Γ δ (.srt q)) := by
      rw [sourceGridInterpretation_sort, sourceGridInterpretation_sort]
      exact SourceTypeEqPrefix.of_eq d rfl
    refine ⟨?_, fun _ _ => hTy⟩
    change FiniteGridValue.Agree d (sourceGridEval r Δ ρ (.srt q)) _
    rw [sourceGridEval_encode_normalize r Δ ρ (.srt q) (Or.inl ⟨q, rfl⟩),
      sourceGridEval_encode_normalize r Γ δ (.srt q) (Or.inl ⟨q, rfl⟩)]
    apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.conversion.depth
      (F.inferred h hw hσ hk hδ hρ he)
    rw [typeSort_eq ht', typeSort_eq ht]
    exact uniformUniverseEncode_prefix_conversion (r + 1) d F.conversion.depth s _ _ hTy
      (sourceGridInterpretation_formed ht' ρ)
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv : FiniteGridValue.Agree d (sourceGridEval r Δ ρ (.app (sub σ f) (sub σ a)))
        (sourceGridEval r Γ δ (.app f a)) := by
      rw [sourceGridEval_app_normalize, sourceGridEval_app_normalize]
      apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.conversion.depth
        (F.inferred h hw hσ hk hδ hρ he)
      unfold sourceGridNativeApp
      apply finiteTypeApplication_prefix_congr r d F.conversion.depth
      · exact F.domain hf hw hσ hk hδ hρ he
      · exact F.codomain hf hw hσ hk hδ hρ he
      · exact (ihf hf hw hσ hk hδ hρ he).1
      · exact (iha ha hw hσ hk hδ hρ he).1
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' : BoundedTyping (r + 2) Δ (.app (sub σ f) (sub σ a)) (.srt s) := hs.substitute hw hσ
    change SourceTypeEqPrefix d (sourceGridInterpretation r Δ ρ (.app (sub σ f) (sub σ a))) _
    rw [sourceGridInterpretation_decode r Δ ρ _ (Or.inr ⟨_, _, rfl⟩),
      sourceGridInterpretation_decode r Γ δ (.app f a) (Or.inr ⟨f, a, rfl⟩),
      typeSort_eq hs', typeSort_eq hs]
    exact sourceTypeEqPrefix_decode (r + 1) d (some s) _ _ hv
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    have hA' := hA.substitute hw hσ
    have hup (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).Valid x) :
        F.admissible (A :: Γ) (push x δ) ∧
          F.admissible (sub σ A :: Δ) (push x ρ) := by
      have hx' := (F.types hA hw hσ hk hδ hρ he).coherent_forward d F.conversion.depth (Nat.le_refl _)
        _ (hx.mono (hd := Nat.le_refl (r + 2)) F.conversion.depth)
      exact ⟨F.extend hA hδ hx', F.extend hA' hρ (hx.mono (hd := Nat.le_refl (r + 2)) F.conversion.depth)⟩
    refine ⟨?_, ?_⟩
    · change FiniteGridValue.Agree d (sourceGridEval r Δ ρ (.lam (sub σ A) (sub (upSub σ) b))) _
      rw [sourceGridEval_lam_normalize, sourceGridEval_lam_normalize]
      apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.conversion.depth
        (F.inferred h hw hσ hk hδ hρ he)
      unfold sourceGridNativeLambda
      apply finiteTypeLambda_prefix_congr r d F.conversion.depth
      · exact F.types hA hw hσ hk hδ hρ he
      · intro x hx
        exact F.inferred hb (.cons hw hA') (hσ.up hw hA')
          (upSub_not_kindAt hk) (hup x hx).1 (hup x hx).2 (he.up F hw hσ hA hρ x hx)
      · intro x hx
        exact (ihb hb (.cons hw hA') (hσ.up hw hA') (upSub_not_kindAt hk) (hup x hx).1 (hup x hx).2 (he.up F hw hσ hA hρ x hx)).1
    · intro q hsort
      obtain ⟨_, _, _, _, _, hh⟩ := hsort.generation
      exact (not_conv_pi_srt hh).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hs
    have ht' : BoundedTyping (r + 2) Δ (.pi (sub σ A) (sub (upSub σ) B)) (.srt s) := ht.substitute hw hσ
    have hA' := hA.substitute hw hσ
    have hup (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).Valid x) :
        F.admissible (A :: Γ) (push x δ) ∧
          F.admissible (sub σ A :: Δ) (push x ρ) := by
      have hx' := (F.types hA hw hσ hk hδ hρ he).coherent_forward d F.conversion.depth (Nat.le_refl _)
        _ (hx.mono (hd := Nat.le_refl (r + 2)) F.conversion.depth)
      exact ⟨F.extend hA hδ hx', F.extend hA' hρ (hx.mono (hd := Nat.le_refl (r + 2)) F.conversion.depth)⟩
    have hDA := (ihA hA hw hσ hk hδ hρ he).2 sA hA
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).Valid x) :
        SourceTypeEqPrefix d (sourceGridInterpretation r (sub σ A :: Δ) (push x ρ) (sub (upSub σ) B))
          (sourceGridInterpretation r (A :: Γ) (push x δ) B) :=
      (ihB hB (.cons hw hA') (hσ.up hw hA') (upSub_not_kindAt hk) (hup x hx).1 (hup x hx).2 (he.up F hw hσ hA hρ x hx)).2 sB hB
    have hTy : SourceTypeEqPrefix d (sourceGridInterpretation r Δ ρ (sub σ (.pi A B)))
        (sourceGridInterpretation r Γ δ (.pi A B)) := by
      change SourceTypeEqPrefix d (sourceGridInterpretation r Δ ρ (.pi (sub σ A) (sub (upSub σ) B))) _
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r d _ _ _ _ hDA hDB
    refine ⟨?_, fun _ _ => hTy⟩
    change FiniteGridValue.Agree d (sourceGridEval r Δ ρ (.pi (sub σ A) (sub (upSub σ) B))) _
    rw [sourceGridEval_encode_normalize r Δ ρ _ (Or.inr ⟨_, _, rfl⟩),
      sourceGridEval_encode_normalize r Γ δ (.pi A B) (Or.inr ⟨A, B, rfl⟩)]
    apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.conversion.depth
      (F.inferred h hw hσ hk hδ hρ he)
    rw [typeSort_eq ht', typeSort_eq ht]
    exact uniformUniverseEncode_prefix_conversion (r + 1) d F.conversion.depth s _ _ hTy
      (sourceGridInterpretation_formed ht' ρ)

end Submission.Helpers
