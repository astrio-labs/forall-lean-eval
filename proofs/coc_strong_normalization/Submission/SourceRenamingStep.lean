import Submission.SourceTransportTypes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- A source renaming stage consumes only comparisons of the previously
available carriers. Structural recursion proves the new value prefix and
the next type carrier, including candidates at the final stage. -/
theorem sourceGrid_rename_stage (F : SourceRenamingFrontier r d)
    {Γ Δ : List Tm} {t T : Tm} {ι : Nat → Nat} {ρ δ : GridEnvironment (r + 1)}
    (h : BoundedTyping (r + 2) Γ t T) (hw : BoundedWf (r + 2) Δ) (hr : RenCtx Γ Δ ι)
    (hρ : F.admissible Γ ρ) (hδ : F.admissible Δ δ) (he : GridEnvironment.RenamedBelow d Γ ι ρ δ) :
    FiniteGridValue.Agree d (sourceGridEval r Δ δ (ren ι t)) (sourceGridEval r Γ ρ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (ren ι t)) (sourceGridInterpretation r Γ ρ t)) := by
  induction t generalizing Γ T Δ ι ρ δ with
  | var j =>
    obtain ⟨C, hjC, hc⟩ := h.generation
    have hv : FiniteGridValue.Agree d (sourceGridEval r Δ δ (.var (ι j))) (sourceGridEval r Γ ρ (.var j)) := by
      rw [sourceGridEval_var_normalize, sourceGridEval_var_normalize]
      exact FiniteGridType.normalizeValue_prefix_congr _ _ d F.depth
        (F.inferred h hw hr hρ hδ he) _ _ (he j C hjC)
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' : BoundedTyping (r + 2) Δ (.var (ι j)) (.srt s) := hs.rename hw hr
    change SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (.var (ι j))) _
    rw [sourceGridInterpretation_decode r Δ δ (.var (ι j)) (Or.inl ⟨ι j, rfl⟩),
      sourceGridInterpretation_decode r Γ ρ (.var j) (Or.inl ⟨j, rfl⟩),
      typeSort_eq hs', typeSort_eq hs]
    exact sourceTypeEqPrefix_decode (r + 1) d (some s) _ _ hv
  | srt q =>
    obtain ⟨s, hAx, hq, hs, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.srt q) (.srt s) := .srt h.wf hAx hq hs
    have ht' := ht.rename hw hr
    simp only [ren] at ht'
    have hTy : SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (.srt q))
        (sourceGridInterpretation r Γ ρ (.srt q)) := by
      rw [sourceGridInterpretation_sort, sourceGridInterpretation_sort]
      exact SourceTypeEqPrefix.of_eq d rfl
    refine ⟨?_, fun _ _ => hTy⟩
    change FiniteGridValue.Agree d (sourceGridEval r Δ δ (.srt q)) _
    rw [sourceGridEval_encode_normalize r Δ δ (.srt q) (Or.inl ⟨q, rfl⟩),
      sourceGridEval_encode_normalize r Γ ρ (.srt q) (Or.inl ⟨q, rfl⟩)]
    apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.depth (F.inferred h hw hr hρ hδ he)
    rw [typeSort_eq ht', typeSort_eq ht]
    exact uniformUniverseEncode_prefix_conversion (r + 1) d F.depth s _ _ hTy
      (sourceGridInterpretation_formed ht' δ)
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha, hc⟩ := h.generation
    have hv : FiniteGridValue.Agree d (sourceGridEval r Δ δ (.app (ren ι f) (ren ι a)))
        (sourceGridEval r Γ ρ (.app f a)) := by
      rw [sourceGridEval_app_normalize, sourceGridEval_app_normalize]
      apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.depth (F.inferred h hw hr hρ hδ he)
      unfold sourceGridNativeApp
      apply finiteTypeApplication_prefix_congr r d F.depth
      · exact F.domain hf hw hr hρ hδ he
      · exact F.codomain hf hw hr hρ hδ he
      · exact (ihf hf hw hr hρ hδ he).1
      · exact (iha ha hw hr hρ hδ he).1
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' : BoundedTyping (r + 2) Δ (.app (ren ι f) (ren ι a)) (.srt s) := hs.rename hw hr
    change SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (.app (ren ι f) (ren ι a))) _
    rw [sourceGridInterpretation_decode r Δ δ (.app (ren ι f) (ren ι a)) (Or.inr ⟨_, _, rfl⟩),
      sourceGridInterpretation_decode r Γ ρ (.app f a) (Or.inr ⟨f, a, rfl⟩),
      typeSort_eq hs', typeSort_eq hs]
    exact sourceTypeEqPrefix_decode (r + 1) d (some s) _ _ hv
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    have hA' := hA.rename hw hr
    have hup (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ δ (ren ι A)).Valid x) :
        F.admissible (A :: Γ) (push x ρ) ∧ F.admissible (ren ι A :: Δ) (push x δ) := by
      have hx' := (F.types hA hw hr hρ hδ he).coherent_forward d F.depth (Nat.le_refl _)
        _ (hx.mono (hd := Nat.le_refl (r + 2)) F.depth)
      exact ⟨F.extend hA hρ hx', F.extend hA' hδ (hx.mono (hd := Nat.le_refl (r + 2)) F.depth)⟩
    refine ⟨?_, ?_⟩
    · change FiniteGridValue.Agree d (sourceGridEval r Δ δ (.lam (ren ι A) (ren (upRen ι) b))) _
      rw [sourceGridEval_lam_normalize, sourceGridEval_lam_normalize]
      apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.depth (F.inferred h hw hr hρ hδ he)
      unfold sourceGridNativeLambda
      apply finiteTypeLambda_prefix_congr r d F.depth
      · exact F.types hA hw hr hρ hδ he
      · intro x hx
        exact F.inferred hb (.cons hw hA') (hr.up A) (hup x hx).1 (hup x hx).2 (he.up A x)
      · intro x hx
        exact (ihb hb (.cons hw hA') (hr.up A) (hup x hx).1 (hup x hx).2 (he.up A x)).1
    · intro q hsort
      obtain ⟨_, _, _, _, _, hh⟩ := hsort.generation
      exact (not_conv_pi_srt hh).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hRule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping (r + 2) Γ (.pi A B) (.srt s) := .pi hA hB hRule hsA hsB hs
    have ht' := ht.rename hw hr
    simp only [ren] at ht'
    have hA' := hA.rename hw hr
    have hDA := (ihA hA hw hr hρ hδ he).2 sA hA
    have hup (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ δ (ren ι A)).Valid x) :
        F.admissible (A :: Γ) (push x ρ) ∧ F.admissible (ren ι A :: Δ) (push x δ) := by
      have hx' := hDA.code.coherent_forward d F.depth (by omega) _ (hx.mono (hd := Nat.le_refl (r + 2)) F.depth)
      exact ⟨F.extend hA hρ hx', F.extend hA' hδ (hx.mono (hd := Nat.le_refl (r + 2)) F.depth)⟩
    have hDB (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ δ (ren ι A)).Valid x) :
        SourceTypeEqPrefix d (sourceGridInterpretation r (ren ι A :: Δ) (push x δ) (ren (upRen ι) B))
          (sourceGridInterpretation r (A :: Γ) (push x ρ) B) :=
      (ihB hB (.cons hw hA') (hr.up A) (hup x hx).1 (hup x hx).2 (he.up A x)).2 sB hB
    have hTy : SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (ren ι (.pi A B)))
        (sourceGridInterpretation r Γ ρ (.pi A B)) := by
      change SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (.pi (ren ι A) (ren (upRen ι) B))) _
      rw [sourceGridInterpretation_pi, sourceGridInterpretation_pi]
      exact sourceTypeEqPrefix_pi r d _ _ _ _ hDA hDB
    refine ⟨?_, fun _ _ => hTy⟩
    change FiniteGridValue.Agree d (sourceGridEval r Δ δ (.pi (ren ι A) (ren (upRen ι) B))) _
    rw [sourceGridEval_encode_normalize r Δ δ _ (Or.inr ⟨_, _, rfl⟩),
      sourceGridEval_encode_normalize r Γ ρ (.pi A B) (Or.inr ⟨A, B, rfl⟩)]
    apply FiniteGridType.normalizeValue_prefix_congr _ _ d F.depth (F.inferred h hw hr hρ hδ he)
    rw [typeSort_eq ht', typeSort_eq ht]
    exact uniformUniverseEncode_prefix_conversion (r + 1) d F.depth s _ _ hTy
      (sourceGridInterpretation_formed ht' δ)

end Submission.Helpers
