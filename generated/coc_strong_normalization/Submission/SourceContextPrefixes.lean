import Submission.SourceSubstitutionSecond

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

/-- A context is compatible through d when evaluation of its declared
variables recovers the supplied entries through d. -/
structure SourceGridCompatible (r d : Nat) (Γ : List Tm) (ρ : GridEnvironment (r + 1)) : Prop where
  first : SourceGridContextFirst r Γ ρ
  lookup : ∀ j A, Γ[j]? = some A →
    FiniteGridValue.Agree d (sourceGridEval r Γ ρ (.var j)) (ρ j)

theorem SourceGridCompatible.mono (h : SourceGridCompatible r d Γ ρ) (he : e ≤ d) :
    SourceGridCompatible r e Γ ρ := ⟨h.first, fun j A hj => (h.lookup j A hj).mono he⟩

theorem sourceGridCompatible_exists (d : Nat) (hw : BoundedWf (r + 2) Γ) :
    ∃ ρ, SourceGridCompatible r d Γ ρ := by
  obtain ⟨ρ, hρ⟩ := sourceGrid_admissible_exists r Γ
  refine ⟨ρ, ⟨?_, ?_⟩⟩
  · intro j A hj
    have hv := sourceGridEval_arity (.var hw hj) ρ
    rw [sourceGridEval_variable r Γ ρ hρ j] at hv
    simpa only [← ren_shift, arityAt_ren] using hv
  · intro j A hj i hi
    exact congrFun (sourceGridEval_variable r Γ ρ hρ j) i

theorem sourceGridEval_head_prefix (F : SourceSubstitutionFrontier r d)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hρ : F.admissible Γ ρ)
    (hx : (sourceGridInterpretation r Γ ρ A).carrier.Coherent d F.conversion.depth
      (FiniteGridValue.toTower _ x)) :
    FiniteGridValue.Agree d (sourceGridEval r (A :: Γ) (push x ρ) (.var 0)) x := by
  have hctx := F.extend hA hρ hx
  have hv : BoundedTyping (r + 2) (A :: Γ) (.var 0) (lift 1 0 A) := .var (.cons hA.wf hA) rfl
  have hChosen := chosenType_typing hv
  have hEq := F.conversion.convert hChosen.type_expression hv.type_expression hctx
    (typing_unique hChosen.forget hv.forget)
  have hrel : GridEnvironment.RenamedBelow d Γ Nat.succ ρ (push x ρ) := by
    intro j C hj i hi
    rfl
  have hRen := (F.rename_stage hA (.cons hA.wf hA) (.weaken Γ A) hρ hctx hrel).2 s hA
  have hCode : FiniteGridCodeEqBelow d
      (sourceGridInterpretation r (A :: Γ) (push x ρ) (chosenType (r + 2) (A :: Γ) (.var 0)))
      (sourceGridInterpretation r Γ ρ A) := by
    rw [← ren_shift] at hEq
    exact hEq.trans (hRen.code.mono (Nat.le_succ _))
  rw [sourceGridEval_var_normalize]
  exact FiniteGridType.normalizeValue_recover_prefix _ d F.conversion.depth _
    (hCode.coherent_backward d F.conversion.depth (Nat.le_refl _) _ hx)

/-- Extension needs only a coherent argument prefix; later coordinates of
the supplied argument are unrestricted. -/
theorem SourceGridCompatible.up (F : SourceSubstitutionFrontier r d) (hd : 1 ≤ d)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hρ : SourceGridCompatible r d Γ ρ)
    (hP : F.admissible Γ ρ)
    (hx : (sourceGridInterpretation r Γ ρ A).carrier.Coherent d F.conversion.depth
      (FiniteGridValue.toTower _ x)) : SourceGridCompatible r d (A :: Γ) (push x ρ) := by
  have hctx := F.extend hA hP hx
  refine ⟨?_, ?_⟩
  · apply hρ.first.up
    have hc := hx 0 (by omega)
    rw [FiniteGridValue.toTower_at _ _ ⟨0, by omega⟩, sourceGridInterpretation_zero] at hc
    exact hc
  · intro j C hj
    cases j with
    | zero => exact sourceGridEval_head_prefix F hA hP hx
    | succ j =>
      have he := (F.rename_stage (.var hA.wf hj) (.cons hA.wf hA) (.weaken Γ A) hP hctx
        (by intro i D hi k hk; rfl)).1
      exact fun i hi => (he i hi).trans (hρ.lookup j C hj i hi)

theorem SourceGridCompatible.up_second (hA : BoundedTyping (r + 2) Γ A (.srt s))
    (hρ : SourceGridCompatible r 2 Γ ρ)
    (hx : (sourceGridInterpretation r Γ ρ A).carrier.Coherent 2 (by omega)
      (FiniteGridValue.toTower _ x)) : SourceGridCompatible r 2 (A :: Γ) (push x ρ) :=
  hρ.up (sourceSubstitutionSecond r) (by omega) hA hρ.first hx

/-- Actual typed single substitution at the second stage. The variable
compatibility is an explicit, inhabited context invariant. -/
theorem sourceGrid_subst_second (hb : BoundedTyping (r + 2) (A :: Γ) b B)
    (hA : BoundedTyping (r + 2) Γ A (.srt sA)) (ha : BoundedTyping (r + 2) Γ a A)
    (hρ : SourceGridCompatible r 2 Γ ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r Γ ρ (subst 0 a b))
      (sourceGridEval r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b) ∧
    (∀ s, BoundedTyping (r + 2) (A :: Γ) b (.srt s) →
      SourceTypeEqPrefix 2 (sourceGridInterpretation r Γ ρ (subst 0 a b))
        (sourceGridInterpretation r (A :: Γ) (push (sourceGridEval r Γ ρ a) ρ) b)) := by
  rw [subst_eq_sub]
  apply sourceGrid_substitute_second hb ha.wf (BoundedSubCtx.single ha)
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · exact hρ.first.up (sourceGridEval_arity ha ρ)
  · exact hρ.first
  · intro j C hj
    cases j with
    | zero => intro i hi; rfl
    | succ j => exact hρ.lookup j C hj

theorem SourceGridContextFirst.convert_head (hA : BoundedTyping (r + 2) Γ A (.srt s))
    (hA' : BoundedTyping (r + 2) Γ A' (.srt s')) (hc : Conv A A')
    (hρ : SourceGridContextFirst r (A' :: Γ) ρ) : SourceGridContextFirst r (A :: Γ) ρ := by
  intro j C hj
  cases j with
  | zero =>
    have he : A = C := Option.some.inj hj
    subst C
    exact (hρ 0 A' rfl).trans (arityAt_conv (hA.goodAt (q := .type r) rfl)
      (hA'.goodAt (q := .type r) rfl) hc).symm
  | succ j => exact hρ (j + 1) C hj

theorem sourceGrid_context_conversion_second (ht : BoundedTyping (r + 2) (A :: Γ) t T)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hA' : BoundedTyping (r + 2) Γ A' (.srt s'))
    (hc : Conv A A') (hρ : SourceGridCompatible r 2 (A' :: Γ) ρ) :
    FiniteGridValue.Agree 2 (sourceGridEval r (A' :: Γ) ρ t) (sourceGridEval r (A :: Γ) ρ t) ∧
    (∀ q, BoundedTyping (r + 2) (A :: Γ) t (.srt q) →
      SourceTypeEqPrefix 2 (sourceGridInterpretation r (A' :: Γ) ρ t) (sourceGridInterpretation r (A :: Γ) ρ t)) := by
  have he : GridEnvironment.SubstitutedBelow r 2 (A :: Γ) (A' :: Γ) Tm.var ρ ρ := by
    intro j C hj
    cases j with
    | zero => exact hρ.lookup 0 A' rfl
    | succ j => exact hρ.lookup (j + 1) C hj
  simpa only [sub_var] using sourceGrid_substitute_second ht (.cons hA'.wf hA')
    (BoundedSubCtx.convert_head hA hA' hc) (fun _ => rfl)
    (hρ.first.convert_head hA hA' hc) hρ.first he

theorem SourceGridCompatible.convert_head_second (hA : BoundedTyping (r + 2) Γ A (.srt s))
    (hA' : BoundedTyping (r + 2) Γ A' (.srt s')) (hc : Conv A A')
    (hρ : SourceGridCompatible r 2 (A' :: Γ) ρ) : SourceGridCompatible r 2 (A :: Γ) ρ := by
  refine ⟨hρ.first.convert_head hA hA' hc, ?_⟩
  intro j C hj
  have hv : BoundedTyping (r + 2) (A :: Γ) (.var j) (lift (j + 1) 0 C) :=
    .var (.cons hA.wf hA) hj
  have he := (sourceGrid_context_conversion_second hv hA hA' hc hρ).1
  have hTarget : FiniteGridValue.Agree 2 (sourceGridEval r (A' :: Γ) ρ (.var j)) (ρ j) := by
    cases j with
    | zero => exact hρ.lookup 0 A' rfl
    | succ j => exact hρ.lookup (j + 1) C hj
  exact fun i hi => (he i hi).symm.trans (hTarget i hi)

end Submission.Helpers
