import Submission.FiberTransport

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem fiberSemantics_var (hδ : FiberContext 2 0 Γ ρ δ)
    (hw : BoundedWf 2 Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type 0) Γ ρ) :
    (fiberSemantics Γ ρ δ (.var j)).1 = δ j :=
  FiberValue.force_eq _ (hδ.var_code hw hj rfl hρ)

theorem kindAt_upSub_false (hk : ∀ j, kindAt q (σ j) = false) :
    ∀ j, kindAt q (upSub σ j) = false := by
  intro j
  cases j with
  | zero => rfl
  | succ j => exact (kindAt_ren _ _ _).trans (hk j)

theorem shapeEval_substitute_related (h : BoundedTyping 2 Γ t T)
    (hw : BoundedWf 2 Δ) (hσ : BoundedSubCtx 2 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 0) (σ j) = false)
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 2 0 Δ ρ' (σ j) = ρ j) :
    shapeEval 2 0 Δ ρ' (sub σ t) = shapeEval 2 0 Γ ρ t :=
  (shapeEval_substitute h hw hσ hk rfl).trans (shapeEval_env h heρ)

theorem fiberShape_substitute_related (h : BoundedTyping 2 Γ A (.srt s))
    (hw : BoundedWf 2 Δ) (hσ : BoundedSubCtx 2 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 0) (σ j) = false)
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 2 0 Δ ρ' (σ j) = ρ j) :
    fiberShape 2 0 Δ ρ' (sub σ A) v = fiberShape 2 0 Γ ρ A v :=
  (fiberShape_substitute h hw hσ hk rfl).trans (fiberShape_env h rfl heρ)

theorem shapeSubstitute_related_up (hA : BoundedTyping 2 Γ A (.srt s))
    (hw : BoundedWf 2 Δ) (hσ : BoundedSubCtx 2 Γ Δ σ)
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 2 0 Δ ρ' (σ j) = ρ j) :
    ∀ j C, (A :: Γ)[j]? = some C →
      shapeEval 2 0 (sub σ A :: Δ) (push x ρ') (upSub σ j) = push x ρ j := by
  intro j C hj
  cases j with
  | zero => rfl
  | succ j =>
    exact (shapeEval_ren (hσ j C hj) (.cons hw (hA.substitute hw hσ))
      (.weaken Δ (sub σ A)) rfl (fun _ => rfl)).trans (heρ j C hj)

theorem fiberSubstitute_related_up (hA : BoundedTyping 2 Γ A (.srt s))
    (hw : BoundedWf 2 Δ) (hσ : BoundedSubCtx 2 Γ Δ σ)
    (hρ' : ShapeContext (.type 0) Δ ρ') (hδ' : FiberContext 2 0 Δ ρ' δ')
    (heδ : ∀ j C, Γ[j]? = some C → (fiberSemantics Δ ρ' δ' (σ j)).1 = δ j)
    (hx : x.code = arityAt (.type 0) (sub σ A))
    (hy : y.code = fiberShape 2 0 Δ ρ' (sub σ A) x) :
    ∀ j C, (A :: Γ)[j]? = some C →
      (fiberSemantics (sub σ A :: Δ) (push x ρ') (push y δ') (upSub σ j)).1 =
        push y δ j := by
  have hA' := hA.substitute hw hσ
  intro j C hj
  cases j with
  | zero =>
    exact fiberSemantics_var (hδ'.up hA' rfl hy) (.cons hw hA') rfl (hρ'.up hx)
  | succ j =>
    exact ((fiberSemantics_ren (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A))
      hρ' (hρ'.up hx) (fun _ => rfl) (fun _ => rfl)).1).trans (heδ j C hj)

/-- Simultaneous substitution preserves typed values and, separately, all formed-type
candidate families. The second clause includes the top sort; it does not assert pair
equality for arbitrary terms whose sort classification can change. -/
theorem fiberSemantics_substitute_related (h : BoundedTyping 2 Γ t T)
    (hw : BoundedWf 2 Δ) (hσ : BoundedSubCtx 2 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 0) (σ j) = false)
    (hρ : ShapeContext (.type 0) Γ ρ) (hρ' : ShapeContext (.type 0) Δ ρ')
    (hδ : FiberContext 2 0 Γ ρ δ) (hδ' : FiberContext 2 0 Δ ρ' δ')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 2 0 Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (fiberSemantics Δ ρ' δ' (σ j)).1 = δ j) :
    (fiberSemantics Δ ρ' δ' (sub σ t)).1 = (fiberSemantics Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping 2 Γ t (.srt s) →
      (fiberSemantics Δ ρ' δ' (sub σ t)).2 = (fiberSemantics Γ ρ δ t).2) := by
  induction t generalizing Γ T Δ σ ρ ρ' δ δ' with
  | var j =>
    obtain ⟨A, hj, hc⟩ := h.generation
    have hv : (fiberSemantics Δ ρ' δ' (sub σ (.var j))).1 =
        (fiberSemantics Γ ρ δ (.var j)).1 := by
      rw [fiberSemantics_var hδ h.wf hj hρ]
      exact heδ j A hj
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f
    rw [fiberSemantics_decode (hs.substitute hw hσ) hs.var_below_top hρ',
      fiberSemantics_decode hs hs.var_below_top hρ, hv]
    exact congrArg (fun k => fiberDecode (some s) k
      (fiberSemantics Γ ρ δ (.var j)).1 u f)
      (congrArg ShapeValue.asArity (shapeEval_substitute_related hs hw hσ hk heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping 2 Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    refine ⟨?_, fun _ _ => rfl⟩
    change (fiberSemantics Δ ρ' δ' (.srt s)).1 = _
    rw [fiberSemantics_sort_value (ht.substitute hw hσ) hρ',
      fiberSemantics_sort_value ht hρ]
    exact congrArg (fun k => fiberEncode (some s') k (fun _ _ => Candidate.sn))
      (congrArg ShapeValue.asArity (shapeEval_substitute_related ht hw hσ hk heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    have hv : (fiberSemantics Δ ρ' δ' (sub σ (.app g a))).1 =
        (fiberSemantics Γ ρ δ (.app g a)).1 := by
      change (fiberSemantics Δ ρ' δ' (.app (sub σ g) (sub σ a))).1 = _
      rw [fiberSemantics_app (hg.substitute hw hσ) (ha.substitute hw hσ) hρ',
        fiberSemantics_app hg ha hρ,
        shapeEval_substitute_related hg hw hσ hk heρ,
        shapeEval_substitute_related ha hw hσ hk heρ,
        (ihg hg hw hσ hk hρ hρ' hδ hδ' heρ heδ).1,
        (iha ha hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
      apply fiberApply_congr (arityAt_sub hk A)
      · intro x hx
        exact fiberShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact fiberShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (shapeSubstitute_related_up hA hw hσ heρ)
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f
    rw [fiberSemantics_decode (hs.substitute hw hσ) hs.app_below_top hρ',
      fiberSemantics_decode hs hs.app_below_top hρ, hv]
    exact congrArg (fun k => fiberDecode (some s) k
      (fiberSemantics Γ ρ δ (.app g a)).1 u f)
      (congrArg ShapeValue.asArity (shapeEval_substitute_related hs hw hσ hk heρ))
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    refine ⟨?_, ?_⟩
    · change (fiberSemantics Δ ρ' δ' (.lam (sub σ A) (sub (upSub σ) b))).1 = _
      rw [fiberSemantics_lam (hPi.substitute hw hσ)
          (hb.substitute (.cons hw hA') (hσ.up hw hA')) hρ',
        fiberSemantics_lam hPi hb hρ,
        ← show sub σ (.lam A b) = .lam (sub σ A) (sub (upSub σ) b) from rfl,
        shapeEval_substitute_related (.lam hPi hb hs) hw hσ hk heρ]
      apply fiberLambda_congr (arityAt_sub hk A)
      · intro x hx
        exact fiberShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact fiberShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (shapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact (ihb hb (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (fiberShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy) (shapeSubstitute_related_up hA hw hσ heρ)
          (fiberSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)).1
    · intro r hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hrule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping 2 Γ (.pi A B) (.srt s) :=
      .pi hA hB hrule hsA hsB hs
    have hA' := hA.substitute hw hσ
    have he : fiberSemantics Δ ρ' δ' (sub σ (.pi A B)) =
        fiberSemantics Γ ρ δ (.pi A B) := by
      apply fiberSemantics_pi_compare (ht.substitute hw hσ) ht hρ' hρ
        (arityAt_sub hk A) (arityAt_sub hk (.pi A B))
        (congrArg ShapeValue.asArity (shapeEval_substitute_related ht hw hσ hk heρ))
      · intro x hx
        exact fiberShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact fiberShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (shapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun
          ((ihA hA hw hσ hk hρ hρ' hδ hδ' heρ heδ).2 sA hA) x) y
      · intro x hx y hy
        exact (ihB hB (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (fiberShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy) (shapeSubstitute_related_up hA hw hσ heρ)
          (fiberSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

/-- Single substitution preserves the fiber value of every typed term. -/
theorem fiberSemantics_subst_value (hb : BoundedTyping 2 (A :: Γ) b B)
    (ha : BoundedTyping 2 Γ a A) (hA : BoundedTyping 2 Γ A (.srt sA))
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ) :
    (fiberSemantics Γ ρ δ (subst 0 a b)).1 =
      (fiberSemantics (A :: Γ) (push (shapeEval 2 0 Γ ρ a) ρ)
        (push (fiberSemantics Γ ρ δ a).1 δ) b).1 := by
  rw [subst_eq_sub]
  apply (fiberSemantics_substitute_related hb ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA rfl (fiberSemantics_typed_code ha hρ)) hδ ?_ ?_).1
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj
    cases j <;> rfl
  · intro j C hj
    cases j with
    | zero => rfl
    | succ j => exact fiberSemantics_var hδ ha.wf hj hρ

/-- Candidate substitution at bound two, including formed types in `Type 1`. -/
theorem fiberSemantics_subst_candidate (hB : BoundedTyping 2 (A :: Γ) B (.srt sB))
    (ha : BoundedTyping 2 Γ a A) (hA : BoundedTyping 2 Γ A (.srt sA))
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ) :
    (fiberSemantics Γ ρ δ (subst 0 a B)).2 =
      (fiberSemantics (A :: Γ) (push (shapeEval 2 0 Γ ρ a) ρ)
        (push (fiberSemantics Γ ρ δ a).1 δ) B).2 := by
  rw [subst_eq_sub]
  apply (fiberSemantics_substitute_related hB ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA rfl (fiberSemantics_typed_code ha hρ)) hδ ?_ ?_).2 sB hB
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj
    cases j <;> rfl
  · intro j C hj
    cases j with
    | zero => rfl
    | succ j => exact fiberSemantics_var hδ ha.wf hj hρ

end Submission.Helpers
