import Submission.MiddleTransport
import Submission.FiberSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem middleSemantics_var (hδ : MiddleContext 3 1 Γ ρ δ)
    (hw : BoundedWf 3 Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type 1) Γ ρ) :
    (middleSemantics Γ ρ δ (.var j)).1 = δ j :=
  MiddleValue.force_eq _ (hδ.var_code hw hj rfl hρ)

theorem middleShapeEval_substitute_related (h : BoundedTyping 3 Γ t T)
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 1) (σ j) = false)
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 3 1 Δ ρ' (σ j) = ρ j) :
    shapeEval 3 1 Δ ρ' (sub σ t) = shapeEval 3 1 Γ ρ t :=
  (shapeEval_substitute h hw hσ hk rfl).trans (shapeEval_env h heρ)

theorem middleShape_substitute_related (h : BoundedTyping 3 Γ A (.srt s))
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 1) (σ j) = false)
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 3 1 Δ ρ' (σ j) = ρ j) :
    middleShape 3 1 Δ ρ' (sub σ A) v = middleShape 3 1 Γ ρ A v :=
  (middleShape_substitute h hw hσ hk rfl).trans (middleShape_env h rfl heρ)

theorem middleShapeSubstitute_related_up (hA : BoundedTyping 3 Γ A (.srt s))
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 3 1 Δ ρ' (σ j) = ρ j) :
    ∀ j C, (A :: Γ)[j]? = some C →
      shapeEval 3 1 (sub σ A :: Δ) (push x ρ') (upSub σ j) = push x ρ j := by
  intro j C hj
  cases j with
  | zero => rfl
  | succ j =>
    exact (shapeEval_ren (hσ j C hj) (.cons hw (hA.substitute hw hσ))
      (.weaken Δ (sub σ A)) rfl (fun _ => rfl)).trans (heρ j C hj)

theorem middleSubstitute_related_up (hA : BoundedTyping 3 Γ A (.srt s))
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hρ' : ShapeContext (.type 1) Δ ρ') (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (heδ : ∀ j C, Γ[j]? = some C → (middleSemantics Δ ρ' δ' (σ j)).1 = δ j)
    (hx : x.code = arityAt (.type 1) (sub σ A))
    (hy : y.code = middleShape 3 1 Δ ρ' (sub σ A) x) :
    ∀ j C, (A :: Γ)[j]? = some C →
      (middleSemantics (sub σ A :: Δ) (push x ρ') (push y δ') (upSub σ j)).1 =
        push y δ j := by
  have hA' := hA.substitute hw hσ
  intro j C hj
  cases j with
  | zero =>
    exact middleSemantics_var (hδ'.up hA' rfl hy) (.cons hw hA') rfl (hρ'.up hx)
  | succ j =>
    exact ((middleSemantics_ren (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A))
      hρ' (hρ'.up hx) (fun _ => rfl) (fun _ => rfl)).1).trans (heδ j C hj)

/-- Simultaneous substitution preserves typed values and, separately, all formed-type
carrier families. The second clause includes the top sort; it does not assert pair
equality for arbitrary terms whose sort classification can change. -/
theorem middleSemantics_substitute_related (h : BoundedTyping 3 Γ t T)
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 1) (σ j) = false)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 3 1 Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (middleSemantics Δ ρ' δ' (σ j)).1 = δ j) :
    (middleSemantics Δ ρ' δ' (sub σ t)).1 = (middleSemantics Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (middleSemantics Δ ρ' δ' (sub σ t)).2 = (middleSemantics Γ ρ δ t).2) := by
  induction t generalizing Γ T Δ σ ρ ρ' δ δ' with
  | var j =>
    obtain ⟨A, hj, hc⟩ := h.generation
    have hv : (middleSemantics Δ ρ' δ' (sub σ (.var j))).1 =
        (middleSemantics Γ ρ δ (.var j)).1 := by
      rw [middleSemantics_var hδ h.wf hj hρ]
      exact heδ j A hj
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f
    rw [middleSemantics_decode (hs.substitute hw hσ) hs.var_below_top hρ',
      middleSemantics_decode hs hs.var_below_top hρ, hv]
    exact congrArg (fun k => middleDecode (some s) k
      (middleSemantics Γ ρ δ (.var j)).1 u f)
      (congrArg ShapeValue.asArity (middleShapeEval_substitute_related hs hw hσ hk heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    refine ⟨?_, fun _ _ => rfl⟩
    change (middleSemantics Δ ρ' δ' (.srt s)).1 = _
    rw [middleSemantics_sort_value (ht.substitute hw hσ) hρ',
      middleSemantics_sort_value ht hρ]
    exact congrArg (fun k => middleEncode (some s') k (thirdSort s))
      (congrArg ShapeValue.asArity (middleShapeEval_substitute_related ht hw hσ hk heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    have hv : (middleSemantics Δ ρ' δ' (sub σ (.app g a))).1 =
        (middleSemantics Γ ρ δ (.app g a)).1 := by
      change (middleSemantics Δ ρ' δ' (.app (sub σ g) (sub σ a))).1 = _
      rw [middleSemantics_app (hg.substitute hw hσ) (ha.substitute hw hσ) hρ',
        middleSemantics_app hg ha hρ,
        middleShapeEval_substitute_related hg hw hσ hk heρ,
        middleShapeEval_substitute_related ha hw hσ hk heρ,
        (ihg hg hw hσ hk hρ hρ' hδ hδ' heρ heδ).1,
        (iha ha hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
      apply middleApply_congr (arityAt_sub hk A)
      · intro x hx
        exact middleShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact middleShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (middleShapeSubstitute_related_up hA hw hσ heρ)
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f
    rw [middleSemantics_decode (hs.substitute hw hσ) hs.app_below_top hρ',
      middleSemantics_decode hs hs.app_below_top hρ, hv]
    exact congrArg (fun k => middleDecode (some s) k
      (middleSemantics Γ ρ δ (.app g a)).1 u f)
      (congrArg ShapeValue.asArity (middleShapeEval_substitute_related hs hw hσ hk heρ))
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    refine ⟨?_, ?_⟩
    · change (middleSemantics Δ ρ' δ' (.lam (sub σ A) (sub (upSub σ) b))).1 = _
      rw [middleSemantics_lam (hPi.substitute hw hσ)
          (hb.substitute (.cons hw hA') (hσ.up hw hA')) hρ',
        middleSemantics_lam hPi hb hρ,
        ← show sub σ (.lam A b) = .lam (sub σ A) (sub (upSub σ) b) from rfl,
        middleShapeEval_substitute_related (.lam hPi hb hs) hw hσ hk heρ]
      apply middleLambda_congr (arityAt_sub hk A)
      · intro x hx
        exact middleShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact middleShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (middleShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact (ihb hb (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy) (middleShapeSubstitute_related_up hA hw hσ heρ)
          (middleSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)).1
    · intro r hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hrule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) :=
      .pi hA hB hrule hsA hsB hs
    have hA' := hA.substitute hw hσ
    have he : middleSemantics Δ ρ' δ' (sub σ (.pi A B)) =
        middleSemantics Γ ρ δ (.pi A B) := by
      apply middleSemantics_pi_compare (ht.substitute hw hσ) ht hρ' hρ
        (arityAt_sub hk A) (arityAt_sub hk (.pi A B))
        (congrArg ShapeValue.asArity (middleShapeEval_substitute_related ht hw hσ hk heρ))
      · intro x hx
        exact middleShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact middleShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (middleShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun
          ((ihA hA hw hσ hk hρ hρ' hδ hδ' heρ heδ).2 sA hA) x) y
      · intro x hx y hy
        exact (ihB hB (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy) (middleShapeSubstitute_related_up hA hw hσ heρ)
          (middleSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

/-- Single substitution preserves the fiber value of every typed term. -/
theorem middleSemantics_subst_value (hb : BoundedTyping 3 (A :: Γ) b B)
    (ha : BoundedTyping 3 Γ a A) (hA : BoundedTyping 3 Γ A (.srt sA))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (middleSemantics Γ ρ δ (subst 0 a b)).1 =
      (middleSemantics (A :: Γ) (push (shapeEval 3 1 Γ ρ a) ρ)
        (push (middleSemantics Γ ρ δ a).1 δ) b).1 := by
  rw [subst_eq_sub]
  apply (middleSemantics_substitute_related hb ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA rfl (middleSemantics_typed_code ha hρ)) hδ ?_ ?_).1
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj
    cases j <;> rfl
  · intro j C hj
    cases j with
    | zero => rfl
    | succ j => exact middleSemantics_var hδ ha.wf hj hρ

/-- Carrier substitution at bound three, including formed types in `Type 2`. -/
theorem middleSemantics_subst_carrier (hB : BoundedTyping 3 (A :: Γ) B (.srt sB))
    (ha : BoundedTyping 3 Γ a A) (hA : BoundedTyping 3 Γ A (.srt sA))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (middleSemantics Γ ρ δ (subst 0 a B)).2 =
      (middleSemantics (A :: Γ) (push (shapeEval 3 1 Γ ρ a) ρ)
        (push (middleSemantics Γ ρ δ a).1 δ) B).2 := by
  rw [subst_eq_sub]
  apply (middleSemantics_substitute_related hB ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA rfl (middleSemantics_typed_code ha hρ)) hδ ?_ ?_).2 sB hB
  · intro j
    cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj
    cases j <;> rfl
  · intro j C hj
    cases j with
    | zero => rfl
    | succ j => exact middleSemantics_var hδ ha.wf hj hρ

end Submission.Helpers
