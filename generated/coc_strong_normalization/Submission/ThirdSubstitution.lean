import Submission.ThirdTransport

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem thirdSemantics_var (hε : ThirdContext Γ ρ δ ε)
    (hw : BoundedWf 3 Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.var j)).1 = ε j :=
  ThirdValue.force_eq _ (hε.var_code hw hj hρ hδ)

theorem thirdSubstitute_related_up (hA : BoundedTyping 3 Γ A (.srt s))
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hρ' : ShapeContext (.type 1) Δ ρ') (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (hε' : ThirdContext Δ ρ' δ' ε')
    (heε : ∀ j C, Γ[j]? = some C → (thirdSemantics Δ ρ' δ' ε' (σ j)).1 = ε j)
    (hx : x.code = arityAt (.type 1) (sub σ A))
    (hy : y.code = middleShape 3 1 Δ ρ' (sub σ A) x)
    (hz : z.code = thirdShape Δ ρ' δ' (sub σ A) x y) :
    ∀ j C, (A :: Γ)[j]? = some C →
      (thirdSemantics (sub σ A :: Δ) (push x ρ') (push y δ') (push z ε') (upSub σ j)).1 =
        push z ε j := by
  have hA' := hA.substitute hw hσ
  intro j C hj
  cases j with
  | zero =>
    exact thirdSemantics_var (hε'.up hA' hρ' hx hz) (.cons hw hA') rfl
      (hρ'.up hx) (hδ'.up hA' rfl hy)
  | succ j =>
    exact ((thirdSemantics_ren (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A))
      hρ' (hρ'.up hx) hδ' (hδ'.up hA' rfl hy)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).1).trans (heε j C hj)

theorem thirdSemantics_substitute_related (h : BoundedTyping 3 Γ t T)
    (hw : BoundedWf 3 Δ) (hσ : BoundedSubCtx 3 Γ Δ σ)
    (hk : ∀ j, kindAt (.type 1) (σ j) = false)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (hε : ThirdContext Γ ρ δ ε) (hε' : ThirdContext Δ ρ' δ' ε')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval 3 1 Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (middleSemantics Δ ρ' δ' (σ j)).1 = δ j)
    (heε : ∀ j C, Γ[j]? = some C → (thirdSemantics Δ ρ' δ' ε' (σ j)).1 = ε j) :
    (thirdSemantics Δ ρ' δ' ε' (sub σ t)).1 = (thirdSemantics Γ ρ δ ε t).1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (thirdSemantics Δ ρ' δ' ε' (sub σ t)).2 = (thirdSemantics Γ ρ δ ε t).2) := by
  induction t generalizing Γ T Δ σ ρ ρ' δ δ' ε ε' with
  | var j =>
    obtain ⟨A, hj, hc⟩ := h.generation
    have hv : (thirdSemantics Δ ρ' δ' ε' (sub σ (.var j))).1 =
        (thirdSemantics Γ ρ δ ε (.var j)).1 := by
      rw [thirdSemantics_var hε h.wf hj hρ hδ]
      exact heε j A hj
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f g
    rw [thirdSemantics_decode (hs.substitute hw hσ) hs.var_below_top hρ' hδ',
      thirdSemantics_decode hs hs.var_below_top hρ hδ, hv,
      (middleSemantics_substitute_related hs hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
    exact congrArg (fun k => thirdDecode (some s) k (middleSemantics Γ ρ δ (.var j)).1
      (thirdSemantics Γ ρ δ ε (.var j)).1 u f g)
      (congrArg ShapeValue.asArity (middleShapeEval_substitute_related hs hw hσ hk heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    refine ⟨?_, fun _ _ => rfl⟩
    change (thirdSemantics Δ ρ' δ' ε' (.srt s)).1 = _
    rw [thirdSemantics_sort_value (ht.substitute hw hσ) hρ' hδ', thirdSemantics_sort_value ht hρ hδ,
      ← show sub σ (.srt s) = .srt s from rfl,
      (middleSemantics_substitute_related ht hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
    exact congrArg (fun k => thirdEncode (some s') k (middleSemantics Γ ρ δ (.srt s)).1
      (fun _ _ _ => Candidate.sn))
      (congrArg ShapeValue.asArity (middleShapeEval_substitute_related ht hw hσ hk heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    have hv : (thirdSemantics Δ ρ' δ' ε' (sub σ (.app g a))).1 =
        (thirdSemantics Γ ρ δ ε (.app g a)).1 := by
      change (thirdSemantics Δ ρ' δ' ε' (.app (sub σ g) (sub σ a))).1 = _
      rw [thirdSemantics_app (hg.substitute hw hσ) (ha.substitute hw hσ) hρ' hδ',
        thirdSemantics_app hg ha hρ hδ,
        middleShapeEval_substitute_related hg hw hσ hk heρ,
        middleShapeEval_substitute_related ha hw hσ hk heρ,
        (middleSemantics_substitute_related hg hw hσ hk hρ hρ' hδ hδ' heρ heδ).1,
        (middleSemantics_substitute_related ha hw hσ hk hρ hρ' hδ hδ' heρ heδ).1,
        (ihg hg hw hσ hk hρ hρ' hδ hδ' hε hε' heρ heδ heε).1,
        (iha ha hw hσ hk hρ hρ' hδ hδ' hε hε' heρ heδ heε).1]
      apply thirdApply_congr (arityAt_sub hk A)
      · intro x hx; exact middleShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact middleShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (middleShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun (thirdShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (thirdShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy) (middleShapeSubstitute_related_up hA hw hσ heρ)
          (middleSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)) z) w
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f v
    rw [thirdSemantics_decode (hs.substitute hw hσ) hs.app_below_top hρ' hδ',
      thirdSemantics_decode hs hs.app_below_top hρ hδ, hv,
      (middleSemantics_substitute_related hs hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
    exact congrArg (fun k => thirdDecode (some s) k (middleSemantics Γ ρ δ (.app g a)).1
      (thirdSemantics Γ ρ δ ε (.app g a)).1 u f v)
      (congrArg ShapeValue.asArity (middleShapeEval_substitute_related hs hw hσ hk heρ))
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    refine ⟨?_, ?_⟩
    · change (thirdSemantics Δ ρ' δ' ε' (.lam (sub σ A) (sub (upSub σ) b))).1 = _
      rw [thirdSemantics_lam (hPi.substitute hw hσ) (hb.substitute (.cons hw hA') (hσ.up hw hA')) hρ' hδ',
        thirdSemantics_lam hPi hb hρ hδ,
        ← show sub σ (.lam A b) = .lam (sub σ A) (sub (upSub σ) b) from rfl,
        middleShapeEval_substitute_related (.lam hPi hb hs) hw hσ hk heρ,
        (middleSemantics_substitute_related (.lam hPi hb hs) hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
      apply thirdLambda_congr (arityAt_sub hk A)
      · intro x hx; exact middleShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact middleShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (middleShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun (thirdShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (thirdShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy) (middleShapeSubstitute_related_up hA hw hσ heρ)
          (middleSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)) z) w
      · intro x hx y hy z hz
        exact (ihb hb (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy)
          (hε.up hA hρ (hx.trans (arityAt_sub hk A))
            (hz.trans (congrFun (congrFun (thirdShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y)))
          (hε'.up hA' hρ' hx hz)
          (middleShapeSubstitute_related_up hA hw hσ heρ)
          (middleSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)
          (thirdSubstitute_related_up hA hw hσ hρ' hδ' hε' heε hx hy hz)).1
    · intro s hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hrule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) := .pi hA hB hrule hsA hsB hs
    have hA' := hA.substitute hw hσ
    have hm := middleSemantics_substitute_related ht hw hσ hk hρ hρ' hδ hδ' heρ heδ
    have he : thirdSemantics Δ ρ' δ' ε' (sub σ (.pi A B)) = thirdSemantics Γ ρ δ ε (.pi A B) := by
      apply thirdSemantics_pi_compare (ht.substitute hw hσ) ht hρ' hρ hδ' hδ
        (arityAt_sub hk A) (arityAt_sub hk (.pi A B))
        (congrArg ShapeValue.asArity (middleShapeEval_substitute_related ht hw hσ hk heρ))
        (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; exact middleShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact middleShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (middleShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun (thirdShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y
      · intro x hx y hy
        exact thirdShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy) (middleShapeSubstitute_related_up hA hw hσ heρ)
          (middleSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)
      · intro x hx y hy z hz
        exact congrFun (congrFun (congrFun
          ((ihA hA hw hσ hk hρ hρ' hδ hδ' hε hε' heρ heδ heε).2 sA hA) x) y) z
      · intro x hx y hy z hz
        exact (ihB hB (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' rfl hy)
          (hε.up hA hρ (hx.trans (arityAt_sub hk A))
            (hz.trans (congrFun (congrFun (thirdShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y)))
          (hε'.up hA' hρ' hx hz)
          (middleShapeSubstitute_related_up hA hw hσ heρ)
          (middleSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)
          (thirdSubstitute_related_up hA hw hσ hρ' hδ' hε' heε hx hy hz)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

theorem thirdSemantics_subst_value (hb : BoundedTyping 3 (A :: Γ) b B)
    (ha : BoundedTyping 3 Γ a A) (hA : BoundedTyping 3 Γ A (.srt sA))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε) :
    (thirdSemantics Γ ρ δ ε (subst 0 a b)).1 =
      (thirdSemantics (A :: Γ) (push (shapeEval 3 1 Γ ρ a) ρ)
        (push (middleSemantics Γ ρ δ a).1 δ) (push (thirdSemantics Γ ρ δ ε a).1 ε) b).1 := by
  rw [subst_eq_sub]
  apply (thirdSemantics_substitute_related hb ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA rfl (middleSemantics_typed_code ha hρ)) hδ
    (hε.up hA hρ (shapeEval_typed_code ha rfl hρ) (thirdSemantics_typed_code ha hρ hδ)) hε ?_ ?_ ?_).1
  · intro j; cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj; cases j <;> rfl
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact middleSemantics_var hδ ha.wf hj hρ
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact thirdSemantics_var hε ha.wf hj hρ hδ

theorem thirdSemantics_subst_candidate (hB : BoundedTyping 3 (A :: Γ) B (.srt sB))
    (ha : BoundedTyping 3 Γ a A) (hA : BoundedTyping 3 Γ A (.srt sA))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) (hε : ThirdContext Γ ρ δ ε) :
    (thirdSemantics Γ ρ δ ε (subst 0 a B)).2 =
      (thirdSemantics (A :: Γ) (push (shapeEval 3 1 Γ ρ a) ρ)
        (push (middleSemantics Γ ρ δ a).1 δ) (push (thirdSemantics Γ ρ δ ε a).1 ε) B).2 := by
  rw [subst_eq_sub]
  apply (thirdSemantics_substitute_related hB ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA rfl (middleSemantics_typed_code ha hρ)) hδ
    (hε.up hA hρ (shapeEval_typed_code ha rfl hρ) (thirdSemantics_typed_code ha hρ hδ)) hε ?_ ?_ ?_).2 sB hB
  · intro j; cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj; cases j <;> rfl
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact middleSemantics_var hδ ha.wf hj hρ
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact thirdSemantics_var hε ha.wf hj hρ hδ

end Submission.Helpers
