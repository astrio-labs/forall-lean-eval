import Submission.SecondLayerTransport

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 2000000
variable {p : Nat} {δ δ' : Nat → UpperGridValue (p + 1)} {ε ε' : Nat → SecondLayerValue p}

theorem secondLayerSemantics_var (hε : SecondGridContext (p + 1) Γ ρ δ ε)
    (hw : BoundedWf (p + 5) Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) :
    (secondLayerSemantics p Γ ρ δ ε (.var j)).1 = ε j :=
  TowerValue.force_eq _ (hε.var_code hw hj hρ hδ)

theorem secondLayerSubstitute_related_up (hA : BoundedTyping (p + 5) Γ A (.srt s))
    (hw : BoundedWf (p + 5) Δ) (hσ : BoundedSubCtx (p + 5) Γ Δ σ)
    (hρ' : ShapeContext (.type (p + 3)) Δ ρ') (hδ' : FirstGridContext (p + 2) Δ ρ' δ')
    (hε' : SecondGridContext (p + 1) Δ ρ' δ' ε')
    (heε : ∀ j C, Γ[j]? = some C → (secondLayerSemantics p Δ ρ' δ' ε' (σ j)).1 = ε j)
    (hx : x.code = arityAt (.type (p + 3)) (sub σ A))
    (hy : y.code = firstGridShape (p + 2) Δ ρ' (sub σ A) x)
    (hz : z.code = secondGridShape (p + 1) Δ ρ' δ' (sub σ A) x y) :
    ∀ j C, (A :: Γ)[j]? = some C →
      (secondLayerSemantics p (sub σ A :: Δ) (push x ρ') (push y δ') (push z ε') (upSub σ j)).1 =
        push z ε j := by
  have hA' := hA.substitute hw hσ
  intro j C hj
  cases j with
  | zero =>
    exact secondLayerSemantics_var (hε'.up hA' hρ' hx hz) (.cons hw hA') rfl
      (hρ'.up hx) (hδ'.up hA' hy)
  | succ j =>
    exact ((secondLayerSemantics_ren (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A))
      hρ' (hρ'.up hx) hδ' (hδ'.up hA' hy)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).1).trans (heε j C hj)

theorem secondLayerSemantics_substitute_related (h : BoundedTyping (p + 5) Γ t T)
    (hw : BoundedWf (p + 5) Δ) (hσ : BoundedSubCtx (p + 5) Γ Δ σ)
    (hk : ∀ j, kindAt (.type (p + 3)) (σ j) = false)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hρ' : ShapeContext (.type (p + 3)) Δ ρ')
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hδ' : FirstGridContext (p + 2) Δ ρ' δ')
    (hε : SecondGridContext (p + 1) Γ ρ δ ε) (hε' : SecondGridContext (p + 1) Δ ρ' δ' ε')
    (heρ : ∀ j C, Γ[j]? = some C → shapeEval (p + 5) (p + 3) Δ ρ' (σ j) = ρ j)
    (heδ : ∀ j C, Γ[j]? = some C → (upperGridSemantics (p + 1) Δ ρ' δ' (σ j)).1 = δ j)
    (heε : ∀ j C, Γ[j]? = some C → (secondLayerSemantics p Δ ρ' δ' ε' (σ j)).1 = ε j) :
    (secondLayerSemantics p Δ ρ' δ' ε' (sub σ t)).1 = (secondLayerSemantics p Γ ρ δ ε t).1 ∧
    (∀ s, BoundedTyping (p + 5) Γ t (.srt s) →
      (secondLayerSemantics p Δ ρ' δ' ε' (sub σ t)).2 = (secondLayerSemantics p Γ ρ δ ε t).2) := by
  induction t generalizing Γ T Δ σ ρ ρ' δ δ' ε ε' with
  | var j =>
    obtain ⟨A, hj, hc⟩ := h.generation
    have hv : (secondLayerSemantics p Δ ρ' δ' ε' (sub σ (.var j))).1 =
        (secondLayerSemantics p Γ ρ δ ε (.var j)).1 := by
      erw [secondLayerSemantics_var hε h.wf hj hρ hδ]
      exact heε j A hj
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f g
    erw [secondLayerSemantics_decode (hs.substitute hw hσ) hs.var_below_top hρ' hδ',
      secondLayerSemantics_decode hs hs.var_below_top hρ hδ, hv,
      (upperGridSemantics_substitute_related hs hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
    exact congrArg (fun k => secondLayerDecode p (some s) k (upperGridSemantics (p + 1) Γ ρ δ (.var j)).1
      (secondLayerSemantics p Γ ρ δ ε (.var j)).1 u f g)
      (congrArg ShapeValue.asArity (upperShapeEval_substitute_related hs hw hσ hk heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping (p + 5) Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    refine ⟨?_, fun _ _ => rfl⟩
    change (secondLayerSemantics p Δ ρ' δ' ε' (.srt s)).1 = _
    erw [secondLayerSemantics_sort_value (ht.substitute hw hσ) hρ' hδ', secondLayerSemantics_sort_value ht hρ hδ,
      ← show sub σ (.srt s) = .srt s from rfl,
      (upperGridSemantics_substitute_related ht hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
    exact congrArg (fun k => secondLayerEncode p (some s') k (upperGridSemantics (p + 1) Γ ρ δ (.srt s)).1
      (secondLayerSort p s))
      (congrArg ShapeValue.asArity (upperShapeEval_substitute_related ht hw hσ hk heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    have hv : (secondLayerSemantics p Δ ρ' δ' ε' (sub σ (.app g a))).1 =
        (secondLayerSemantics p Γ ρ δ ε (.app g a)).1 := by
      change (secondLayerSemantics p Δ ρ' δ' ε' (.app (sub σ g) (sub σ a))).1 = _
      erw [secondLayerSemantics_app (hg.substitute hw hσ) (ha.substitute hw hσ) hρ' hδ',
        secondLayerSemantics_app hg ha hρ hδ,
        upperShapeEval_substitute_related hg hw hσ hk heρ,
        upperShapeEval_substitute_related ha hw hσ hk heρ,
        (upperGridSemantics_substitute_related hg hw hσ hk hρ hρ' hδ hδ' heρ heδ).1,
        (upperGridSemantics_substitute_related ha hw hσ hk hρ hρ' hδ hδ' heρ heδ).1,
        (ihg hg hw hσ hk hρ hρ' hδ hδ' hε hε' heρ heδ heε).1,
        (iha ha hw hσ hk hρ hρ' hδ hδ' hε hε' heρ heδ heε).1]
      apply secondGridApply_congr (arityAt_sub hk A)
      · intro x hx; exact firstGridShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact firstGridShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (upperShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun (secondGridShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (secondGridShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA (hy.trans (firstGridShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' hy) (upperShapeSubstitute_related_up hA hw hσ heρ)
          (upperSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)) z) w
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f v
    erw [secondLayerSemantics_decode (hs.substitute hw hσ) hs.app_below_top hρ' hδ',
      secondLayerSemantics_decode hs hs.app_below_top hρ hδ, hv,
      (upperGridSemantics_substitute_related hs hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
    exact congrArg (fun k => secondLayerDecode p (some s) k (upperGridSemantics (p + 1) Γ ρ δ (.app g a)).1
      (secondLayerSemantics p Γ ρ δ ε (.app g a)).1 u f v)
      (congrArg ShapeValue.asArity (upperShapeEval_substitute_related hs hw hσ hk heρ))
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.substitute hw hσ
    refine ⟨?_, ?_⟩
    · change (secondLayerSemantics p Δ ρ' δ' ε' (.lam (sub σ A) (sub (upSub σ) b))).1 = _
      erw [secondLayerSemantics_lam (hPi.substitute hw hσ) (hb.substitute (.cons hw hA') (hσ.up hw hA')) hρ' hδ',
        secondLayerSemantics_lam hPi hb hρ hδ,
        ← show sub σ (.lam A b) = .lam (sub σ A) (sub (upSub σ) b) from rfl,
        upperShapeEval_substitute_related (.lam hPi hb hs) hw hσ hk heρ,
        (upperGridSemantics_substitute_related (.lam hPi hb hs) hw hσ hk hρ hρ' hδ hδ' heρ heδ).1]
      apply secondGridLambda_congr (arityAt_sub hk A)
      · intro x hx; exact firstGridShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact firstGridShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (upperShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun (secondGridShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (secondGridShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA (hy.trans (firstGridShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' hy) (upperShapeSubstitute_related_up hA hw hσ heρ)
          (upperSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)) z) w
      · intro x hx y hy z hz
        exact (ihb hb (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA (hy.trans (firstGridShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' hy)
          (hε.up hA hρ (hx.trans (arityAt_sub hk A))
            (hz.trans (congrFun (congrFun (secondGridShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y)))
          (hε'.up hA' hρ' hx hz)
          (upperShapeSubstitute_related_up hA hw hσ heρ)
          (upperSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)
          (secondLayerSubstitute_related_up hA hw hσ hρ' hδ' hε' heε hx hy hz)).1
    · intro s hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hrule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping (p + 5) Γ (.pi A B) (.srt s) := .pi hA hB hrule hsA hsB hs
    have hA' := hA.substitute hw hσ
    have hm := upperGridSemantics_substitute_related ht hw hσ hk hρ hρ' hδ hδ' heρ heδ
    have he : secondLayerSemantics p Δ ρ' δ' ε' (sub σ (.pi A B)) = secondLayerSemantics p Γ ρ δ ε (.pi A B) := by
      apply secondLayerSemantics_pi_compare (ht.substitute hw hσ) ht hρ' hρ hδ' hδ
        (arityAt_sub hk A) (arityAt_sub hk (.pi A B))
        (congrArg ShapeValue.asArity (upperShapeEval_substitute_related ht hw hσ hk heρ))
        (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; exact firstGridShape_substitute_related hA hw hσ hk heρ
      · intro x hx z
        exact firstGridShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (upperShapeSubstitute_related_up hA hw hσ heρ)
      · intro x hx y hy
        exact congrFun (congrFun (secondGridShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y
      · intro x hx y hy
        exact secondGridShape_substitute_related hB (.cons hw hA') (hσ.up hw hA')
          (kindAt_upSub_false hk) (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA (hy.trans (firstGridShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' hy) (upperShapeSubstitute_related_up hA hw hσ heρ)
          (upperSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)
      · intro x hx y hy z hz
        exact congrFun (congrFun (congrFun
          ((ihA hA hw hσ hk hρ hρ' hδ hδ' hε hε' heρ heδ heε).2 sA hA) x) y) z
      · intro x hx y hy z hz
        exact (ihB hB (.cons hw hA') (hσ.up hw hA') (kindAt_upSub_false hk)
          (hρ.up (hx.trans (arityAt_sub hk A))) (hρ'.up hx)
          (hδ.up hA (hy.trans (firstGridShape_substitute_related hA hw hσ hk heρ)))
          (hδ'.up hA' hy)
          (hε.up hA hρ (hx.trans (arityAt_sub hk A))
            (hz.trans (congrFun (congrFun (secondGridShape_substitute_related hA hw hσ hk hρ hρ' hδ hδ' heρ heδ) x) y)))
          (hε'.up hA' hρ' hx hz)
          (upperShapeSubstitute_related_up hA hw hσ heρ)
          (upperSubstitute_related_up hA hw hσ hρ' hδ' heδ hx hy)
          (secondLayerSubstitute_related_up hA hw hσ hρ' hδ' hε' heε hx hy hz)).2 sB hB
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

theorem secondLayerSemantics_subst_value (hb : BoundedTyping (p + 5) (A :: Γ) b B)
    (ha : BoundedTyping (p + 5) Γ a A) (hA : BoundedTyping (p + 5) Γ A (.srt sA))
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε) :
    (secondLayerSemantics p Γ ρ δ ε (subst 0 a b)).1 =
      (secondLayerSemantics p (A :: Γ) (push (shapeEval (p + 5) (p + 3) Γ ρ a) ρ)
        (push (upperGridSemantics (p + 1) Γ ρ δ a).1 δ) (push (secondLayerSemantics p Γ ρ δ ε a).1 ε) b).1 := by
  erw [subst_eq_sub]
  apply (secondLayerSemantics_substitute_related hb ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA (upperGridSemantics_typed_code ha hρ)) hδ
    (hε.up hA hρ (shapeEval_typed_code ha rfl hρ) (secondLayerSemantics_typed_code ha hρ hδ)) hε ?_ ?_ ?_).1
  · intro j; cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj; cases j <;> rfl
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact upperGridSemantics_var hδ ha.wf hj hρ
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact secondLayerSemantics_var hε ha.wf hj hρ hδ

theorem secondLayerSemantics_subst_carrier (hB : BoundedTyping (p + 5) (A :: Γ) B (.srt sB))
    (ha : BoundedTyping (p + 5) Γ a A) (hA : BoundedTyping (p + 5) Γ A (.srt sA))
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hδ : FirstGridContext (p + 2) Γ ρ δ) (hε : SecondGridContext (p + 1) Γ ρ δ ε) :
    (secondLayerSemantics p Γ ρ δ ε (subst 0 a B)).2 =
      (secondLayerSemantics p (A :: Γ) (push (shapeEval (p + 5) (p + 3) Γ ρ a) ρ)
        (push (upperGridSemantics (p + 1) Γ ρ δ a).1 δ) (push (secondLayerSemantics p Γ ρ δ ε a).1 ε) B).2 := by
  erw [subst_eq_sub]
  apply (secondLayerSemantics_substitute_related hB ha.wf (.single ha) ?_
    (hρ.up (shapeEval_typed_code ha rfl hρ)) hρ
    (hδ.up hA (upperGridSemantics_typed_code ha hρ)) hδ
    (hε.up hA hρ (shapeEval_typed_code ha rfl hρ) (secondLayerSemantics_typed_code ha hρ hδ)) hε ?_ ?_ ?_).2 sB hB
  · intro j; cases j with
    | zero => exact ha.not_kindAt hA rfl
    | succ j => rfl
  · intro j C hj; cases j <;> rfl
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact upperGridSemantics_var hδ ha.wf hj hρ
  · intro j C hj; cases j with
    | zero => rfl
    | succ j => exact secondLayerSemantics_var hε ha.wf hj hρ hδ

end Submission.Helpers
