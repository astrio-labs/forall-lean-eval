import Submission.MiddleDecoding

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Comparison of product interpretations includes their carriers at the top sort. -/
theorem middleSemantics_pi_compare
    (h : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (h' : BoundedTyping 3 Δ (.pi A' B') (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (ha : arityAt (.type 1) A = arityAt (.type 1) A')
    (hp : arityAt (.type 1) (.pi A B) = arityAt (.type 1) (.pi A' B'))
    (hk : nextArity 3 1 Γ ρ (.pi A B) = nextArity 3 1 Δ ρ' (.pi A' B'))
    (hD : ∀ x, x.code = arityAt (.type 1) A →
      middleShape 3 1 Γ ρ A x = middleShape 3 1 Δ ρ' A' x)
    (hB : ∀ x, x.code = arityAt (.type 1) A → ∀ z,
      middleShape 3 1 (A :: Γ) (push x ρ) B z =
        middleShape 3 1 (A' :: Δ) (push x ρ') B' z)
    (hd : ∀ x, x.code = arityAt (.type 1) A → ∀ y,
      y.code = middleShape 3 1 Γ ρ A x →
      (middleSemantics Γ ρ δ A).2 x y = (middleSemantics Δ ρ' δ' A').2 x y)
    (hc : ∀ x, x.code = arityAt (.type 1) A → ∀ y,
      y.code = middleShape 3 1 Γ ρ A x →
      (middleSemantics (A :: Γ) (push x ρ) (push y δ) B).2 =
        (middleSemantics (A' :: Δ) (push x ρ') (push y δ') B').2) :
    middleSemantics Γ ρ δ (.pi A B) = middleSemantics Δ ρ' δ' (.pi A' B') := by
  have hshape (u : ShapeValue) :
      middleShape 3 1 Γ ρ (.pi A B) u = middleShape 3 1 Δ ρ' (.pi A' B') u := by
    rw [middleShape_pi h rfl hρ, middleShape_pi h' rfl hρ']
    exact middleProduct_congr ha hD hB
  have hcarrier :
      (middleSemantics Γ ρ δ (.pi A B)).2 = (middleSemantics Δ ρ' δ' (.pi A' B')).2 := by
    funext u f
    simp only [middleSemantics]
    unfold middleCanonical
    dsimp only
    rw [hp, hshape]
    apply thirdProduct_congr ha hD hB hd
    intro x hx y hy z w
    exact congrFun (congrFun (hc x hx y hy) z) w
  apply Prod.ext
  · rw [middleSemantics_pi_value h hρ, middleSemantics_pi_value h' hρ', hk, hcarrier]
  · exact hcarrier

/-- Renaming preserves values and the carrier families of formed types. -/
theorem middleSemantics_ren (h : BoundedTyping 3 Γ t T) (hw : BoundedWf 3 Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j) :
    (middleSemantics Δ ρ' δ' (ren r t)).1 = (middleSemantics Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (middleSemantics Δ ρ' δ' (ren r t)).2 = (middleSemantics Γ ρ δ t).2) := by
  induction t generalizing Γ T Δ r ρ ρ' δ δ' with
  | var j =>
    have hv : (middleSemantics Δ ρ' δ' (ren r (.var j))).1 =
        (middleSemantics Γ ρ δ (.var j)).1 := by
      change (δ' (r j)).force _ = (δ j).force _
      rw [heδ j, ← show ren r (.var j) = .var (r j) from rfl,
        inferredMiddle_ren h hw hr rfl hρ hρ' heρ]
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' := hs.rename hw hr
    funext u f
    rw [middleSemantics_decode hs' hs.var_below_top hρ',
      middleSemantics_decode hs hs.var_below_top hρ, hv]
    exact congrArg (fun k => middleDecode (some s) k
      (middleSemantics Γ ρ δ (.var j)).1 u f)
      (congrArg ShapeValue.asArity (shapeEval_ren hs hw hr rfl heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    have ht' := ht.rename hw hr
    refine ⟨?_, fun _ _ => rfl⟩
    change (middleSemantics Δ ρ' δ' (.srt s)).1 = _
    rw [middleSemantics_sort_value ht' hρ', middleSemantics_sort_value ht hρ]
    exact congrArg (fun k => middleEncode (some s') k (thirdSort s))
      (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hv : (middleSemantics Δ ρ' δ' (ren r (.app g a))).1 =
        (middleSemantics Γ ρ δ (.app g a)).1 := by
      change (middleSemantics Δ ρ' δ' (.app (ren r g) (ren r a))).1 = _
      rw [middleSemantics_app (hg.rename hw hr) (ha.rename hw hr) hρ',
        middleSemantics_app hg ha hρ,
        shapeEval_ren hg hw hr rfl heρ, shapeEval_ren ha hw hr rfl heρ,
        (ihg hg hw hr hρ hρ' heρ heδ).1, (iha ha hw hr hρ hρ' heρ heδ).1]
      apply middleApply_congr (arityAt_ren _ _ _)
      · intro x hx
        exact middleShape_ren hA hw hr rfl heρ
      · intro x hx z
        apply middleShape_ren hB (.cons hw (hA.rename hw hr)) (hr.up A) rfl
        intro j
        cases j with
        | zero => rfl
        | succ j => exact heρ j
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f
    rw [middleSemantics_decode (hs.rename hw hr) hs.app_below_top hρ',
      middleSemantics_decode hs hs.app_below_top hρ, hv]
    exact congrArg (fun k => middleDecode (some s) k
      (middleSemantics Γ ρ δ (.app g a)).1 u f)
      (congrArg ShapeValue.asArity (shapeEval_ren hs hw hr rfl heρ))
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.rename hw hr
    have heρup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j
      cases j with
      | zero => rfl
      | succ j => exact heρ j
    refine ⟨?_, ?_⟩
    · change (middleSemantics Δ ρ' δ' (.lam (ren r A) (ren (upRen r) b))).1 = _
      rw [middleSemantics_lam (hPi.rename hw hr)
          (hb.rename (.cons hw hA') (hr.up A)) hρ', middleSemantics_lam hPi hb hρ,
        ← show ren r (.lam A b) = .lam (ren r A) (ren (upRen r) b) from rfl,
        shapeEval_ren (.lam hPi hb hs) hw hr rfl heρ]
      apply middleLambda_congr (arityAt_ren _ _ _)
      · intro x hx
        exact middleShape_ren hA hw hr rfl heρ
      · intro x hx z
        exact middleShape_ren hB (.cons hw hA') (hr.up A) rfl (heρup x)
      · intro x hx y hy
        apply (ihb hb (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (heρup x) ?_).1
        intro j
        cases j with
        | zero => rfl
        | succ j => exact heδ j
    · intro r hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hrule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) :=
      .pi hA hB hrule hsA hsB hs
    have hA' := hA.rename hw hr
    have heρup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j
      cases j with
      | zero => rfl
      | succ j => exact heρ j
    have he : middleSemantics Δ ρ' δ' (ren r (.pi A B)) =
        middleSemantics Γ ρ δ (.pi A B) := by
      apply middleSemantics_pi_compare (ht.rename hw hr) ht hρ' hρ
        (arityAt_ren _ _ _) (arityAt_ren (.type 1) r (.pi A B))
        (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ))
      · intro x hx
        exact middleShape_ren hA hw hr rfl heρ
      · intro x hx z
        exact middleShape_ren hB (.cons hw hA') (hr.up A) rfl (heρup x)
      · intro x hx y hy
        exact congrFun (congrFun ((ihA hA hw hr hρ hρ' heρ heδ).2 sA hA) x) y
      · intro x hx y hy
        apply (ihB hB (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (heρup x) ?_).2 sB hB
        intro j
        cases j with
        | zero => rfl
        | succ j => exact heδ j
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

end Submission.Helpers
