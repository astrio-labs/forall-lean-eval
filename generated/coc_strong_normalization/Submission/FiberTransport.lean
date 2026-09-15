import Submission.FiberUniverse

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Comparison of product interpretations includes their candidates at the top sort. -/
theorem fiberSemantics_pi_compare
    (h : BoundedTyping 2 Γ (.pi A B) (.srt s))
    (h' : BoundedTyping 2 Δ (.pi A' B') (.srt s))
    (hρ : ShapeContext (.type 0) Γ ρ) (hρ' : ShapeContext (.type 0) Δ ρ')
    (ha : arityAt (.type 0) A = arityAt (.type 0) A')
    (hp : arityAt (.type 0) (.pi A B) = arityAt (.type 0) (.pi A' B'))
    (hk : nextArity 2 0 Γ ρ (.pi A B) = nextArity 2 0 Δ ρ' (.pi A' B'))
    (hD : ∀ x, x.code = arityAt (.type 0) A →
      fiberShape 2 0 Γ ρ A x = fiberShape 2 0 Δ ρ' A' x)
    (hB : ∀ x, x.code = arityAt (.type 0) A → ∀ z,
      fiberShape 2 0 (A :: Γ) (push x ρ) B z =
        fiberShape 2 0 (A' :: Δ) (push x ρ') B' z)
    (hd : ∀ x, x.code = arityAt (.type 0) A → ∀ y,
      y.code = fiberShape 2 0 Γ ρ A x →
      (fiberSemantics Γ ρ δ A).2 x y = (fiberSemantics Δ ρ' δ' A').2 x y)
    (hc : ∀ x, x.code = arityAt (.type 0) A → ∀ y,
      y.code = fiberShape 2 0 Γ ρ A x →
      (fiberSemantics (A :: Γ) (push x ρ) (push y δ) B).2 =
        (fiberSemantics (A' :: Δ) (push x ρ') (push y δ') B').2) :
    fiberSemantics Γ ρ δ (.pi A B) = fiberSemantics Δ ρ' δ' (.pi A' B') := by
  have hshape (u : ShapeValue) :
      fiberShape 2 0 Γ ρ (.pi A B) u = fiberShape 2 0 Δ ρ' (.pi A' B') u := by
    rw [fiberShape_pi h rfl hρ, fiberShape_pi h' rfl hρ']
    exact fiberProduct_congr ha hD hB
  have hcandidate :
      (fiberSemantics Γ ρ δ (.pi A B)).2 = (fiberSemantics Δ ρ' δ' (.pi A' B')).2 := by
    funext u f
    simp only [fiberSemantics]
    unfold fiberCanonical
    dsimp only
    rw [hp, hshape]
    apply fiberCandidatePi_congr ha hD hB hd
    intro x hx y hy z w
    exact congrFun (congrFun (hc x hx y hy) z) w
  apply Prod.ext
  · rw [fiberSemantics_pi_value h hρ, fiberSemantics_pi_value h' hρ', hk, hcandidate]
  · exact hcandidate

/-- Renaming preserves values and the candidate families of formed types. -/
theorem fiberSemantics_ren (h : BoundedTyping 2 Γ t T) (hw : BoundedWf 2 Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type 0) Γ ρ) (hρ' : ShapeContext (.type 0) Δ ρ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j) :
    (fiberSemantics Δ ρ' δ' (ren r t)).1 = (fiberSemantics Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping 2 Γ t (.srt s) →
      (fiberSemantics Δ ρ' δ' (ren r t)).2 = (fiberSemantics Γ ρ δ t).2) := by
  induction t generalizing Γ T Δ r ρ ρ' δ δ' with
  | var j =>
    have hv : (fiberSemantics Δ ρ' δ' (ren r (.var j))).1 =
        (fiberSemantics Γ ρ δ (.var j)).1 := by
      change (δ' (r j)).force _ = (δ j).force _
      rw [heδ j, ← show ren r (.var j) = .var (r j) from rfl,
        inferredFiber_ren h hw hr rfl hρ hρ' heρ]
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' := hs.rename hw hr
    funext u f
    rw [fiberSemantics_decode hs' hs.var_below_top hρ',
      fiberSemantics_decode hs hs.var_below_top hρ, hv]
    exact congrArg (fun k => fiberDecode (some s) k
      (fiberSemantics Γ ρ δ (.var j)).1 u f)
      (congrArg ShapeValue.asArity (shapeEval_ren hs hw hr rfl heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping 2 Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    have ht' := ht.rename hw hr
    refine ⟨?_, fun _ _ => rfl⟩
    change (fiberSemantics Δ ρ' δ' (.srt s)).1 = _
    rw [fiberSemantics_sort_value ht' hρ', fiberSemantics_sort_value ht hρ]
    exact congrArg (fun k => fiberEncode (some s') k (fun _ _ => Candidate.sn))
      (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hv : (fiberSemantics Δ ρ' δ' (ren r (.app g a))).1 =
        (fiberSemantics Γ ρ δ (.app g a)).1 := by
      change (fiberSemantics Δ ρ' δ' (.app (ren r g) (ren r a))).1 = _
      rw [fiberSemantics_app (hg.rename hw hr) (ha.rename hw hr) hρ',
        fiberSemantics_app hg ha hρ,
        shapeEval_ren hg hw hr rfl heρ, shapeEval_ren ha hw hr rfl heρ,
        (ihg hg hw hr hρ hρ' heρ heδ).1, (iha ha hw hr hρ hρ' heρ heδ).1]
      apply fiberApply_congr (arityAt_ren _ _ _)
      · intro x hx
        exact fiberShape_ren hA hw hr rfl heρ
      · intro x hx z
        apply fiberShape_ren hB (.cons hw (hA.rename hw hr)) (hr.up A) rfl
        intro j
        cases j with
        | zero => rfl
        | succ j => exact heρ j
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f
    rw [fiberSemantics_decode (hs.rename hw hr) hs.app_below_top hρ',
      fiberSemantics_decode hs hs.app_below_top hρ, hv]
    exact congrArg (fun k => fiberDecode (some s) k
      (fiberSemantics Γ ρ δ (.app g a)).1 u f)
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
    · change (fiberSemantics Δ ρ' δ' (.lam (ren r A) (ren (upRen r) b))).1 = _
      rw [fiberSemantics_lam (hPi.rename hw hr)
          (hb.rename (.cons hw hA') (hr.up A)) hρ', fiberSemantics_lam hPi hb hρ,
        ← show ren r (.lam A b) = .lam (ren r A) (ren (upRen r) b) from rfl,
        shapeEval_ren (.lam hPi hb hs) hw hr rfl heρ]
      apply fiberLambda_congr (arityAt_ren _ _ _)
      · intro x hx
        exact fiberShape_ren hA hw hr rfl heρ
      · intro x hx z
        exact fiberShape_ren hB (.cons hw hA') (hr.up A) rfl (heρup x)
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
    have ht : BoundedTyping 2 Γ (.pi A B) (.srt s) :=
      .pi hA hB hrule hsA hsB hs
    have hA' := hA.rename hw hr
    have heρup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j
      cases j with
      | zero => rfl
      | succ j => exact heρ j
    have he : fiberSemantics Δ ρ' δ' (ren r (.pi A B)) =
        fiberSemantics Γ ρ δ (.pi A B) := by
      apply fiberSemantics_pi_compare (ht.rename hw hr) ht hρ' hρ
        (arityAt_ren _ _ _) (arityAt_ren (.type 0) r (.pi A B))
        (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ))
      · intro x hx
        exact fiberShape_ren hA hw hr rfl heρ
      · intro x hx z
        exact fiberShape_ren hB (.cons hw hA') (hr.up A) rfl (heρup x)
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
