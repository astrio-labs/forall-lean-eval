import Submission.UpperGridCongruence

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Comparison of product interpretations includes their carriers at the top sort. -/
theorem upperGridSemantics_pi_compare {p : Nat}
    {δ δ' : Nat → UpperGridValue p}
    (h : BoundedTyping (p + 4) Γ (.pi A B) (.srt s))
    (h' : BoundedTyping (p + 4) Δ (.pi A' B') (.srt s))
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ')
    (ha : arityAt (.type (p + 2)) A = arityAt (.type (p + 2)) A')
    (hp : arityAt (.type (p + 2)) (.pi A B) = arityAt (.type (p + 2)) (.pi A' B'))
    (hk : nextArity (p + 4) (p + 2) Γ ρ (.pi A B) = nextArity (p + 4) (p + 2) Δ ρ' (.pi A' B'))
    (hD : ∀ x, x.code = arityAt (.type (p + 2)) A →
      firstGridShape (p + 1) Γ ρ A x = firstGridShape (p + 1) Δ ρ' A' x)
    (hB : ∀ x, x.code = arityAt (.type (p + 2)) A → ∀ z,
      firstGridShape (p + 1) (A :: Γ) (push x ρ) B z =
        firstGridShape (p + 1) (A' :: Δ) (push x ρ') B' z)
    (hd : ∀ x, x.code = arityAt (.type (p + 2)) A → ∀ y,
      y.code = firstGridShape (p + 1) Γ ρ A x →
      (upperGridSemantics p Γ ρ δ A).2 x y = (upperGridSemantics p Δ ρ' δ' A').2 x y)
    (hc : ∀ x, x.code = arityAt (.type (p + 2)) A → ∀ y,
      y.code = firstGridShape (p + 1) Γ ρ A x →
      (upperGridSemantics p (A :: Γ) (push x ρ) (push y δ) B).2 =
        (upperGridSemantics p (A' :: Δ) (push x ρ') (push y δ') B').2) :
    upperGridSemantics p Γ ρ δ (.pi A B) = upperGridSemantics p Δ ρ' δ' (.pi A' B') := by
  have hshape (u : ShapeValue) :
      firstGridShape (p + 1) Γ ρ (.pi A B) u = firstGridShape (p + 1) Δ ρ' (.pi A' B') u := by
    rw [firstGridShape_pi h hρ, firstGridShape_pi h' hρ']
    exact firstGridProduct_congr ha hD hB
  have hcarrier :
      (upperGridSemantics p Γ ρ δ (.pi A B)).2 = (upperGridSemantics p Δ ρ' δ' (.pi A' B')).2 := by
    funext u f
    simp only [upperGridSemantics]
    unfold upperGridCanonical
    dsimp only
    rw [hp, hshape]
    apply upperGridProduct_congr ha hD hB hd
    intro x hx y hy z w
    exact congrFun (congrFun (hc x hx y hy) z) w
  apply Prod.ext
  · rw [upperGridSemantics_pi_value h hρ, upperGridSemantics_pi_value h' hρ', hk, hcarrier]
  · exact hcarrier

/-- Renaming preserves values and the carrier families of formed types. -/
theorem upperGridSemantics_ren {p : Nat} {δ δ' : Nat → UpperGridValue p} (h : BoundedTyping (p + 4) Γ t T) (hw : BoundedWf (p + 4) Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type (p + 2)) Γ ρ) (hρ' : ShapeContext (.type (p + 2)) Δ ρ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j) :
    (upperGridSemantics p Δ ρ' δ' (ren r t)).1 = (upperGridSemantics p Γ ρ δ t).1 ∧
    (∀ s, BoundedTyping (p + 4) Γ t (.srt s) →
      (upperGridSemantics p Δ ρ' δ' (ren r t)).2 = (upperGridSemantics p Γ ρ δ t).2) := by
  induction t generalizing Γ T Δ r ρ ρ' δ δ' with
  | var j =>
    have hv : (upperGridSemantics p Δ ρ' δ' (ren r (.var j))).1 =
        (upperGridSemantics p Γ ρ δ (.var j)).1 := by
      change (δ' (r j)).force _ = (δ j).force _
      rw [heδ j, ← show ren r (.var j) = .var (r j) from rfl,
        inferredFirstGrid_ren h hw hr hρ hρ' heρ]
    refine ⟨hv, ?_⟩
    intro s hs
    have hs' := hs.rename hw hr
    funext u f
    rw [upperGridSemantics_decode hs' hs.var_below_top hρ',
      upperGridSemantics_decode hs hs.var_below_top hρ, hv]
    exact congrArg (fun k => upperGridDecode p (some s) k
      (upperGridSemantics p Γ ρ δ (.var j)).1 u f)
      (congrArg ShapeValue.asArity (shapeEval_ren hs hw hr rfl heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping (p + 4) Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    have ht' := ht.rename hw hr
    refine ⟨?_, fun _ _ => rfl⟩
    change (upperGridSemantics p Δ ρ' δ' (.srt s)).1 = _
    rw [upperGridSemantics_sort_value ht' hρ', upperGridSemantics_sort_value ht hρ]
    exact congrArg (fun k => upperGridEncode p (some s') k (upperGridSort p s))
      (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hv : (upperGridSemantics p Δ ρ' δ' (ren r (.app g a))).1 =
        (upperGridSemantics p Γ ρ δ (.app g a)).1 := by
      change (upperGridSemantics p Δ ρ' δ' (.app (ren r g) (ren r a))).1 = _
      rw [upperGridSemantics_app (hg.rename hw hr) (ha.rename hw hr) hρ',
        upperGridSemantics_app hg ha hρ,
        shapeEval_ren hg hw hr rfl heρ, shapeEval_ren ha hw hr rfl heρ,
        (ihg hg hw hr hρ hρ' heρ heδ).1, (iha ha hw hr hρ hρ' heρ heδ).1]
      apply firstGridApply_congr (arityAt_ren _ _ _)
      · intro x hx
        exact firstGridShape_ren hA hw hr heρ
      · intro x hx z
        apply firstGridShape_ren hB (.cons hw (hA.rename hw hr)) (hr.up A)
        intro j
        cases j with
        | zero => rfl
        | succ j => exact heρ j
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f
    rw [upperGridSemantics_decode (hs.rename hw hr) hs.app_below_top hρ',
      upperGridSemantics_decode hs hs.app_below_top hρ, hv]
    exact congrArg (fun k => upperGridDecode p (some s) k
      (upperGridSemantics p Γ ρ δ (.app g a)).1 u f)
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
    · change (upperGridSemantics p Δ ρ' δ' (.lam (ren r A) (ren (upRen r) b))).1 = _
      rw [upperGridSemantics_lam (hPi.rename hw hr)
          (hb.rename (.cons hw hA') (hr.up A)) hρ', upperGridSemantics_lam hPi hb hρ,
        ← show ren r (.lam A b) = .lam (ren r A) (ren (upRen r) b) from rfl,
        shapeEval_ren (.lam hPi hb hs) hw hr rfl heρ]
      apply firstGridLambda_congr (arityAt_ren _ _ _)
      · intro x hx
        exact firstGridShape_ren hA hw hr heρ
      · intro x hx z
        exact firstGridShape_ren hB (.cons hw hA') (hr.up A) (heρup x)
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
    have ht : BoundedTyping (p + 4) Γ (.pi A B) (.srt s) :=
      .pi hA hB hrule hsA hsB hs
    have hA' := hA.rename hw hr
    have heρup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j
      cases j with
      | zero => rfl
      | succ j => exact heρ j
    have he : upperGridSemantics p Δ ρ' δ' (ren r (.pi A B)) =
        upperGridSemantics p Γ ρ δ (.pi A B) := by
      apply upperGridSemantics_pi_compare (ht.rename hw hr) ht hρ' hρ
        (arityAt_ren _ _ _) (arityAt_ren (.type (p + 2)) r (.pi A B))
        (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ))
      · intro x hx
        exact firstGridShape_ren hA hw hr heρ
      · intro x hx z
        exact firstGridShape_ren hB (.cons hw hA') (hr.up A) (heρup x)
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
