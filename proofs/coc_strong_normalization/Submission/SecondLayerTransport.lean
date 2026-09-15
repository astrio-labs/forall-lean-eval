import Submission.SecondLayerTyping

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 2000000
variable {p : Nat} {δ δ' : Nat → UpperGridValue (p + 1)} {ε ε' : Nat → SecondLayerValue p}

theorem secondLayerSemantics_pi_compare
    (h : BoundedTyping (p + 5) Γ (.pi A B) (.srt s))
    (h' : BoundedTyping (p + 5) Δ (.pi A' B') (.srt s))
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hρ' : ShapeContext (.type (p + 3)) Δ ρ')
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hδ' : FirstGridContext (p + 2) Δ ρ' δ')
    (ha : arityAt (.type (p + 3)) A = arityAt (.type (p + 3)) A')
    (hp : arityAt (.type (p + 3)) (.pi A B) = arityAt (.type (p + 3)) (.pi A' B'))
    (hk : nextArity (p + 5) (p + 3) Γ ρ (.pi A B) = nextArity (p + 5) (p + 3) Δ ρ' (.pi A' B'))
    (hm : upperGridSemantics (p + 1) Γ ρ δ (.pi A B) = upperGridSemantics (p + 1) Δ ρ' δ' (.pi A' B'))
    (hD : ∀ x, x.code = arityAt (.type (p + 3)) A →
      firstGridShape (p + 2) Γ ρ A x = firstGridShape (p + 2) Δ ρ' A' x)
    (hB : ∀ x, x.code = arityAt (.type (p + 3)) A → ∀ z,
      firstGridShape (p + 2) (A :: Γ) (push x ρ) B z = firstGridShape (p + 2) (A' :: Δ) (push x ρ') B' z)
    (hd : ∀ x, x.code = arityAt (.type (p + 3)) A → ∀ y,
      y.code = firstGridShape (p + 2) Γ ρ A x → secondGridShape (p + 1) Γ ρ δ A x y = secondGridShape (p + 1) Δ ρ' δ' A' x y)
    (hc : ∀ x, x.code = arityAt (.type (p + 3)) A → ∀ y,
      y.code = firstGridShape (p + 2) Γ ρ A x →
      secondGridShape (p + 1) (A :: Γ) (push x ρ) (push y δ) B =
        secondGridShape (p + 1) (A' :: Δ) (push x ρ') (push y δ') B')
    (hP : ∀ x, x.code = arityAt (.type (p + 3)) A → ∀ y,
      y.code = firstGridShape (p + 2) Γ ρ A x → ∀ z, z.code = secondGridShape (p + 1) Γ ρ δ A x y →
      (secondLayerSemantics p Γ ρ δ ε A).2 x y z = (secondLayerSemantics p Δ ρ' δ' ε' A').2 x y z)
    (hQ : ∀ x, x.code = arityAt (.type (p + 3)) A → ∀ y,
      y.code = firstGridShape (p + 2) Γ ρ A x → ∀ z, z.code = secondGridShape (p + 1) Γ ρ δ A x y →
      (secondLayerSemantics p (A :: Γ) (push x ρ) (push y δ) (push z ε) B).2 =
        (secondLayerSemantics p (A' :: Δ) (push x ρ') (push y δ') (push z ε') B').2) :
    secondLayerSemantics p Γ ρ δ ε (.pi A B) = secondLayerSemantics p Δ ρ' δ' ε' (.pi A' B') := by
  have hshape (u : ShapeValue) :
      firstGridShape (p + 2) Γ ρ (.pi A B) u = firstGridShape (p + 2) Δ ρ' (.pi A' B') u := by
    erw [firstGridShape_pi h hρ, firstGridShape_pi h' hρ']
    exact firstGridProduct_congr ha hD hB
  have ht : secondGridShape (p + 1) Γ ρ δ (.pi A B) = secondGridShape (p + 1) Δ ρ' δ' (.pi A' B') := congrArg Prod.snd hm
  have hcandidate : (secondLayerSemantics p Γ ρ δ ε (.pi A B)).2 =
      (secondLayerSemantics p Δ ρ' δ' ε' (.pi A' B')).2 := by
    funext u f v
    simp only [secondLayerSemantics]
    unfold secondLayerCanonical
    dsimp only
    erw [hp, hshape, ht]
    apply secondLayerProduct_congr ha hD hB hd
      (fun x hx y hy z w => congrFun (congrFun (hc x hx y hy) z) w) hP
    intro x hx y hy z hz v w r
    exact congrFun (congrFun (congrFun (hQ x hx y hy z hz) v) w) r
  apply Prod.ext
  · erw [secondLayerSemantics_pi_value h hρ hδ, secondLayerSemantics_pi_value h' hρ' hδ',
      hk, congrArg Prod.fst hm, hcandidate]
  · exact hcandidate

theorem secondLayerSemantics_ren (h : BoundedTyping (p + 5) Γ t T) (hw : BoundedWf (p + 5) Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type (p + 3)) Γ ρ) (hρ' : ShapeContext (.type (p + 3)) Δ ρ')
    (hδ : FirstGridContext (p + 2) Γ ρ δ) (hδ' : FirstGridContext (p + 2) Δ ρ' δ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j)
    (heε : ∀ j, ε' (r j) = ε j) :
    (secondLayerSemantics p Δ ρ' δ' ε' (ren r t)).1 = (secondLayerSemantics p Γ ρ δ ε t).1 ∧
    (∀ s, BoundedTyping (p + 5) Γ t (.srt s) →
      (secondLayerSemantics p Δ ρ' δ' ε' (ren r t)).2 = (secondLayerSemantics p Γ ρ δ ε t).2) := by
  induction t generalizing Γ T Δ r ρ ρ' δ δ' ε ε' with
  | var j =>
    have hv : (secondLayerSemantics p Δ ρ' δ' ε' (ren r (.var j))).1 =
        (secondLayerSemantics p Γ ρ δ ε (.var j)).1 := by
      change (ε' (r j)).force _ = (ε j).force _
      erw [heε j, ← show ren r (.var j) = .var (r j) from rfl,
        inferredSecondGrid_ren h hw hr hρ hρ' hδ hδ' heρ heδ]
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f v
    erw [secondLayerSemantics_decode (hs.rename hw hr) hs.var_below_top hρ' hδ',
      secondLayerSemantics_decode hs hs.var_below_top hρ hδ, hv,
      (upperGridSemantics_ren hs hw hr hρ hρ' heρ heδ).1]
    exact congrArg (fun k => secondLayerDecode p (some s) k (upperGridSemantics (p + 1) Γ ρ δ (.var j)).1
      (secondLayerSemantics p Γ ρ δ ε (.var j)).1 u f v)
      (congrArg ShapeValue.asArity (shapeEval_ren hs hw hr rfl heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping (p + 5) Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    refine ⟨?_, fun _ _ => rfl⟩
    change (secondLayerSemantics p Δ ρ' δ' ε' (.srt s)).1 = _
    erw [secondLayerSemantics_sort_value (ht.rename hw hr) hρ' hδ', secondLayerSemantics_sort_value ht hρ hδ,
      ← show ren r (.srt s) = .srt s from rfl,
      (upperGridSemantics_ren ht hw hr hρ hρ' heρ heδ).1]
    exact congrArg (fun k => secondLayerEncode p (some s') k (upperGridSemantics (p + 1) Γ ρ δ (.srt s)).1
      (secondLayerSort p s))
      (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ))
  | app g a ihg iha =>
    obtain ⟨A, B, hg, ha, hc⟩ := h.generation
    obtain ⟨sPi, hPi⟩ := hg.pi_type
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heρ j
    have hdup (y : UpperGridValue (p + 1)) : ∀ j, push y δ' (upRen r j) = push y δ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heδ j
    have hv : (secondLayerSemantics p Δ ρ' δ' ε' (ren r (.app g a))).1 =
        (secondLayerSemantics p Γ ρ δ ε (.app g a)).1 := by
      change (secondLayerSemantics p Δ ρ' δ' ε' (.app (ren r g) (ren r a))).1 = _
      erw [secondLayerSemantics_app (hg.rename hw hr) (ha.rename hw hr) hρ' hδ',
        secondLayerSemantics_app hg ha hρ hδ,
        shapeEval_ren hg hw hr rfl heρ, shapeEval_ren ha hw hr rfl heρ,
        (upperGridSemantics_ren hg hw hr hρ hρ' heρ heδ).1,
        (upperGridSemantics_ren ha hw hr hρ hρ' heρ heδ).1,
        (ihg hg hw hr hρ hρ' hδ hδ' heρ heδ heε).1,
        (iha ha hw hr hρ hρ' hδ hδ' heρ heδ heε).1]
      apply secondGridApply_congr (arityAt_ren _ _ _)
      · intro x hx; exact firstGridShape_ren hA hw hr heρ
      · intro x hx z
        exact firstGridShape_ren hB (.cons hw (hA.rename hw hr)) (hr.up A) (hup x)
      · intro x hx y hy
        exact congrFun (congrFun (secondGridShape_ren hA hw hr hρ hρ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (secondGridShape_ren hB (.cons hw (hA.rename hw hr)) (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (hup x) (hdup y)) z) w
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f v
    erw [secondLayerSemantics_decode (hs.rename hw hr) hs.app_below_top hρ' hδ',
      secondLayerSemantics_decode hs hs.app_below_top hρ hδ, hv,
      (upperGridSemantics_ren hs hw hr hρ hρ' heρ heδ).1]
    exact congrArg (fun k => secondLayerDecode p (some s) k (upperGridSemantics (p + 1) Γ ρ δ (.app g a)).1
      (secondLayerSemantics p Γ ρ δ ε (.app g a)).1 u f v)
      (congrArg ShapeValue.asArity (shapeEval_ren hs hw hr rfl heρ))
  | lam A b ihA ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
    have hA' := hA.rename hw hr
    have hup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heρ j
    have hdup (y : UpperGridValue (p + 1)) : ∀ j, push y δ' (upRen r j) = push y δ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heδ j
    refine ⟨?_, ?_⟩
    · change (secondLayerSemantics p Δ ρ' δ' ε' (.lam (ren r A) (ren (upRen r) b))).1 = _
      erw [secondLayerSemantics_lam (hPi.rename hw hr) (hb.rename (.cons hw hA') (hr.up A)) hρ' hδ',
        secondLayerSemantics_lam hPi hb hρ hδ,
        ← show ren r (.lam A b) = .lam (ren r A) (ren (upRen r) b) from rfl,
        shapeEval_ren (.lam hPi hb hs) hw hr rfl heρ,
        (upperGridSemantics_ren (.lam hPi hb hs) hw hr hρ hρ' heρ heδ).1]
      apply secondGridLambda_congr (arityAt_ren _ _ _)
      · intro x hx; exact firstGridShape_ren hA hw hr heρ
      · intro x hx z; exact firstGridShape_ren hB (.cons hw hA') (hr.up A) (hup x)
      · intro x hx y hy
        exact congrFun (congrFun (secondGridShape_ren hA hw hr hρ hρ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (secondGridShape_ren hB (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (hup x) (hdup y)) z) w
      · intro x hx y hy z hz
        apply (ihb hb (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx)
          (hδ.up hA (hy.trans (firstGridShape_ren hA hw hr heρ)))
          (hδ'.up hA' hy) (hup x) (hdup y) ?_).1
        intro j; cases j with
        | zero => rfl
        | succ j => exact heε j
    · intro s hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hrule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping (p + 5) Γ (.pi A B) (.srt s) := .pi hA hB hrule hsA hsB hs
    have hA' := hA.rename hw hr
    have hup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heρ j
    have hdup (y : UpperGridValue (p + 1)) : ∀ j, push y δ' (upRen r j) = push y δ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heδ j
    have hm := upperGridSemantics_ren ht hw hr hρ hρ' heρ heδ
    have he : secondLayerSemantics p Δ ρ' δ' ε' (ren r (.pi A B)) = secondLayerSemantics p Γ ρ δ ε (.pi A B) := by
      apply secondLayerSemantics_pi_compare (ht.rename hw hr) ht hρ' hρ hδ' hδ
        (arityAt_ren _ _ _) (arityAt_ren (.type (p + 3)) r (.pi A B))
        (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ)) (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; exact firstGridShape_ren hA hw hr heρ
      · intro x hx z; exact firstGridShape_ren hB (.cons hw hA') (hr.up A) (hup x)
      · intro x hx y hy
        exact congrFun (congrFun (secondGridShape_ren hA hw hr hρ hρ' heρ heδ) x) y
      · intro x hx y hy
        exact secondGridShape_ren hB (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (hup x) (hdup y)
      · intro x hx y hy z hz
        exact congrFun (congrFun (congrFun
          ((ihA hA hw hr hρ hρ' hδ hδ' heρ heδ heε).2 sA hA) x) y) z
      · intro x hx y hy z hz
        apply (ihB hB (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx)
          (hδ.up hA (hy.trans (firstGridShape_ren hA hw hr heρ)))
          (hδ'.up hA' hy) (hup x) (hdup y) ?_).2 sB hB
        intro j; cases j with
        | zero => rfl
        | succ j => exact heε j
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

end Submission.Helpers
