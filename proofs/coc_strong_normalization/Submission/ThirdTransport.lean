import Submission.ThirdTypingOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem thirdSemantics_pi_compare
    (h : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (h' : BoundedTyping 3 Δ (.pi A' B') (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (ha : arityAt (.type 1) A = arityAt (.type 1) A')
    (hp : arityAt (.type 1) (.pi A B) = arityAt (.type 1) (.pi A' B'))
    (hk : nextArity 3 1 Γ ρ (.pi A B) = nextArity 3 1 Δ ρ' (.pi A' B'))
    (hm : middleSemantics Γ ρ δ (.pi A B) = middleSemantics Δ ρ' δ' (.pi A' B'))
    (hD : ∀ x, x.code = arityAt (.type 1) A →
      middleShape 3 1 Γ ρ A x = middleShape 3 1 Δ ρ' A' x)
    (hB : ∀ x, x.code = arityAt (.type 1) A → ∀ z,
      middleShape 3 1 (A :: Γ) (push x ρ) B z = middleShape 3 1 (A' :: Δ) (push x ρ') B' z)
    (hd : ∀ x, x.code = arityAt (.type 1) A → ∀ y,
      y.code = middleShape 3 1 Γ ρ A x → thirdShape Γ ρ δ A x y = thirdShape Δ ρ' δ' A' x y)
    (hc : ∀ x, x.code = arityAt (.type 1) A → ∀ y,
      y.code = middleShape 3 1 Γ ρ A x →
      thirdShape (A :: Γ) (push x ρ) (push y δ) B =
        thirdShape (A' :: Δ) (push x ρ') (push y δ') B')
    (hP : ∀ x, x.code = arityAt (.type 1) A → ∀ y,
      y.code = middleShape 3 1 Γ ρ A x → ∀ z, z.code = thirdShape Γ ρ δ A x y →
      (thirdSemantics Γ ρ δ ε A).2 x y z = (thirdSemantics Δ ρ' δ' ε' A').2 x y z)
    (hQ : ∀ x, x.code = arityAt (.type 1) A → ∀ y,
      y.code = middleShape 3 1 Γ ρ A x → ∀ z, z.code = thirdShape Γ ρ δ A x y →
      (thirdSemantics (A :: Γ) (push x ρ) (push y δ) (push z ε) B).2 =
        (thirdSemantics (A' :: Δ) (push x ρ') (push y δ') (push z ε') B').2) :
    thirdSemantics Γ ρ δ ε (.pi A B) = thirdSemantics Δ ρ' δ' ε' (.pi A' B') := by
  have hshape (u : ShapeValue) :
      middleShape 3 1 Γ ρ (.pi A B) u = middleShape 3 1 Δ ρ' (.pi A' B') u := by
    rw [middleShape_pi h rfl hρ, middleShape_pi h' rfl hρ']
    exact middleProduct_congr ha hD hB
  have ht : thirdShape Γ ρ δ (.pi A B) = thirdShape Δ ρ' δ' (.pi A' B') := congrArg Prod.snd hm
  have hcandidate : (thirdSemantics Γ ρ δ ε (.pi A B)).2 =
      (thirdSemantics Δ ρ' δ' ε' (.pi A' B')).2 := by
    funext u f v
    simp only [thirdSemantics]
    unfold thirdCanonical
    dsimp only
    rw [hp, hshape, ht]
    apply thirdCandidatePi_congr ha hD hB hd
      (fun x hx y hy z w => congrFun (congrFun (hc x hx y hy) z) w) hP
    intro x hx y hy z hz v w r
    exact congrFun (congrFun (congrFun (hQ x hx y hy z hz) v) w) r
  apply Prod.ext
  · rw [thirdSemantics_pi_value h hρ hδ, thirdSemantics_pi_value h' hρ' hδ',
      hk, congrArg Prod.fst hm, hcandidate]
  · exact hcandidate

theorem thirdSemantics_ren (h : BoundedTyping 3 Γ t T) (hw : BoundedWf 3 Δ)
    (hr : RenCtx Γ Δ r)
    (hρ : ShapeContext (.type 1) Γ ρ) (hρ' : ShapeContext (.type 1) Δ ρ')
    (hδ : MiddleContext 3 1 Γ ρ δ) (hδ' : MiddleContext 3 1 Δ ρ' δ')
    (heρ : ∀ j, ρ' (r j) = ρ j) (heδ : ∀ j, δ' (r j) = δ j)
    (heε : ∀ j, ε' (r j) = ε j) :
    (thirdSemantics Δ ρ' δ' ε' (ren r t)).1 = (thirdSemantics Γ ρ δ ε t).1 ∧
    (∀ s, BoundedTyping 3 Γ t (.srt s) →
      (thirdSemantics Δ ρ' δ' ε' (ren r t)).2 = (thirdSemantics Γ ρ δ ε t).2) := by
  induction t generalizing Γ T Δ r ρ ρ' δ δ' ε ε' with
  | var j =>
    have hv : (thirdSemantics Δ ρ' δ' ε' (ren r (.var j))).1 =
        (thirdSemantics Γ ρ δ ε (.var j)).1 := by
      change (ε' (r j)).force _ = (ε j).force _
      rw [heε j, ← show ren r (.var j) = .var (r j) from rfl,
        inferredThird_ren h hw hr hρ hρ' hδ hδ' heρ heδ]
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f v
    rw [thirdSemantics_decode (hs.rename hw hr) hs.var_below_top hρ' hδ',
      thirdSemantics_decode hs hs.var_below_top hρ hδ, hv,
      (middleSemantics_ren hs hw hr hρ hρ' heρ heδ).1]
    exact congrArg (fun k => thirdDecode (some s) k (middleSemantics Γ ρ δ (.var j)).1
      (thirdSemantics Γ ρ δ ε (.var j)).1 u f v)
      (congrArg ShapeValue.asArity (shapeEval_ren hs hw hr rfl heρ))
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    refine ⟨?_, fun _ _ => rfl⟩
    change (thirdSemantics Δ ρ' δ' ε' (.srt s)).1 = _
    rw [thirdSemantics_sort_value (ht.rename hw hr) hρ' hδ', thirdSemantics_sort_value ht hρ hδ,
      ← show ren r (.srt s) = .srt s from rfl,
      (middleSemantics_ren ht hw hr hρ hρ' heρ heδ).1]
    exact congrArg (fun k => thirdEncode (some s') k (middleSemantics Γ ρ δ (.srt s)).1
      (fun _ _ _ => Candidate.sn))
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
    have hdup (y : MiddleValue) : ∀ j, push y δ' (upRen r j) = push y δ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heδ j
    have hv : (thirdSemantics Δ ρ' δ' ε' (ren r (.app g a))).1 =
        (thirdSemantics Γ ρ δ ε (.app g a)).1 := by
      change (thirdSemantics Δ ρ' δ' ε' (.app (ren r g) (ren r a))).1 = _
      rw [thirdSemantics_app (hg.rename hw hr) (ha.rename hw hr) hρ' hδ',
        thirdSemantics_app hg ha hρ hδ,
        shapeEval_ren hg hw hr rfl heρ, shapeEval_ren ha hw hr rfl heρ,
        (middleSemantics_ren hg hw hr hρ hρ' heρ heδ).1,
        (middleSemantics_ren ha hw hr hρ hρ' heρ heδ).1,
        (ihg hg hw hr hρ hρ' hδ hδ' heρ heδ heε).1,
        (iha ha hw hr hρ hρ' hδ hδ' heρ heδ heε).1]
      apply thirdApply_congr (arityAt_ren _ _ _)
      · intro x hx; exact middleShape_ren hA hw hr rfl heρ
      · intro x hx z
        exact middleShape_ren hB (.cons hw (hA.rename hw hr)) (hr.up A) rfl (hup x)
      · intro x hx y hy
        exact congrFun (congrFun (thirdShape_ren hA hw hr hρ hρ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (thirdShape_ren hB (.cons hw (hA.rename hw hr)) (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (hup x) (hdup y)) z) w
    refine ⟨hv, ?_⟩
    intro s hs
    funext u f v
    rw [thirdSemantics_decode (hs.rename hw hr) hs.app_below_top hρ' hδ',
      thirdSemantics_decode hs hs.app_below_top hρ hδ, hv,
      (middleSemantics_ren hs hw hr hρ hρ' heρ heδ).1]
    exact congrArg (fun k => thirdDecode (some s) k (middleSemantics Γ ρ δ (.app g a)).1
      (thirdSemantics Γ ρ δ ε (.app g a)).1 u f v)
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
    have hdup (y : MiddleValue) : ∀ j, push y δ' (upRen r j) = push y δ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heδ j
    refine ⟨?_, ?_⟩
    · change (thirdSemantics Δ ρ' δ' ε' (.lam (ren r A) (ren (upRen r) b))).1 = _
      rw [thirdSemantics_lam (hPi.rename hw hr) (hb.rename (.cons hw hA') (hr.up A)) hρ' hδ',
        thirdSemantics_lam hPi hb hρ hδ,
        ← show ren r (.lam A b) = .lam (ren r A) (ren (upRen r) b) from rfl,
        shapeEval_ren (.lam hPi hb hs) hw hr rfl heρ,
        (middleSemantics_ren (.lam hPi hb hs) hw hr hρ hρ' heρ heδ).1]
      apply thirdLambda_congr (arityAt_ren _ _ _)
      · intro x hx; exact middleShape_ren hA hw hr rfl heρ
      · intro x hx z; exact middleShape_ren hB (.cons hw hA') (hr.up A) rfl (hup x)
      · intro x hx y hy
        exact congrFun (congrFun (thirdShape_ren hA hw hr hρ hρ' heρ heδ) x) y
      · intro x hx y hy z w
        exact congrFun (congrFun (thirdShape_ren hB (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (hup x) (hdup y)) z) w
      · intro x hx y hy z hz
        apply (ihb hb (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_ren hA hw hr rfl heρ)))
          (hδ'.up hA' rfl hy) (hup x) (hdup y) ?_).1
        intro j; cases j with
        | zero => rfl
        | succ j => exact heε j
    · intro s hsort
      obtain ⟨_, _, _, _, _, he⟩ := hsort.generation
      exact (not_conv_pi_srt he).elim
  | pi A B ihA ihB =>
    obtain ⟨sA, sB, s, hA, hB, hrule, hsA, hsB, hs, hc⟩ := h.generation
    have ht : BoundedTyping 3 Γ (.pi A B) (.srt s) := .pi hA hB hrule hsA hsB hs
    have hA' := hA.rename hw hr
    have hup (x : ShapeValue) : ∀ j, push x ρ' (upRen r j) = push x ρ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heρ j
    have hdup (y : MiddleValue) : ∀ j, push y δ' (upRen r j) = push y δ j := by
      intro j; cases j with
      | zero => rfl
      | succ j => exact heδ j
    have hm := middleSemantics_ren ht hw hr hρ hρ' heρ heδ
    have he : thirdSemantics Δ ρ' δ' ε' (ren r (.pi A B)) = thirdSemantics Γ ρ δ ε (.pi A B) := by
      apply thirdSemantics_pi_compare (ht.rename hw hr) ht hρ' hρ hδ' hδ
        (arityAt_ren _ _ _) (arityAt_ren (.type 1) r (.pi A B))
        (congrArg ShapeValue.asArity (shapeEval_ren ht hw hr rfl heρ)) (Prod.ext hm.1 (hm.2 s ht))
      · intro x hx; exact middleShape_ren hA hw hr rfl heρ
      · intro x hx z; exact middleShape_ren hB (.cons hw hA') (hr.up A) rfl (hup x)
      · intro x hx y hy
        exact congrFun (congrFun (thirdShape_ren hA hw hr hρ hρ' heρ heδ) x) y
      · intro x hx y hy
        exact thirdShape_ren hB (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx) (hup x) (hdup y)
      · intro x hx y hy z hz
        exact congrFun (congrFun (congrFun
          ((ihA hA hw hr hρ hρ' hδ hδ' heρ heδ heε).2 sA hA) x) y) z
      · intro x hx y hy z hz
        apply (ihB hB (.cons hw hA') (hr.up A)
          (hρ.up (hx.trans (arityAt_ren _ _ _))) (hρ'.up hx)
          (hδ.up hA rfl (hy.trans (middleShape_ren hA hw hr rfl heρ)))
          (hδ'.up hA' rfl hy) (hup x) (hdup y) ?_).2 sB hB
        intro j; cases j with
        | zero => rfl
        | succ j => exact heε j
    exact ⟨congrArg Prod.fst he, fun _ _ => congrArg Prod.snd he⟩

end Submission.Helpers
