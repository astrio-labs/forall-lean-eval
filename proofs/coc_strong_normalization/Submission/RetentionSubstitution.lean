import Submission.TopRetention

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem richErase_uses (h : BoundedTyping n Γ t A) (hq : sortRank q + 1 = n) :
    UsesAt (erasureSupport q Γ) (richErase n q Γ t) := by
  induction t generalizing Γ A with
  | var i =>
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [richErase_unit he]; exact erasedPoint_uses _
    · obtain ⟨B, hi, hc⟩ := h.generation
      rw [richErase_var he]
      exact ⟨B, hi, fun hb => he ((inferredArityAt_var h.wf hi hq).trans hb)⟩
  | srt s => rw [richErase_srt]; exact erasedPoint_uses _
  | app f a ihf iha =>
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [richErase_unit he]; exact erasedPoint_uses _
    · obtain ⟨C, B, hf, ha, hc⟩ := h.generation
      rw [richErase_app he]
      exact ⟨ihf hf, iha ha⟩
  | lam C b ihC ihb =>
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [richErase_unit he]; exact erasedPoint_uses _
    · obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
      obtain ⟨sC, hC, _⟩ := hPi.pi_domain
      rw [richErase_lam he]
      apply retain_uses (ihC hC)
      refine ⟨arityType_uses _ _, (ihb hb).mono ?_⟩
      intro i hi
      cases i with
      | zero => trivial
      | succ i => exact hi
  | pi C D ihC ihD =>
    by_cases he : inferredArityAt n q Γ (.pi C D) = .unit
    · rw [richErase_unit he]; exact erasedPoint_uses _
    · obtain ⟨s₁, s₂, s₃, hC, hD, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
      rw [richErase_pi he]
      apply retain_uses (ihC hC)
      apply retain_uses ?_ (erasedPoint_uses _)
      refine ⟨arityType_uses _ _, (ihD hD).mono ?_⟩
      intro i hi
      cases i with
      | zero => trivial
      | succ i => exact hi

theorem richErase_ren (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hr : RenCtx Γ Δ r) (hq : sortRank q + 1 = n) :
    richErase n q Δ (ren r t) = ren r (richErase n q Γ t) := by
  induction t generalizing Γ A Δ r with
  | var i =>
    have hi := inferredArityAt_ren h hw hr hq
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [richErase_unit (hi.trans he), richErase_unit he, erasedPoint_ren]
    · rw [richErase_var he, ren,
        richErase_var (fun hc => he (hi.symm.trans hc))]
  | srt s => simp only [ren, richErase_srt, erasedPoint_ren]
  | app f a ihf iha =>
    have hi := inferredArityAt_ren h hw hr hq
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [richErase_unit (hi.trans he), richErase_unit he, erasedPoint_ren]
    · obtain ⟨C, B, hf, ha, hc⟩ := h.generation
      simp only [ren] at hi ⊢
      rw [richErase_app (fun hc => he (hi.symm.trans hc)), richErase_app he, ren,
        ihf hf hw hr, iha ha hw hr]
  | lam C b ihC ihb =>
    have hi := inferredArityAt_ren h hw hr hq
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [richErase_unit (hi.trans he), richErase_unit he, erasedPoint_ren]
    · obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
      obtain ⟨sC, hC, _⟩ := hPi.pi_domain
      have hC' := hC.rename hw hr
      simp only [ren] at hi ⊢
      rw [richErase_lam (fun hc => he (hi.symm.trans hc)), richErase_lam he,
        retain_ren, ren, hi, ihC hC hw hr, arityAt_ren, arityType_ren,
        ihb hb (.cons hw hC') (hr.up C)]
  | pi C D ihC ihD =>
    have hi := inferredArityAt_ren h hw hr hq
    by_cases he : inferredArityAt n q Γ (.pi C D) = .unit
    · rw [richErase_unit (hi.trans he), richErase_unit he, erasedPoint_ren]
    · obtain ⟨s₁, s₂, s₃, hC, hD, hrule, hs₁, hs₂, hs₃, hc⟩ := h.generation
      have hC' := hC.rename hw hr
      simp only [ren] at hi ⊢
      rw [richErase_pi (fun hc => he (hi.symm.trans hc)), richErase_pi he,
        retain_ren, retain_ren, ren, ihC hC hw hr, arityAt_ren, arityType_ren,
        erasedPoint_ren, ihD hD (.cons hw hC') (hr.up C)]

theorem retainedSub_up (hw : BoundedWf n Δ) (hσ : BoundedSubCtx n Γ Δ σ)
    (hC : BoundedTyping n Γ C (.srt s)) (hk : ∀ i, kindAt q (σ i) = false)
    (hq : sortRank q + 1 = n) (hi : erasureSupport q (C :: Γ) i) :
    richErase n q (sub σ C :: Δ) (upSub σ i) =
      upSub (fun j => richErase n q Δ (σ j)) i := by
  have hC' := hC.substitute hw hσ
  cases i with
  | zero =>
    obtain ⟨D, hi, hne⟩ := hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst D
    change richErase n q (sub σ C :: Δ) (.var 0) = .var 0
    apply richErase_var
    rw [inferredArityAt_var (.cons hw hC') (i := 0) rfl hq, arityAt_sub hk]
    exact hne
  | succ i =>
    obtain ⟨D, hi, hne⟩ := hi
    exact richErase_ren (hσ i D hi) (.cons hw hC') (.weaken Δ (sub σ C)) hq

theorem richErase_substitute (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ σ) (hk : ∀ i, kindAt q (σ i) = false)
    (hq : sortRank q + 1 = n) :
    richErase n q Δ (sub σ t) = sub (fun i => richErase n q Δ (σ i)) (richErase n q Γ t) := by
  have hup {σ : Nat → Tm} (hk : ∀ i, kindAt q (σ i) = false) :
      ∀ i, kindAt q (upSub σ i) = false := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (kindAt_ren _ _ _).trans (hk i)
  induction t generalizing Γ A Δ σ with
  | var i =>
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [richErase_unit ((inferredArityAt_substitute h hw hσ hk hq).trans he),
        richErase_unit he, erasedPoint_sub]
    · rw [richErase_var he]; rfl
  | srt s => simp only [sub, richErase_srt, erasedPoint_sub]
  | app f a ihf iha =>
    have hi := inferredArityAt_substitute h hw hσ hk hq
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [richErase_unit (hi.trans he), richErase_unit he, erasedPoint_sub]
    · obtain ⟨C, B, hf, ha, hc⟩ := h.generation
      simp only [sub] at hi ⊢
      rw [richErase_app (fun hc => he (hi.symm.trans hc)), richErase_app he, sub,
        ihf hf hw hσ hk, iha ha hw hσ hk]
  | lam C b ihC ihb =>
    have hi := inferredArityAt_substitute h hw hσ hk hq
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [richErase_unit (hi.trans he), richErase_unit he, erasedPoint_sub]
    · obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
      obtain ⟨sC, hC, _⟩ := hPi.pi_domain
      have hC' := hC.substitute hw hσ
      simp only [sub] at hi ⊢
      rw [richErase_lam (fun hc => he (hi.symm.trans hc)), richErase_lam he,
        retain_sub, sub, hi, ihC hC hw hσ hk, arityAt_sub hk, arityType_sub,
        ihb hb (.cons hw hC') (hσ.up hw hC') (hup hk)]
      congr 2
      exact (richErase_uses hb hq).sub_eq (fun i hi => retainedSub_up hw hσ hC hk hq hi)
  | pi C D ihC ihD =>
    have hi := inferredArityAt_substitute h hw hσ hk hq
    by_cases he : inferredArityAt n q Γ (.pi C D) = .unit
    · rw [richErase_unit (hi.trans he), richErase_unit he, erasedPoint_sub]
    · obtain ⟨s₁, s₂, s₃, hC, hD, hrule, hs₁, hs₂, hs₃, hc⟩ := h.generation
      have hC' := hC.substitute hw hσ
      simp only [sub] at hi ⊢
      rw [richErase_pi (fun hc => he (hi.symm.trans hc)), richErase_pi he,
        retain_sub, retain_sub, sub, ihC hC hw hσ hk, arityAt_sub hk, arityType_sub,
        erasedPoint_sub, ihD hD (.cons hw hC') (hσ.up hw hC') (hup hk)]
      congr 3
      exact (richErase_uses hD hq).sub_eq (fun i hi => retainedSub_up hw hσ hC hk hq hi)

theorem richErase_subst (hb : BoundedTyping n (A :: Γ) b B)
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt s))
    (hq : sortRank q + 1 = n) :
    richErase n q Γ (subst 0 a b) =
      subst 0 (richErase n q Γ a) (richErase n q (A :: Γ) b) := by
  have hk : ∀ i, kindAt q (single a i) = false := by
    intro i
    cases i with
    | zero => exact ha.not_kindAt hA hq
    | succ => rfl
  rw [subst_eq_sub, richErase_substitute hb ha.wf (.single ha) hk hq, subst_eq_sub]
  apply (richErase_uses hb hq).sub_eq
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    obtain ⟨D, hi, hne⟩ := hi
    change richErase n q Γ (.var i) = .var i
    apply richErase_var
    rw [inferredArityAt_var ha.wf hi hq]
    exact hne

/-- Erasure is independent of a change to convertible context declarations. -/
theorem richErase_context (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ Tm.var) (hq : sortRank q + 1 = n) :
    richErase n q Δ t = richErase n q Γ t := by
  have hk : ∀ i, kindAt q (Tm.var i) = false := fun _ => rfl
  have he := richErase_substitute h hw hσ hk hq
  rw [sub_var] at he
  rw [he]
  calc
    sub (fun i => richErase n q Δ (.var i)) (richErase n q Γ t) =
        sub Tm.var (richErase n q Γ t) := by
      apply (richErase_uses h hq).sub_eq
      intro i hi
      obtain ⟨B, hi, hne⟩ := hi
      apply richErase_var
      rw [inferredArityAt_eq (hσ i B hi) hq, sub_var, ← ren_shift, arityAt_ren]
      exact hne
    _ = _ := sub_var _

theorem BoundedSubCtx.context_conversion (hA : BoundedTyping n Γ A (.srt s))
    (hA' : BoundedTyping n Γ A' (.srt s')) (hs : sortRank s ≤ n) (hc : Conv A A') :
    BoundedSubCtx n (A :: Γ) (A' :: Γ) Tm.var := by
  intro i C hi
  rw [sub_var]
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst C
    simp only [Nat.zero_add, lift_one]
    apply BoundedTyping.conv (BoundedTyping.var (i := 0) (.cons hA'.wf hA') rfl)
      (hA.weaken hA') ?_ hs
    simpa only [Nat.zero_add, lift_one] using conv_ren (conv_symm hc) Nat.succ
  | succ i => exact .var (.cons hA'.wf hA') hi

theorem richErase_context_conversion (hb : BoundedTyping n (A :: Γ) b B)
    (hA : BoundedTyping n Γ A (.srt s)) (hA' : BoundedTyping n Γ A' (.srt s'))
    (hs : sortRank s ≤ n) (hc : Conv A A') (hq : sortRank q + 1 = n) :
    richErase n q (A' :: Γ) b = richErase n q (A :: Γ) b :=
  richErase_context hb (.cons hA'.wf hA')
    (BoundedSubCtx.context_conversion hA hA' hs hc) hq

end Submission.Helpers
