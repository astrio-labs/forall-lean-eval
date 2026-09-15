import Submission.TopErasure

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem topErase_var (h : inferredArityAt n q Γ (.var i) ≠ .unit) :
    topErase n q Γ (.var i) = .var i := by rw [topErase, if_neg h]

theorem topErase_srt (n : Nat) (q : Srt) (Γ : List Tm) (s : Srt) :
    topErase n q Γ (.srt s) = erasedPoint := by
  simp only [topErase]; split <;> rfl

theorem topErase_pi (n : Nat) (q : Srt) (Γ : List Tm) (A B : Tm) :
    topErase n q Γ (.pi A B) = erasedPoint := by
  simp only [topErase]; split <;> rfl

theorem topErase_lam (h : inferredArityAt n q Γ (.lam A b) ≠ .unit) :
    topErase n q Γ (.lam A b) =
      .lam (arityType (arityAt q A)) (topErase n q (A :: Γ) b) := by
  rw [topErase, if_neg h]

theorem topErase_app (h : inferredArityAt n q Γ (.app f a) ≠ .unit) :
    topErase n q Γ (.app f a) = .app (topErase n q Γ f) (topErase n q Γ a) := by
  rw [topErase, if_neg h]

def upUse (P : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => P i

def UsesAt (P : Nat → Prop) : Tm → Prop
  | .var i => P i
  | .srt _ => True
  | .app f a => UsesAt P f ∧ UsesAt P a
  | .lam A b => UsesAt P A ∧ UsesAt (upUse P) b
  | .pi A B => UsesAt P A ∧ UsesAt (upUse P) B

theorem UsesAt.mono (h : UsesAt P t) (hp : ∀ i, P i → Q i) : UsesAt Q t := by
  have hup {P Q : Nat → Prop} (hp : ∀ i, P i → Q i) :
      ∀ i, upUse P i → upUse Q i := by
    intro i hi
    cases i with
    | zero => trivial
    | succ i => exact hp i hi
  induction t generalizing P Q with
  | var i => exact hp i h
  | srt => trivial
  | app f a ihf iha => exact ⟨ihf h.1 hp, iha h.2 hp⟩
  | lam A b ihA ihb => exact ⟨ihA h.1 hp, ihb h.2 (hup hp)⟩
  | pi A B ihA ihB => exact ⟨ihA h.1 hp, ihB h.2 (hup hp)⟩

theorem UsesAt.sub_eq (h : UsesAt P t) (he : ∀ i, P i → σ i = τ i) :
    sub σ t = sub τ t := by
  have hup {P : Nat → Prop} {σ τ : Nat → Tm} (he : ∀ i, P i → σ i = τ i) :
      ∀ i, upUse P i → upSub σ i = upSub τ i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg (ren Nat.succ) (he i hi)
  induction t generalizing P σ τ with
  | var i => exact he i h
  | srt => rfl
  | app f a ihf iha => simp only [sub, ihf h.1 he, iha h.2 he]
  | lam A b ihA ihb => simp only [sub, ihA h.1 he, ihb h.2 (hup he)]
  | pi A B ihA ihB => simp only [sub, ihA h.1 he, ihB h.2 (hup he)]

theorem arityType_uses (P : Nat → Prop) (A : Arity) : UsesAt P (arityType A) := by
  induction A generalizing P with
  | unit => trivial
  | prop => trivial
  | fn A B ihA ihB => exact ⟨ihA _, ihB _⟩

theorem erasedPoint_uses (P : Nat → Prop) : UsesAt P erasedPoint :=
  ⟨True.intro, True.intro⟩

def erasureSupport (q : Srt) (Γ : List Tm) (i : Nat) : Prop :=
  ∃ A, Γ[i]? = some A ∧ arityAt q A ≠ .unit

theorem topErase_uses (h : BoundedTyping n Γ t A) (hq : sortRank q + 1 = n) :
    UsesAt (erasureSupport q Γ) (topErase n q Γ t) := by
  induction t generalizing Γ A with
  | var i =>
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [topErase_unit he]; exact erasedPoint_uses _
    · obtain ⟨B, hi, hc⟩ := h.generation
      rw [topErase_var he]
      exact ⟨B, hi, fun hb => he ((inferredArityAt_var h.wf hi hq).trans hb)⟩
  | srt s => rw [topErase_srt]; exact erasedPoint_uses _
  | pi C D ihC ihD => rw [topErase_pi]; exact erasedPoint_uses _
  | app f a ihf iha =>
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [topErase_unit he]; exact erasedPoint_uses _
    · obtain ⟨C, B, hf, ha, hc⟩ := h.generation
      rw [topErase_app he]
      exact ⟨ihf hf, iha ha⟩
  | lam C b ihC ihb =>
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [topErase_unit he]; exact erasedPoint_uses _
    · obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
      rw [topErase_lam he]
      refine ⟨arityType_uses _ _, (ihb hb).mono ?_⟩
      intro i hi
      cases i with
      | zero => trivial
      | succ i => exact hi

theorem topErase_ren (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hr : RenCtx Γ Δ r) (hq : sortRank q + 1 = n) :
    topErase n q Δ (ren r t) = ren r (topErase n q Γ t) := by
  induction t generalizing Γ A Δ r with
  | var i =>
    have hi := inferredArityAt_ren h hw hr hq
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [topErase_unit (hi.trans he), topErase_unit he, erasedPoint_ren]
    · rw [topErase_var he, ren,
        topErase_var (fun hc => he (hi.symm.trans hc))]
  | srt s => simp only [ren, topErase_srt, erasedPoint_ren]
  | pi C D ihC ihD => simp only [ren, topErase_pi, erasedPoint_ren]
  | app f a ihf iha =>
    have hi := inferredArityAt_ren h hw hr hq
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [topErase_unit (hi.trans he), topErase_unit he, erasedPoint_ren]
    · obtain ⟨C, B, hf, ha, hc⟩ := h.generation
      simp only [ren] at hi ⊢
      rw [topErase_app (fun hc => he (hi.symm.trans hc)), topErase_app he, ren,
        ihf hf hw hr, iha ha hw hr]
  | lam C b ihC ihb =>
    have hi := inferredArityAt_ren h hw hr hq
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [topErase_unit (hi.trans he), topErase_unit he, erasedPoint_ren]
    · obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
      obtain ⟨sC, hC, _⟩ := hPi.pi_domain
      have hC' := hC.rename hw hr
      simp only [ren] at hi ⊢
      rw [topErase_lam (fun hc => he (hi.symm.trans hc)), topErase_lam he, ren,
        arityAt_ren, arityType_ren, ihb hb (.cons hw hC') (hr.up C)]

theorem erasedSub_up (hw : BoundedWf n Δ) (hσ : BoundedSubCtx n Γ Δ σ)
    (hC : BoundedTyping n Γ C (.srt s)) (hk : ∀ i, kindAt q (σ i) = false)
    (hq : sortRank q + 1 = n) (hi : erasureSupport q (C :: Γ) i) :
    topErase n q (sub σ C :: Δ) (upSub σ i) =
      upSub (fun j => topErase n q Δ (σ j)) i := by
  have hC' := hC.substitute hw hσ
  cases i with
  | zero =>
    obtain ⟨D, hi, hne⟩ := hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst D
    change topErase n q (sub σ C :: Δ) (.var 0) = .var 0
    apply topErase_var
    rw [inferredArityAt_var (.cons hw hC') (i := 0) rfl hq, arityAt_sub hk]
    exact hne
  | succ i =>
    obtain ⟨D, hi, hne⟩ := hi
    exact topErase_ren (hσ i D hi) (.cons hw hC') (.weaken Δ (sub σ C)) hq

theorem topErase_substitute (h : BoundedTyping n Γ t A) (hw : BoundedWf n Δ)
    (hσ : BoundedSubCtx n Γ Δ σ) (hk : ∀ i, kindAt q (σ i) = false)
    (hq : sortRank q + 1 = n) :
    topErase n q Δ (sub σ t) = sub (fun i => topErase n q Δ (σ i)) (topErase n q Γ t) := by
  have hup {σ : Nat → Tm} (hk : ∀ i, kindAt q (σ i) = false) :
      ∀ i, kindAt q (upSub σ i) = false := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (kindAt_ren _ _ _).trans (hk i)
  induction t generalizing Γ A Δ σ with
  | var i =>
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [topErase_unit ((inferredArityAt_substitute h hw hσ hk hq).trans he),
        topErase_unit he, erasedPoint_sub]
    · rw [topErase_var he]; rfl
  | srt s => simp only [sub, topErase_srt, erasedPoint_sub]
  | pi C D ihC ihD => simp only [sub, topErase_pi, erasedPoint_sub]
  | app f a ihf iha =>
    have hi := inferredArityAt_substitute h hw hσ hk hq
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [topErase_unit (hi.trans he), topErase_unit he, erasedPoint_sub]
    · obtain ⟨C, B, hf, ha, hc⟩ := h.generation
      simp only [sub] at hi ⊢
      rw [topErase_app (fun hc => he (hi.symm.trans hc)), topErase_app he, sub,
        ihf hf hw hσ hk, iha ha hw hσ hk]
  | lam C b ihC ihb =>
    have hi := inferredArityAt_substitute h hw hσ hk hq
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [topErase_unit (hi.trans he), topErase_unit he, erasedPoint_sub]
    · obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
      obtain ⟨sC, hC, _⟩ := hPi.pi_domain
      have hC' := hC.substitute hw hσ
      simp only [sub] at hi ⊢
      rw [topErase_lam (fun hc => he (hi.symm.trans hc)), topErase_lam he, sub,
        arityAt_sub hk, arityType_sub,
        ihb hb (.cons hw hC') (hσ.up hw hC') (hup hk)]
      congr 1
      exact (topErase_uses hb hq).sub_eq (fun i hi => erasedSub_up hw hσ hC hk hq hi)

theorem topErase_subst (hb : BoundedTyping n (A :: Γ) b B)
    (ha : BoundedTyping n Γ a A) (hA : BoundedTyping n Γ A (.srt s))
    (hq : sortRank q + 1 = n) :
    topErase n q Γ (subst 0 a b) =
      subst 0 (topErase n q Γ a) (topErase n q (A :: Γ) b) := by
  have hk : ∀ i, kindAt q (single a i) = false := by
    intro i
    cases i with
    | zero => exact ha.not_kindAt hA hq
    | succ => rfl
  rw [subst_eq_sub, topErase_substitute hb ha.wf (.single ha) hk hq, subst_eq_sub]
  apply (topErase_uses hb hq).sub_eq
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    obtain ⟨D, hi, hne⟩ := hi
    change topErase n q Γ (.var i) = .var i
    apply topErase_var
    rw [inferredArityAt_var ha.wf hi hq]
    exact hne

theorem topErase_beta (hPi : BoundedTyping n Γ (.pi A B) (.srt s))
    (hb : BoundedTyping n (A :: Γ) b B) (ha : BoundedTyping n Γ a A)
    (hq : sortRank q + 1 = n) (hne : arityAt q B ≠ .unit) :
    Step (topErase n q Γ (.app (.lam A b) a)) (topErase n q Γ (subst 0 a b)) := by
  have hf : BoundedTyping n Γ (.lam A b) (.pi A B) := .lam hPi hb hPi.sort_bound
  have hfn : inferredArityAt n q Γ (.lam A b) ≠ .unit := by
    rw [inferredArityAt_eq hf hq, arityAt]
    intro he
    exact hne ((Arity.arrow_unit_iff _ _).1 he)
  have happ : inferredArityAt n q Γ (.app (.lam A b) a) ≠ .unit := by
    rw [inferredArityAt_app hf ha hq, inferredArityAt_eq hf hq,
      arityAt, Arity.codomain_arrow]
    exact hne
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  rw [topErase_app happ, topErase_lam hfn, topErase_subst hb ha hA hq]
  exact .beta _ _ _

end Submission.Helpers
