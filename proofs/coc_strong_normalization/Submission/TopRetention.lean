import Submission.TopSubstitution

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A typed constant function keeps both arguments in the translated syntax. -/
def retain (X Y : Arity) (a t : Tm) : Tm :=
  .app (.app (.lam (arityType Y) (.lam (arityType X) (.var 1))) t) a

theorem retain_ren (r : Nat → Nat) (X Y : Arity) (a t : Tm) :
    ren r (retain X Y a t) = retain X Y (ren r a) (ren r t) := by
  simp only [retain, ren, arityType_ren, upRen]

theorem retain_sub (σ : Nat → Tm) (X Y : Arity) (a t : Tm) :
    sub σ (retain X Y a t) = retain X Y (sub σ a) (sub σ t) := by
  simp only [retain, sub, arityType_sub, upSub, ren]

theorem retain_uses (ha : UsesAt P a) (ht : UsesAt P t) :
    UsesAt P (retain X Y a t) :=
  ⟨⟨⟨arityType_uses _ _, arityType_uses _ _, True.intro⟩, ht⟩, ha⟩

theorem retain_typing (ha : BoundedTyping 1 Γ a (arityType X))
    (ht : BoundedTyping 1 Γ t (arityType Y)) :
    BoundedTyping 1 Γ (retain X Y a t) (arityType Y) := by
  have hw := ha.wf
  have hY := arityType_typing hw Y
  have hwY := BoundedWf.cons hw hY
  have hX := arityType_typing hwY X
  have hwYX := BoundedWf.cons hwY hX
  have hv : BoundedTyping 1 (arityType X :: arityType Y :: Γ) (.var 1) (arityType Y) := by
    have h := BoundedTyping.var (i := 1) (A := arityType Y) hwYX rfl
    simpa only [← ren_shift, arityType_ren] using h
  have hpXY := arityType_typing hwY (.fn X Y)
  have hlX := BoundedTyping.lam hpXY hv (by decide : sortRank (.type 0) ≤ 1)
  have hpYXY := arityType_typing hw (.fn Y (.fn X Y))
  have hlY := BoundedTyping.lam hpYXY hlX (by decide : sortRank (.type 0) ≤ 1)
  have h₁ := BoundedTyping.app hlY ht
  have h₁' : BoundedTyping 1 Γ
      (.app (.lam (arityType Y) (.lam (arityType X) (.var 1))) t)
      (arityType (.fn X Y)) := by
    simpa only [subst_eq_sub, arityType, sub, arityType_sub] using h₁
  have h₂ := BoundedTyping.app h₁' ha
  simpa only [retain, subst_eq_sub, arityType_sub] using h₂

/-- The retained argument is discarded after two beta steps. -/
theorem retain_steps (X Y : Arity) (a t : Tm) : Steps (retain X Y a t) t := by
  have h₁ : Step (retain X Y a t)
      (.app (.lam (arityType X) (ren Nat.succ t)) a) := by
    have h := Step.appFun a (Step.beta (arityType Y) (.lam (arityType X) (.var 1)) t)
    simpa only [retain, subst_eq_sub, sub, arityType_sub, upSub, single] using h
  have h₂ : Step (.app (.lam (arityType X) (ren Nat.succ t)) a) t := by
    have h := Step.beta (arityType X) (ren Nat.succ t) a
    simpa only [subst_eq_sub, single_ren_succ] using h
  exact .head h₁ (.head h₂ (.refl _))

/-- Retain annotations and products, while replacing singleton computations by a point. -/
noncomputable def richErase (n : Nat) (q : Srt) (Γ : List Tm) (t : Tm) : Tm :=
  if inferredArityAt n q Γ t = .unit then erasedPoint else
  match t with
  | .var i => .var i
  | .srt _ => erasedPoint
  | .app f a => .app (richErase n q Γ f) (richErase n q Γ a)
  | .lam A b => retain .prop (inferredArityAt n q Γ t) (richErase n q Γ A)
      (.lam (arityType (arityAt q A)) (richErase n q (A :: Γ) b))
  | .pi A B => retain .prop .prop (richErase n q Γ A)
      (retain (.fn (arityAt q A) .prop) .prop
        (.lam (arityType (arityAt q A)) (richErase n q (A :: Γ) B)) erasedPoint)
termination_by structural t

theorem richErase_unit (h : inferredArityAt n q Γ t = .unit) :
    richErase n q Γ t = erasedPoint := by
  cases t <;> simp only [richErase, h, ↓reduceIte]

theorem richErase_var (h : inferredArityAt n q Γ (.var i) ≠ .unit) :
    richErase n q Γ (.var i) = .var i := by rw [richErase, if_neg h]

theorem richErase_srt (n : Nat) (q : Srt) (Γ : List Tm) (s : Srt) :
    richErase n q Γ (.srt s) = erasedPoint := by
  simp only [richErase]; split <;> rfl

theorem richErase_app (h : inferredArityAt n q Γ (.app f a) ≠ .unit) :
    richErase n q Γ (.app f a) = .app (richErase n q Γ f) (richErase n q Γ a) := by
  rw [richErase, if_neg h]

theorem richErase_lam (h : inferredArityAt n q Γ (.lam A b) ≠ .unit) :
    richErase n q Γ (.lam A b) =
      retain .prop (inferredArityAt n q Γ (.lam A b)) (richErase n q Γ A)
        (.lam (arityType (arityAt q A)) (richErase n q (A :: Γ) b)) := by
  rw [richErase, if_neg h]

theorem richErase_pi (h : inferredArityAt n q Γ (.pi A B) ≠ .unit) :
    richErase n q Γ (.pi A B) = retain .prop .prop (richErase n q Γ A)
      (retain (.fn (arityAt q A) .prop) .prop
        (.lam (arityType (arityAt q A)) (richErase n q (A :: Γ) B)) erasedPoint) := by
  rw [richErase, if_neg h]

theorem richErase_typing (h : BoundedTyping n Γ t A) (hq : sortRank q + 1 = n) :
    BoundedTyping 1 (arityContext q Γ) (richErase n q Γ t)
      (arityType (inferredArityAt n q Γ t)) := by
  induction t generalizing Γ A with
  | var i =>
    obtain ⟨B, hi, hc⟩ := h.generation
    have hi' : (arityContext q Γ)[i]? = some (arityType (arityAt q B)) := by
      simp only [arityContext, List.getElem?_map, hi, Option.map_some]
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [richErase_unit he, he]
      exact erasedPoint_typing (arityContext_wf q Γ)
    · rw [richErase_var he, inferredArityAt_var h.wf hi hq]
      have hv := BoundedTyping.var (arityContext_wf q Γ) hi'
      simpa only [← ren_shift, arityType_ren] using hv
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping n Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    rw [richErase_srt, inferredArityAt_eq ht hq, arityType_sort]
    exact erasedPoint_typing (arityContext_wf q Γ)
  | pi C D ihC ihD =>
    obtain ⟨s₁, s₂, s₃, hC, hD, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have ht : BoundedTyping n Γ (.pi C D) (.srt s₃) := .pi hC hD hr hs₁ hs₂ hs₃
    by_cases he : inferredArityAt n q Γ (.pi C D) = .unit
    · rw [richErase_unit he, he]
      exact erasedPoint_typing (arityContext_wf q Γ)
    · rw [richErase_pi he, inferredArityAt_eq ht hq, arityType_sort]
      have hEC := ihC hC
      have hED := ihD hD
      rw [inferredArityAt_eq hC hq, arityType_sort] at hEC
      rw [inferredArityAt_eq hD hq, arityType_sort] at hED
      apply retain_typing (X := .prop) (Y := .prop) hEC
      have hp := arityType_typing (arityContext_wf q Γ) (.fn (arityAt q C) .prop)
      have hl := BoundedTyping.lam hp hED (by decide : sortRank (.type 0) ≤ 1)
      exact retain_typing hl (erasedPoint_typing (arityContext_wf q Γ))
  | lam C b ihC ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [richErase_unit he, he]
      exact erasedPoint_typing (arityContext_wf q Γ)
    · have hbe : inferredArityAt n q (C :: Γ) b ≠ .unit := by
        intro hbe
        apply he
        rw [inferredArityAt_lam hPi hb hq, hbe]
        rfl
      rw [richErase_lam he]
      obtain ⟨sC, hC, _⟩ := hPi.pi_domain
      have hEC := ihC hC
      rw [inferredArityAt_eq hC hq, arityType_sort] at hEC
      apply retain_typing (X := .prop) hEC
      rw [inferredArityAt_lam hPi hb hq, Arity.arrow_eq_fn hbe]
      have hp := arityType_typing (arityContext_wf q Γ)
        (.fn (arityAt q C) (inferredArityAt n q (C :: Γ) b))
      exact .lam hp (ihb hb) (by decide)
  | app f a ihf iha =>
    obtain ⟨C, B, hf, ha, hc⟩ := h.generation
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [richErase_unit he, he]
      exact erasedPoint_typing (arityContext_wf q Γ)
    · have heq : inferredArityAt n q Γ (.app f a) = arityAt q B := by
        rw [inferredArityAt_app hf ha hq, inferredArityAt_eq hf hq,
          arityAt, Arity.codomain_arrow]
      have hne : arityAt q B ≠ .unit := fun hb => he (heq.trans hb)
      have hf' := ihf hf
      rw [inferredArityAt_eq hf hq, arityAt, Arity.arrow_eq_fn hne] at hf'
      have ha' := iha ha
      rw [inferredArityAt_eq ha hq] at ha'
      have happ := BoundedTyping.app hf' ha'
      rw [richErase_app he, heq]
      simpa only [subst_eq_sub, arityType_sub] using happ

theorem richErase_normalization (h : BoundedTyping n Γ t A)
    (hq : sortRank q + 1 = n) : SN (richErase n q Γ t) :=
  two_sort_normalization (richErase_typing h hq)

end Submission.Helpers
