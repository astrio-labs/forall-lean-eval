import Submission.TopArity
import Submission.TwoSortNormalization

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def arityType : Arity → Tm
  | .unit | .prop => .srt .prop
  | .fn A B => .pi (arityType A) (arityType B)

theorem arityType_ren (r : Nat → Nat) (A : Arity) :
    ren r (arityType A) = arityType A := by
  induction A generalizing r with
  | unit => rfl
  | prop => rfl
  | fn A B ihA ihB => simp only [arityType, ren, ihA, ihB]

theorem arityType_sub (σ : Nat → Tm) (A : Arity) :
    sub σ (arityType A) = arityType A := by
  induction A generalizing σ with
  | unit => rfl
  | prop => rfl
  | fn A B ihA ihB => simp only [arityType, sub, ihA, ihB]

theorem arityType_sort (q s : Srt) : arityType (arityAt q (.srt s)) = .srt .prop := by
  by_cases h : s = q <;> simp [arityAt, arityType, h]

theorem Arity.arrow_eq_fn {A B : Arity} (h : B ≠ .unit) : A.arrow B = .fn A B := by
  cases B with
  | unit => exact (h rfl).elim
  | prop => rfl
  | fn => rfl

theorem arityType_typing (hw : BoundedWf 1 Γ) (A : Arity) :
    BoundedTyping 1 Γ (arityType A) (.srt (.type 0)) := by
  induction A generalizing Γ with
  | unit => exact .srt hw .prop (by decide) (by decide)
  | prop => exact .srt hw .prop (by decide) (by decide)
  | fn A B ihA ihB =>
    have hA := ihA hw
    exact .pi hA (ihB (.cons hw hA)) (.type 0 0) (by decide) (by decide) (by decide)

def arityContext (q : Srt) (Γ : List Tm) : List Tm :=
  Γ.map (fun A => arityType (arityAt q A))

theorem arityContext_wf (q : Srt) (Γ : List Tm) : BoundedWf 1 (arityContext q Γ) := by
  induction Γ with
  | nil => exact .nil
  | cons A Γ ih => exact .cons ih (arityType_typing ih _)

/-- A closed proposition used for computations with the singleton arity. -/
def erasedPoint : Tm := .pi (.srt .prop) (.var 0)

theorem erasedPoint_ren (r : Nat → Nat) : ren r erasedPoint = erasedPoint := rfl

theorem erasedPoint_sub (σ : Nat → Tm) : sub σ erasedPoint = erasedPoint := rfl

theorem erasedPoint_typing (hw : BoundedWf 1 Γ) :
    BoundedTyping 1 Γ erasedPoint (.srt .prop) := by
  have hP : BoundedTyping 1 Γ (.srt .prop) (.srt (.type 0)) :=
    .srt hw .prop (by decide) (by decide)
  have hv : BoundedTyping 1 (.srt .prop :: Γ) (.var 0) (.srt .prop) :=
    .var (i := 0) (A := .srt .prop) (.cons hw hP) rfl
  exact .pi hP hv (.prop (.type 0)) (by decide) (by decide) (by decide)

/-- Erase singleton computations and retain the higher function applications. -/
noncomputable def topErase (n : Nat) (q : Srt) (Γ : List Tm) (t : Tm) : Tm :=
  if inferredArityAt n q Γ t = .unit then erasedPoint else
  match t with
  | .var i => .var i
  | .srt _ | .pi _ _ => erasedPoint
  | .app f a => .app (topErase n q Γ f) (topErase n q Γ a)
  | .lam A b => .lam (arityType (arityAt q A)) (topErase n q (A :: Γ) b)
termination_by structural t

theorem topErase_unit (h : inferredArityAt n q Γ t = .unit) :
    topErase n q Γ t = erasedPoint := by
  cases t <;> simp only [topErase, h, ↓reduceIte]

theorem topErase_typing (h : BoundedTyping n Γ t A) (hq : sortRank q + 1 = n) :
    BoundedTyping 1 (arityContext q Γ) (topErase n q Γ t)
      (arityType (inferredArityAt n q Γ t)) := by
  induction t generalizing Γ A with
  | var i =>
    obtain ⟨B, hi, hc⟩ := h.generation
    have hi' : (arityContext q Γ)[i]? = some (arityType (arityAt q B)) := by
      simp only [arityContext, List.getElem?_map, hi, Option.map_some]
    by_cases he : inferredArityAt n q Γ (.var i) = .unit
    · rw [topErase_unit he, he]
      exact erasedPoint_typing (arityContext_wf q Γ)
    · rw [topErase, if_neg he, inferredArityAt_var h.wf hi hq]
      have hv := BoundedTyping.var (arityContext_wf q Γ) hi'
      simpa only [← ren_shift, arityType_ren] using hv
  | srt s =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have ht : BoundedTyping n Γ (.srt s) (.srt s') := .srt h.wf ha hs hs'
    have he : topErase n q Γ (.srt s) = erasedPoint := by
      simp only [topErase]; split <;> rfl
    rw [he, inferredArityAt_eq ht hq, arityType_sort]
    exact erasedPoint_typing (arityContext_wf q Γ)
  | pi C D ihC ihD =>
    obtain ⟨s₁, s₂, s₃, hC, hD, hr, hs₁, hs₂, hs₃, hc⟩ := h.generation
    have ht : BoundedTyping n Γ (.pi C D) (.srt s₃) :=
      .pi hC hD hr hs₁ hs₂ hs₃
    have he : topErase n q Γ (.pi C D) = erasedPoint := by
      simp only [topErase]; split <;> rfl
    rw [he, inferredArityAt_eq ht hq, arityType_sort]
    exact erasedPoint_typing (arityContext_wf q Γ)
  | lam C b ihC ihb =>
    obtain ⟨B, s, hPi, hb, hs, hc⟩ := h.generation
    by_cases he : inferredArityAt n q Γ (.lam C b) = .unit
    · rw [topErase_unit he, he]
      exact erasedPoint_typing (arityContext_wf q Γ)
    · have hbe : inferredArityAt n q (C :: Γ) b ≠ .unit := by
        intro hbe
        apply he
        rw [inferredArityAt_lam hPi hb hq, hbe]
        rfl
      rw [topErase, if_neg he, inferredArityAt_lam hPi hb hq,
        Arity.arrow_eq_fn hbe]
      have hw := arityContext_wf q Γ
      have hC := arityType_typing hw (arityAt q C)
      have hB := arityType_typing (.cons hw hC) (inferredArityAt n q (C :: Γ) b)
      exact .lam (.pi hC hB (.type 0 0) (by decide) (by decide) (by decide))
        (ihb hb) (by decide)
  | app f a ihf iha =>
    obtain ⟨C, B, hf, ha, hc⟩ := h.generation
    by_cases he : inferredArityAt n q Γ (.app f a) = .unit
    · rw [topErase_unit he, he]
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
      rw [topErase, if_neg he, heq]
      simpa only [subst_eq_sub, arityType_sub] using happ

/-- The highest-level computational projection normalizes at every finite universe bound. -/
theorem topErase_normalization (h : BoundedTyping n Γ t A)
    (hq : sortRank q + 1 = n) : SN (topErase n q Γ t) :=
  two_sort_normalization (topErase_typing h hq)

end Submission.Helpers
