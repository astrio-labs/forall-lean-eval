import Submission.FiberSoundness
import Submission.TwoSortNormalization

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A syntactic substitution realizes a context at its two semantic layers. -/
def FiberRealizesContext (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → FiberValue) (σ : Nat → Tm) : Prop :=
  ∀ j A, Γ[j]? = some A →
    ((fiberSemantics Γ ρ δ (lift (j + 1) 0 A)).2 (ρ j) (δ j)).contains (σ j)

theorem FiberRealizesContext.up (hσ : FiberRealizesContext Γ ρ δ σ)
    (hA : BoundedTyping 2 Γ A (.srt s)) (hρ : ShapeContext (.type 0) Γ ρ)
    (hx : x.code = arityAt (.type 0) A)
    (ha : ((fiberSemantics Γ ρ δ A).2 x y).contains a) :
    FiberRealizesContext (A :: Γ) (push x ρ) (push y δ) (push a σ) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      (fiberSemantics_ren hA (.cons hA.wf hA) (.weaken Γ A)
        hρ (hρ.up hx) (fun _ => rfl) (fun _ => rfl)).2 s hA] using ha
  | succ j =>
    obtain ⟨r, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1),
      (fiberSemantics_ren hC (.cons hA.wf hA) (.weaken Γ A)
        hρ (hρ.up hx) (fun _ => rfl) (fun _ => rfl)).2 r hC] using hσ j C hj

/-- Every candidate contains each variable, independently of the chosen
semantic values. -/
theorem FiberRealizesContext.identity (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → FiberValue) : FiberRealizesContext Γ ρ δ Tm.var := by
  intro j A hj
  exact ((fiberSemantics Γ ρ δ (lift (j + 1) 0 A)).2 (ρ j) (δ j)).var j

def defaultShapeEnv (Γ : List Tm) (j : Nat) : ShapeValue :=
  match Γ[j]? with
  | some A => ⟨arityAt (.type 0) A, (arityAt (.type 0) A).shapePoint⟩
  | none => .unit

noncomputable def defaultFiberEnv (Γ : List Tm) (ρ : Nat → ShapeValue) (j : Nat) :
    FiberValue :=
  match Γ[j]? with
  | some A =>
    let D := fiberShape 2 0 Γ ρ (lift (j + 1) 0 A) (ρ j)
    ⟨D, D.point⟩
  | none => .unit

theorem defaultShapeEnv_admissible (Γ : List Tm) :
    ShapeContext (.type 0) Γ (defaultShapeEnv Γ) := by
  intro j A hj
  simp only [defaultShapeEnv, hj]

theorem defaultFiberEnv_admissible (Γ : List Tm) (ρ : Nat → ShapeValue) :
    FiberContext 2 0 Γ ρ (defaultFiberEnv Γ ρ) := by
  intro j A hj
  simp only [defaultFiberEnv, hj]

/-- Admissible environments and an identity realization exist for every
context. This construction uses carrier points, without assuming that context
entries normalize or already satisfy the fundamental theorem. -/
theorem fiberEnvironment_exists (Γ : List Tm) :
    ∃ ρ δ, ShapeContext (.type 0) Γ ρ ∧ FiberContext 2 0 Γ ρ δ ∧
      FiberRealizesContext Γ ρ δ Tm.var :=
  ⟨defaultShapeEnv Γ, defaultFiberEnv Γ (defaultShapeEnv Γ),
    defaultShapeEnv_admissible Γ, defaultFiberEnv_admissible Γ _,
    FiberRealizesContext.identity Γ _ _⟩

/-- Fundamental reducibility for the original bound-two derivation and every
realizing substitution in admissible upper and lower environments. -/
theorem bound_two_fundamental (h : BoundedTyping 2 Γ t A)
    (hρ : ShapeContext (.type 0) Γ ρ) (hδ : FiberContext 2 0 Γ ρ δ)
    (hσ : FiberRealizesContext Γ ρ δ σ) :
    ((fiberSemantics Γ ρ δ A).2
      (shapeEval 2 0 Γ ρ t) (fiberSemantics Γ ρ δ t).1).contains (sub σ t) := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True)
      generalizing ρ δ σ with
  | nil => trivial
  | cons => trivial
  | srt hw ha hs hs' ihw =>
    change SN (.srt _)
    apply Acc.intro
    intro u hu
    cases hu
  | var hw hi ihw =>
    rw [fiberSemantics_var hδ hw hi hρ]
    exact hσ _ _ hi
  | @pi Γ A sA B sB s hA hB hr hsA hsB hs ihA ihB =>
    have ha : SN (sub σ A) := ihA hρ hδ hσ
    let x : ShapeValue := ⟨arityAt (.type 0) A, (arityAt (.type 0) A).shapePoint⟩
    let y : FiberValue := ⟨fiberShape 2 0 Γ ρ A x, (fiberShape 2 0 Γ ρ A x).point⟩
    have hb : SN (sub (push (.var 0) σ) B) :=
      ihB (hρ.up (x := x) rfl) (hδ.up hA rfl (y := y) rfl)
        (hσ.up hA hρ rfl (((fiberSemantics Γ ρ δ A).2 x y).var 0))
    exact sn_pi ha (sn_under_binder σ B hb)
  | @lam Γ A B s b hPi hb hs ihPi ihb =>
    obtain ⟨sA, hA, _⟩ := hPi.pi_domain
    have hD : SN (sub σ A) := sn_pi_domain (ihPi hρ hδ hσ)
    have ht : BoundedTyping 2 Γ (.lam A b) (.pi A B) := .lam hPi hb hs
    rw [fiberSemantics_pi (shapeEval_typed_code ht rfl hρ)
      (fiberSemantics_typed_code ht hρ), fiberSemantics_lam hPi hb hρ]
    apply fiberCandidatePi_lambda
    · intro x hx y hy
      rw [shapeEval_lam_apply hb hρ hx]
      exact fiberSemantics_typed_code hb (hρ.up hx)
    · exact hD
    · intro x hx y hy arg ha
      rw [shapeEval_lam_apply hb hρ hx, sub_push_beta]
      exact ihb (hρ.up hx) (hδ.up hA rfl hy) (hσ.up hA hρ hx ha)
  | @app Γ f A B a hf ha ihf iha =>
    exact fiberSemantics_app_candidate hf ha hρ hδ (ihf hρ hδ hσ) (iha hρ hδ hσ)
  | conv ht hB hc hs iht ihB =>
    rw [← type_fiberSemantics_conv ht hB hρ hδ hc]
    exact iht hρ hδ hσ

/-- Unconditional strong normalization for every term with an original
`BoundedTyping 2` derivation, in an arbitrary context. -/
theorem bound_two_normalization (h : BoundedTyping 2 Γ t A) : SN t := by
  obtain ⟨ρ, δ, hρ, hδ, hσ⟩ := fiberEnvironment_exists Γ
  have hc := bound_two_fundamental h hρ hδ hσ
  simpa only [sub_var] using
    ((fiberSemantics Γ ρ δ A).2
      (shapeEval 2 0 Γ ρ t) (fiberSemantics Γ ρ δ t).1).normalizes hc

end Submission.Helpers
