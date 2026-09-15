import Submission.FirstGridCodes

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The first intermediate source carrier at bound `r + 3`. Its universe
atom contains codes in grid `(r + 1, 1)`, which varies with the source bound. -/
noncomputable def firstGridShape (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (A : Tm) (u : ShapeValue) : (carrierGrid (r + 2) 1).Code :=
  firstGridCode r (middleShape (r + 3) (r + 1) Γ ρ A u)

noncomputable def firstGridProduct (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 2) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code) (u : ShapeValue) :
    (carrierGrid (r + 2) 1).Code :=
  (carrierGridQuantifiers (r + 1) 0).pi (carrierGridArrows (r + 2) 1) a
    (fun x => D ⟨a, x⟩) (fun x => B ⟨a, x⟩ (u.apply ⟨a, x⟩))

theorem firstGridShape_pi (h : BoundedTyping (r + 3) Γ (.pi A B) (.srt s))
    (hρ : ShapeContext (.type (r + 1)) Γ ρ) :
    firstGridShape r Γ ρ (.pi A B) u = firstGridProduct r (arityAt (.type (r + 1)) A)
      (fun x => firstGridShape r Γ ρ A x)
      (fun x y => firstGridShape r (A :: Γ) (push x ρ) B y) u :=
  (congrArg (firstGridCode r) (middleShape_pi h rfl hρ)).trans (firstGridCode_pi r _ _ _)

theorem firstGridShape_at_universe (h : BoundedTyping (r + 3) Γ A (.srt (.type (r + 1)))) :
    firstGridShape r Γ ρ A u = .small (nextArity (r + 3) (r + 1) Γ ρ A) :=
  congrArg (firstGridCode r) (middleShape_at_universe h)

theorem firstGridShape_lower (h : BoundedTyping (r + 3) Γ A (.srt s))
    (hs : sortRank s < sortRank (.type (r + 1))) :
    firstGridShape r Γ ρ A u = .small Arity.unit :=
  congrArg (firstGridCode r) (middleShape_lower h hs)

theorem firstGridShape_ren (h : BoundedTyping (r + 3) Γ A (.srt s))
    (hw : BoundedWf (r + 3) Δ) (hι : RenCtx Γ Δ ι) (he : ∀ j, δ (ι j) = ρ j) :
    firstGridShape r Δ δ (ren ι A) u = firstGridShape r Γ ρ A u :=
  congrArg (firstGridCode r) (middleShape_ren h hw hι rfl he)

theorem firstGridShape_substitute (h : BoundedTyping (r + 3) Γ A (.srt s))
    (hw : BoundedWf (r + 3) Δ) (hσ : BoundedSubCtx (r + 3) Γ Δ σ)
    (hk : ∀ j, kindAt (.type (r + 1)) (σ j) = false) :
    firstGridShape r Δ ρ (sub σ A) u =
      firstGridShape r Γ (shapeSub (r + 3) (r + 1) Δ ρ σ) A u :=
  congrArg (firstGridCode r) (middleShape_substitute h hw hσ hk rfl)

/-- Typed single substitution discharges the kind restriction internally. -/
theorem firstGridShape_subst (hB : BoundedTyping (r + 3) (A :: Γ) B (.srt sB))
    (ha : BoundedTyping (r + 3) Γ a A) (hA : BoundedTyping (r + 3) Γ A (.srt sA)) :
    firstGridShape r Γ ρ (subst 0 a B) u = firstGridShape r (A :: Γ)
      (push (shapeEval (r + 3) (r + 1) Γ ρ a) ρ) B u :=
  congrArg (firstGridCode r) (middleShape_subst hB ha hA rfl)

theorem firstGridShape_step (h : BoundedTyping (r + 3) Γ A (.srt s))
    (hρ : ShapeContext (.type (r + 1)) Γ ρ) (hs : Step A A') :
    firstGridShape r Γ ρ A u = firstGridShape r Γ ρ A' u :=
  congrArg (firstGridCode r) (middleShape_step h rfl hρ hs)

theorem firstGridShape_conv (hA : FiberTypeExpression (r + 3) Γ A)
    (hB : FiberTypeExpression (r + 3) Γ B) (hρ : ShapeContext (.type (r + 1)) Γ ρ)
    (hc : Conv A B) : firstGridShape r Γ ρ A u = firstGridShape r Γ ρ B u :=
  congrArg (firstGridCode r) (middleShape_conv hA hB rfl hρ hc)

noncomputable def inferredFirstGrid (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (t : Tm) : (carrierGrid (r + 2) 1).Code := firstGridCode r (inferredMiddle (r + 3) (r + 1) Γ ρ t)

theorem inferredFirstGrid_eq (h : BoundedTyping (r + 3) Γ t A)
    (hρ : ShapeContext (.type (r + 1)) Γ ρ) :
    inferredFirstGrid r Γ ρ t = firstGridShape r Γ ρ A (shapeEval (r + 3) (r + 1) Γ ρ t) :=
  congrArg (firstGridCode r) (inferredMiddle_eq h rfl hρ)

theorem inferredFirstGrid_subst (hb : BoundedTyping (r + 3) (A :: Γ) b B)
    (ha : BoundedTyping (r + 3) Γ a A) (hA : BoundedTyping (r + 3) Γ A (.srt sA))
    (hρ : ShapeContext (.type (r + 1)) Γ ρ) :
    inferredFirstGrid r Γ ρ (subst 0 a b) = inferredFirstGrid r (A :: Γ)
      (push (shapeEval (r + 3) (r + 1) Γ ρ a) ρ) b :=
  congrArg (firstGridCode r) (inferredMiddle_subst hb ha hA rfl hρ)

abbrev FirstGridValue (r : Nat) := TowerValue (carrierGrid (r + 2) 1)

def FirstGridContext (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (δ : Nat → FirstGridValue r) : Prop :=
  ∀ j A, Γ[j]? = some A → (δ j).code = firstGridShape r Γ ρ (lift (j + 1) 0 A) (ρ j)

theorem FirstGridContext.up (h : FirstGridContext r Γ ρ δ)
    (hA : BoundedTyping (r + 3) Γ A (.srt s))
    (hy : y.code = firstGridShape r Γ ρ A x) :
    FirstGridContext r (A :: Γ) (push x ρ) (push y δ) := by
  intro j C hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst C
    simpa only [push, Nat.zero_add, lift_one,
      firstGridShape_ren hA (.cons hA.wf hA) (.weaken Γ A) (fun _ => rfl)] using hy
  | succ j =>
    obtain ⟨sC, hC⟩ := hA.wf.lookup hj
    simpa only [push, ← ren_succ_lift (j + 1),
      firstGridShape_ren hC (.cons hA.wf hA) (.weaken Γ A) (fun _ => rfl)] using h j C hj

theorem FirstGridContext.var_code (h : FirstGridContext r Γ ρ δ)
    (hw : BoundedWf (r + 3) Γ) (hj : Γ[j]? = some A)
    (hρ : ShapeContext (.type (r + 1)) Γ ρ) : (δ j).code = inferredFirstGrid r Γ ρ (.var j) := by
  rw [inferredFirstGrid_eq (.var hw hj) hρ]
  exact h j A hj

noncomputable def defaultFirstGridEnv (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (j : Nat) : FirstGridValue r :=
  let A := firstGridShape r Γ ρ (lift (j + 1) 0 (Γ[j]?.getD (.srt .prop))) (ρ j)
  ⟨A, (carrierGrid (r + 2) 1).point A⟩

theorem defaultFirstGridEnv_context (r : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue) :
    FirstGridContext r Γ ρ (defaultFirstGridEnv r Γ ρ) := by
  intro j A hj
  simp only [defaultFirstGridEnv, hj, Option.getD_some]

end Submission.Helpers
