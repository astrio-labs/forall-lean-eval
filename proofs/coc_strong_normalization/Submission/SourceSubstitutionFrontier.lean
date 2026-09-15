import Submission.SourceConversionFrontier

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1500000

theorem FiniteGridCodeEqBelow.mono {A B : FiniteGridType R}
    (h : FiniteGridCodeEqBelow d A B) (he : e ≤ d) : FiniteGridCodeEqBelow e A B :=
  fun j hj hje v hv => h j hj (by omega) v hv

def GridEnvironment.SubstitutedBelow (r d : Nat) (Γ Δ : List Tm) (σ : Nat → Tm)
    (ρ δ : GridEnvironment (r + 1)) : Prop :=
  ∀ j A, Γ[j]? = some A → FiniteGridValue.Agree d (sourceGridEval r Δ ρ (σ j)) (δ j)

theorem GridEnvironment.SubstitutedBelow.mono (he : SubstitutedBelow r d Γ Δ σ ρ δ)
    (hed : e ≤ d) : SubstitutedBelow r e Γ Δ σ ρ δ :=
  fun j A hj => (he j A hj).mono hed

/-- A substitution stage follows renaming at the same stage and consumes
only the preceding carrier comparisons for substitution. No substitution
value equation or candidate equation is a field. -/
structure SourceSubstitutionFrontier (r d : Nat) where
  admissible : List Tm → GridEnvironment (r + 1) → Prop
  conversion : SourceCarrierConversion r d admissible
  extend : ∀ {Γ ρ A s x}, BoundedTyping (r + 2) Γ A (.srt s) → admissible Γ ρ →
    (sourceGridInterpretation r Γ ρ A).carrier.Coherent d conversion.depth (FiniteGridValue.toTower _ x) →
    admissible (A :: Γ) (push x ρ)
  rename_stage : ∀ {Γ Δ t T ι ρ δ}, BoundedTyping (r + 2) Γ t T → BoundedWf (r + 2) Δ →
    RenCtx Γ Δ ι → admissible Γ ρ → admissible Δ δ →
    GridEnvironment.RenamedBelow d Γ ι ρ δ →
    FiniteGridValue.Agree d (sourceGridEval r Δ δ (ren ι t)) (sourceGridEval r Γ ρ t) ∧
    (∀ s, BoundedTyping (r + 2) Γ t (.srt s) →
      SourceTypeEqPrefix d (sourceGridInterpretation r Δ δ (ren ι t)) (sourceGridInterpretation r Γ ρ t))
  inferred : ∀ {Γ Δ t T σ ρ δ}, BoundedTyping (r + 2) Γ t T → BoundedWf (r + 2) Δ →
    BoundedSubCtx (r + 2) Γ Δ σ → (∀ j, kindAt (.type r) (σ j) = false) →
    admissible Γ δ → admissible Δ ρ →
    GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ →
    FiniteGridCodeEqBelow d
      (sourceGridInterpretation r Δ ρ (chosenType (r + 2) Δ (sub σ t)))
      (sourceGridInterpretation r Γ δ (chosenType (r + 2) Γ t))
  types : ∀ {Γ Δ A s σ ρ δ}, BoundedTyping (r + 2) Γ A (.srt s) → BoundedWf (r + 2) Δ →
    BoundedSubCtx (r + 2) Γ Δ σ → (∀ j, kindAt (.type r) (σ j) = false) →
    admissible Γ δ → admissible Δ ρ →
    GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ →
    FiniteGridCodeEqBelow d (sourceGridInterpretation r Δ ρ (sub σ A)) (sourceGridInterpretation r Γ δ A)
  domain : ∀ {Γ Δ f A B σ ρ δ}, BoundedTyping (r + 2) Γ f (.pi A B) → BoundedWf (r + 2) Δ →
    BoundedSubCtx (r + 2) Γ Δ σ → (∀ j, kindAt (.type r) (σ j) = false) →
    admissible Γ δ → admissible Δ ρ →
    GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ →
    FiniteGridCodeEqBelow d
      (sourceGridInterpretation r Δ ρ (chosenProduct (r + 2) Δ (sub σ f)).1)
      (sourceGridInterpretation r Γ δ (chosenProduct (r + 2) Γ f).1)
  codomain : ∀ {Γ Δ f A B σ ρ δ}, BoundedTyping (r + 2) Γ f (.pi A B) → BoundedWf (r + 2) Δ →
    BoundedSubCtx (r + 2) Γ Δ σ → (∀ j, kindAt (.type r) (σ j) = false) →
    admissible Γ δ → admissible Δ ρ →
    GridEnvironment.SubstitutedBelow r d Γ Δ σ ρ δ →
    ∀ x, (sourceGridInterpretation r Δ ρ (chosenProduct (r + 2) Δ (sub σ f)).1).Valid x →
    FiniteGridCodeEqBelow d
      (sourceGridInterpretation r ((chosenProduct (r + 2) Δ (sub σ f)).1 :: Δ) (push x ρ)
        (chosenProduct (r + 2) Δ (sub σ f)).2)
      (sourceGridInterpretation r ((chosenProduct (r + 2) Γ f).1 :: Γ) (push x δ)
        (chosenProduct (r + 2) Γ f).2)

theorem GridEnvironment.SubstitutedBelow.variable (F : SourceSubstitutionFrontier r d)
    (he : SubstitutedBelow r d Γ Δ σ ρ δ) (h : BoundedTyping (r + 2) Γ (.var j) T)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hk : ∀ j, kindAt (.type r) (σ j) = false)
    (hδ : F.admissible Γ δ) (hρ : F.admissible Δ ρ)
    (hj : Γ[j]? = some A) :
    FiniteGridValue.Agree d (sourceGridEval r Δ ρ (σ j)) (sourceGridEval r Γ δ (.var j)) := by
  have hh := FiniteGridType.normalizeValue_prefix_congr _ _ d F.conversion.depth
    (F.inferred h hw hσ hk hδ hρ he) _ _ (he j A hj)
  simp only [sub] at hh
  rw [FiniteGridType.normalizeValue_eq _ _ (sourceGridEval_inferred r Δ ρ (σ j))] at hh
  rw [sourceGridEval_var_normalize]
  exact hh

theorem GridEnvironment.SubstitutedBelow.up (F : SourceSubstitutionFrontier r d)
    (he : SubstitutedBelow r d Γ Δ σ ρ δ)
    (hw : BoundedWf (r + 2) Δ) (hσ : BoundedSubCtx (r + 2) Γ Δ σ)
    (hA : BoundedTyping (r + 2) Γ A (.srt s)) (hρ : F.admissible Δ ρ)
    (x : FiniteGridValue (r + 1)) (hx : (sourceGridInterpretation r Δ ρ (sub σ A)).Valid x) :
    SubstitutedBelow r d (A :: Γ) (sub σ A :: Δ) (upSub σ) (push x ρ) (push x δ) := by
  have hA' := hA.substitute hw hσ
  have hctx := F.extend hA' hρ (hx.mono (hd := Nat.le_refl (r + 2)) F.conversion.depth)
  have hrel : GridEnvironment.RenamedBelow d Δ Nat.succ ρ (push x ρ) := by
    intro j C hj i hi
    rfl
  intro j C hj
  cases j with
  | zero =>
    have hv : BoundedTyping (r + 2) (sub σ A :: Δ) (.var 0) (lift 1 0 (sub σ A)) :=
      .var (.cons hw hA') rfl
    have hChosen := chosenType_typing hv
    have hEq := F.conversion.convert hChosen.type_expression hv.type_expression hctx
      (typing_unique hChosen.forget hv.forget)
    have hRen := (F.rename_stage hA' (.cons hw hA') (.weaken Δ (sub σ A)) hρ hctx hrel).2 s hA'
    have hCode : FiniteGridCodeEqBelow d
        (sourceGridInterpretation r (sub σ A :: Δ) (push x ρ) (chosenType (r + 2) (sub σ A :: Δ) (.var 0)))
        (sourceGridInterpretation r Δ ρ (sub σ A)) := by
      rw [← ren_shift] at hEq
      exact hEq.trans (hRen.code.mono (Nat.le_succ _))
    have hc := hCode.coherent_backward d F.conversion.depth (Nat.le_refl _) _
      (hx.mono (hd := Nat.le_refl (r + 2)) F.conversion.depth)
    change FiniteGridValue.Agree d (sourceGridEval r (sub σ A :: Δ) (push x ρ) (.var 0)) x
    rw [sourceGridEval_var_normalize]
    exact FiniteGridType.normalizeValue_recover_prefix _ d F.conversion.depth _ hc
  | succ j =>
    have hh := (F.rename_stage (hσ j C hj) (.cons hw hA') (.weaken Δ (sub σ A)) hρ hctx hrel).1
    exact fun i hi => (hh i hi).trans (he j C hj i hi)

end Submission.Helpers
