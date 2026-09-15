import Submission.SourceOperationalUniverses

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- The output of source stage d: carriers through d, and a candidate
comparison only when d has reached the final value coordinate. -/
structure SourceTypeEqPrefix (d : Nat) (A B : FiniteGridType R) : Prop where
  code : FiniteGridCodeEqBelow (d + 1) A B
  candidate : R + 1 ≤ d → ∀ v, A.Valid v → A.candidate v = B.candidate v

theorem SourceTypeEqPrefix.of_eq (d : Nat) {A B : FiniteGridType R} (h : A = B) :
    SourceTypeEqPrefix d A B := by
  cases h
  exact ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem SourceTypeEqPrefix.full {A B : FiniteGridType R}
    (h : SourceTypeEqPrefix d A B) (hd : R + 1 ≤ d) : FiniteGridTypeEq A B :=
  ⟨fun j hj v hv => h.code j hj (by omega) v hv, h.candidate hd⟩

theorem sourceTypeEqPrefix_pi (r d : Nat) (A A' : FiniteGridType (r + 1))
    (B B' : FiniteGridFamily (r + 1)) (hA : SourceTypeEqPrefix d A A')
    (hB : ∀ a, A.Valid a → SourceTypeEqPrefix d (B.fiber a) (B'.fiber a)) :
    SourceTypeEqPrefix d (finitePiType r A B) (finitePiType r A' B') := by
  constructor
  · intro j hj hjd f hf
    exact finitePiType_carrier_below_eq r (d + 1) A A' B B' hA.code (fun a ha => (hB a ha).code) j hj hjd f
  · intro hd v hv
    exact congrArg (fun T => T.candidate v)
      (finitePiType_coherent_eq r A A' B B' (hA.full hd) (fun a ha => (hB a ha).full hd))

theorem sourceTypeEqPrefix_decode (R d : Nat) (s : Option Srt)
    (u w : FiniteGridValue R) (h : FiniteGridValue.Agree d u w) :
    SourceTypeEqPrefix d (uniformUniverseDecode R s u) (uniformUniverseDecode R s w) := by
  constructor
  · intro j hj hjd v hv
    exact uniformUniverseDecode_causal R s u w j hj (h.mono (by omega)) v
  · intro hd v hv
    have he : u = w := by funext i; exact h i (by omega)
    rw [he]

theorem uniformUniverseEncode_prefix_conversion (R d : Nat) (hd : d ≤ R + 1)
    (s : Srt) (A B : FiniteGridType R) (h : SourceTypeEqPrefix d A B) (hA : A.Formed s) :
    FiniteGridValue.Agree d (uniformUniverseEncode R (some s) A) (uniformUniverseEncode R (some s) B) := by
  cases s with
  | prop =>
    by_cases he : R + 1 ≤ d
    · have hh := (h.full he).reifyProp_eq hA
      intro i hi
      exact congrFun hh i
    · intro i hi
      change propReifyValues R _ i.val = propReifyValues R _ i.val
      unfold propReifyValues
      rw [dif_neg (show i.val ≠ R by omega), dif_neg (show i.val ≠ R by omega)]
  | type r =>
    by_cases hr : r + 1 ≤ R
    · obtain ⟨k, he⟩ : ∃ k, R = r + 1 + k := ⟨R - (r + 1), by omega⟩
      subst R
      rw [uniformUniverseEncode_at, uniformUniverseEncode_at]
      by_cases he : r + 1 + k + 1 ≤ d
      · intro i hi
        exact congrFun ((h.full he).reify_eq r k hA) i
      · exact h.code.reify_prefix r k d (by omega) hA
    · unfold uniformUniverseEncode
      dsimp only
      rw [dif_neg hr, dif_neg hr]
      intro i hi
      rfl

def GridEnvironment.RenamedBelow (d : Nat) (Γ : List Tm) (ι : Nat → Nat)
    (ρ δ : GridEnvironment R) : Prop :=
  ∀ x A, Γ[x]? = some A → FiniteGridValue.Agree d (δ (ι x)) (ρ x)

theorem GridEnvironment.RenamedBelow.up {ρ δ : GridEnvironment R}
    (h : RenamedBelow d Γ ι ρ δ) (A : Tm) (x : FiniteGridValue R) :
    RenamedBelow d (A :: Γ) (upRen ι) (push x ρ) (push x δ) := by
  intro i C hi
  cases i with
  | zero => intro j hj; rfl
  | succ i => exact h i C hi

/-- These are only the carrier and context premises consumed by the next
source renaming stage. No value equation, candidate equation, substitution
law, fundamental lemma, or source normalization is a field. -/
structure SourceRenamingFrontier (r d : Nat) where
  admissible : List Tm → GridEnvironment (r + 1) → Prop
  depth : d ≤ r + 2
  extend : ∀ {Γ ρ A s x}, BoundedTyping (r + 2) Γ A (.srt s) → admissible Γ ρ →
    (sourceGridInterpretation r Γ ρ A).carrier.Coherent d depth (FiniteGridValue.toTower _ x) →
    admissible (A :: Γ) (push x ρ)
  inferred : ∀ {Γ Δ t T ι ρ δ}, BoundedTyping (r + 2) Γ t T → BoundedWf (r + 2) Δ →
    RenCtx Γ Δ ι → admissible Γ ρ → admissible Δ δ → GridEnvironment.RenamedBelow d Γ ι ρ δ →
    FiniteGridCodeEqBelow d
      (sourceGridInterpretation r Δ δ (chosenType (r + 2) Δ (ren ι t)))
      (sourceGridInterpretation r Γ ρ (chosenType (r + 2) Γ t))
  types : ∀ {Γ Δ A s ι ρ δ}, BoundedTyping (r + 2) Γ A (.srt s) → BoundedWf (r + 2) Δ →
    RenCtx Γ Δ ι → admissible Γ ρ → admissible Δ δ → GridEnvironment.RenamedBelow d Γ ι ρ δ →
    FiniteGridCodeEqBelow d (sourceGridInterpretation r Δ δ (ren ι A)) (sourceGridInterpretation r Γ ρ A)
  domain : ∀ {Γ Δ f A B ι ρ δ}, BoundedTyping (r + 2) Γ f (.pi A B) → BoundedWf (r + 2) Δ →
    RenCtx Γ Δ ι → admissible Γ ρ → admissible Δ δ → GridEnvironment.RenamedBelow d Γ ι ρ δ →
    FiniteGridCodeEqBelow d
      (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (ren ι f)).1)
      (sourceGridInterpretation r Γ ρ (chosenProduct (r + 2) Γ f).1)
  codomain : ∀ {Γ Δ f A B ι ρ δ}, BoundedTyping (r + 2) Γ f (.pi A B) → BoundedWf (r + 2) Δ →
    RenCtx Γ Δ ι → admissible Γ ρ → admissible Δ δ → GridEnvironment.RenamedBelow d Γ ι ρ δ →
    ∀ x, (sourceGridInterpretation r Δ δ (chosenProduct (r + 2) Δ (ren ι f)).1).Valid x →
    FiniteGridCodeEqBelow d
      (sourceGridInterpretation r ((chosenProduct (r + 2) Δ (ren ι f)).1 :: Δ) (push x δ)
        (chosenProduct (r + 2) Δ (ren ι f)).2)
      (sourceGridInterpretation r ((chosenProduct (r + 2) Γ f).1 :: Γ) (push x ρ)
        (chosenProduct (r + 2) Γ f).2)

end Submission.Helpers
