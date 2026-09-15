import Submission.FiberCandidates
import Submission.SortClassification

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The lower function carrier over a fixed upper function value. -/
noncomputable def fiberProduct (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode) (v : ShapeValue) : FiberCode :=
  FiberCode.pi a (fun x => D ⟨a, x⟩) (fun x => B ⟨a, x⟩ (v.apply ⟨a, x⟩))

theorem fiberProduct_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ y, B x y = B' x y) :
    fiberProduct a D B v = fiberProduct a' D' B' v := by
  subst a'
  unfold fiberProduct
  congr 1
  · funext x
    exact hD ⟨a, x⟩ rfl
  · funext x
    exact hB ⟨a, x⟩ rfl _

theorem fiberProduct_unit (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode) (v : ShapeValue) :
    fiberProduct .unit D B v = (D .unit).arrow (B .unit (v.apply .unit)) :=
  FiberCode.all_unit _

theorem fiberProduct_trivial (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode) (v : ShapeValue)
    (h : ∀ x, x.code = a → B x (v.apply x) = .small .unit) :
    fiberProduct a D B v = .small .unit := by
  apply FiberCode.all_trivial
  intro x
  change (D ⟨a, x⟩).arrow (B ⟨a, x⟩ (v.apply ⟨a, x⟩)) = _
  rw [h ⟨a, x⟩ rfl, FiberCode.arrow_unit]

/-- A type's next carrier can depend on the semantic data already fixed above it. -/
noncomputable def fiberShape (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (A : Tm) (v : ShapeValue) : FiberCode := by
  classical
  exact if typeSort n Γ A = some (.type i) then .small (nextArity n i Γ ρ A)
    else if ∃ s, typeSort n Γ A = some s ∧ sortRank s < sortRank (.type i) then
      .small .unit
    else match A with
      | .srt s => if s = .type i then .small (.fn v.asArity .prop) else .small .unit
      | .pi D B => fiberProduct (arityAt (.type i) D)
          (fun x => fiberShape n i Γ ρ D x)
          (fun x y => fiberShape n i (D :: Γ) (push x ρ) B y) v
      | _ => .small .unit
termination_by structural A

theorem fiberShape_eq (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (A : Tm) (v : ShapeValue) :
    fiberShape n i Γ ρ A v =
      if typeSort n Γ A = some (.type i) then .small (nextArity n i Γ ρ A)
      else if ∃ s, typeSort n Γ A = some s ∧ sortRank s < sortRank (.type i) then
        .small .unit
      else match A with
        | .srt s => if s = .type i then .small (.fn v.asArity .prop) else .small .unit
        | .pi D B => fiberProduct (arityAt (.type i) D)
            (fun x => fiberShape n i Γ ρ D x)
            (fun x y => fiberShape n i (D :: Γ) (push x ρ) B y) v
        | _ => .small .unit := by
  classical
  cases A <;> rfl

theorem fiberShape_at_universe (h : BoundedTyping n Γ A (.srt (.type i))) :
    fiberShape n i Γ ρ A v = .small (nextArity n i Γ ρ A) := by
  classical
  rw [fiberShape_eq, if_pos (typeSort_eq h)]

theorem fiberShape_lower (h : BoundedTyping n Γ A (.srt s))
    (hs : sortRank s < sortRank (.type i)) : fiberShape n i Γ ρ A v = .small .unit := by
  classical
  have hne : typeSort n Γ A ≠ some (.type i) := by
    rw [typeSort_eq h]
    intro he
    have he' := Option.some.inj he
    subst s
    omega
  rw [fiberShape_eq, if_neg hne, if_pos ⟨s, typeSort_eq h, hs⟩]

theorem fiberShape_small (h : BoundedTyping n Γ A (.srt s))
    (hs : sortRank s ≤ sortRank (.type i)) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) :
    fiberShape n i Γ ρ A v = .small (nextArity n i Γ ρ A) := by
  by_cases he : s = .type i
  · subst s
    exact fiberShape_at_universe h
  · rw [fiberShape_lower h (by
      have hh : sortRank s ≠ sortRank (.type i) := fun e => he (sortRank_injective e)
      omega), nextArity_lower h hq hρ he]

theorem fiberShape_top (h : BoundedTyping n Γ A (.srt s)) (hs : sortRank s = n)
    (hq : sortRank (.type i) + 1 = n) :
    fiberShape n i Γ ρ A v = match A with
      | .srt r => if r = .type i then .small (.fn v.asArity .prop) else .small .unit
      | .pi D B => fiberProduct (arityAt (.type i) D)
          (fun x => fiberShape n i Γ ρ D x)
          (fun x y => fiberShape n i (D :: Γ) (push x ρ) B y) v
      | _ => .small .unit := by
  classical
  have hne : typeSort n Γ A ≠ some (.type i) := by
    rw [typeSort_eq h]
    intro he
    have he' := Option.some.inj he
    subst s
    omega
  have hnl : ¬ ∃ r, typeSort n Γ A = some r ∧ sortRank r < sortRank (.type i) := by
    rintro ⟨r, hr, hlt⟩
    rw [typeSort_eq h] at hr
    have he := Option.some.inj hr
    subst r
    omega
  rw [fiberShape_eq, if_neg hne, if_neg hnl]
  cases A <;> rfl

theorem rule_codomain_le (hr : Rl s₁ s₂ s₃) : sortRank s₂ ≤ sortRank s₃ := by
  cases hr with
  | prop => exact Nat.le_refl _
  | type a b => simp only [sortRank]; omega
  | propType => exact Nat.le_refl _

/-- All three possible universe levels give the same dependent product carrier. -/
theorem fiberShape_pi (h : BoundedTyping n Γ (.pi A B) (.srt s))
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    fiberShape n i Γ ρ (.pi A B) v = fiberProduct (arityAt (.type i) A)
      (fun x => fiberShape n i Γ ρ A x)
      (fun x y => fiberShape n i (A :: Γ) (push x ρ) B y) v := by
  obtain ⟨sA, sB, sC, hA, hB, hr, hsA, hsB, hsC, hc⟩ := h.generation
  have he := conv_srt_inj hc
  subst sC
  rcases sort_level_cases hsC hq with he | hlt | ht
  · subst s
    have hda := h.top_pi_domain_unit hq
    rw [fiberShape_at_universe h, nextArity_pi h hq, hda, fiberProduct_unit]
    rw [fiberShape_small hA (rule_predicative_domain hr) hq hρ,
      fiberShape_small hB (rule_predicative_codomain hr) hq (hρ.up hda.symm),
      FiberCode.arrow_small]
  · rw [fiberShape_lower h hlt]
    symm
    apply fiberProduct_trivial
    intro x hx
    exact fiberShape_lower hB (Nat.lt_of_le_of_lt (rule_codomain_le hr) hlt)
  · exact fiberShape_top h ht hq

/-- Below the top sort, comparison reduces to the already interpreted upper shape. -/
theorem fiberShape_compare (hA : BoundedTyping n Γ A (.srt s))
    (hB : BoundedTyping n Δ B (.srt s)) (hq : sortRank (.type i) + 1 = n)
    (he : nextArity n i Γ ρ A = nextArity n i Δ δ B)
    (ht : sortRank s = n → fiberShape n i Γ ρ A v = fiberShape n i Δ δ B v) :
    fiberShape n i Γ ρ A v = fiberShape n i Δ δ B v := by
  rcases sort_level_cases hA.sort_bound hq with hs | hs | hs
  · subst s
    rw [fiberShape_at_universe hA, fiberShape_at_universe hB, he]
  · rw [fiberShape_lower hA hs, fiberShape_lower hB hs]
  · exact ht hs

end Submission.Helpers
