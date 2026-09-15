import Submission.MiddleCodes
import Submission.FiberShapeSoundness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The lower function carrier over a fixed upper function value. -/
noncomputable def middleProduct (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode) (v : ShapeValue) : MiddleCode :=
  MiddleCode.pi a (fun x => D ⟨a, x⟩) (fun x => B ⟨a, x⟩ (v.apply ⟨a, x⟩))

theorem middleProduct_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ y, B x y = B' x y) :
    middleProduct a D B v = middleProduct a' D' B' v := by
  subst a'
  unfold middleProduct
  congr 1
  · funext x
    exact hD ⟨a, x⟩ rfl
  · funext x
    exact hB ⟨a, x⟩ rfl _

theorem middleProduct_unit (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode) (v : ShapeValue) :
    middleProduct .unit D B v = (D .unit).arrow (B .unit (v.apply .unit)) :=
  MiddleCode.all_unit _

theorem middleProduct_trivial (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode) (v : ShapeValue)
    (h : ∀ x, x.code = a → B x (v.apply x) = .small .unit) :
    middleProduct a D B v = .small .unit := by
  apply MiddleCode.all_trivial
  intro x
  change (D ⟨a, x⟩).arrow (B ⟨a, x⟩ (v.apply ⟨a, x⟩)) = _
  rw [h ⟨a, x⟩ rfl, MiddleCode.arrow_unit]

/-- The next carrier, retaining lower fiber-code families at the upper universe.
For bound three use `n = 3` and `i = 1`. -/
noncomputable def middleShape (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (A : Tm) (v : ShapeValue) : MiddleCode := by
  classical
  exact if typeSort n Γ A = some (.type i) then .small (nextArity n i Γ ρ A)
    else if ∃ s, typeSort n Γ A = some s ∧ sortRank s < sortRank (.type i) then
      .small .unit
    else match A with
      | .srt s => if s = .type i then .universe v.asArity else .small .unit
      | .pi D B => middleProduct (arityAt (.type i) D)
          (fun x => middleShape n i Γ ρ D x)
          (fun x y => middleShape n i (D :: Γ) (push x ρ) B y) v
      | _ => .small .unit
termination_by structural A

theorem middleShape_eq (n i : Nat) (Γ : List Tm) (ρ : Nat → ShapeValue)
    (A : Tm) (v : ShapeValue) :
    middleShape n i Γ ρ A v =
      if typeSort n Γ A = some (.type i) then .small (nextArity n i Γ ρ A)
      else if ∃ s, typeSort n Γ A = some s ∧ sortRank s < sortRank (.type i) then
        .small .unit
      else match A with
        | .srt s => if s = .type i then .universe v.asArity else .small .unit
        | .pi D B => middleProduct (arityAt (.type i) D)
            (fun x => middleShape n i Γ ρ D x)
            (fun x y => middleShape n i (D :: Γ) (push x ρ) B y) v
        | _ => .small .unit := by
  classical
  cases A <;> rfl

theorem middleShape_at_universe (h : BoundedTyping n Γ A (.srt (.type i))) :
    middleShape n i Γ ρ A v = .small (nextArity n i Γ ρ A) := by
  classical
  rw [middleShape_eq, if_pos (typeSort_eq h)]

theorem middleShape_lower (h : BoundedTyping n Γ A (.srt s))
    (hs : sortRank s < sortRank (.type i)) : middleShape n i Γ ρ A v = .small .unit := by
  classical
  have hne : typeSort n Γ A ≠ some (.type i) := by
    rw [typeSort_eq h]
    intro he
    have he' := Option.some.inj he
    subst s
    omega
  rw [middleShape_eq, if_neg hne, if_pos ⟨s, typeSort_eq h, hs⟩]

theorem middleShape_small (h : BoundedTyping n Γ A (.srt s))
    (hs : sortRank s ≤ sortRank (.type i)) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) :
    middleShape n i Γ ρ A v = .small (nextArity n i Γ ρ A) := by
  by_cases he : s = .type i
  · subst s
    exact middleShape_at_universe h
  · rw [middleShape_lower h (by
      have hh : sortRank s ≠ sortRank (.type i) := fun e => he (sortRank_injective e)
      omega), nextArity_lower h hq hρ he]

theorem middleShape_top (h : BoundedTyping n Γ A (.srt s)) (hs : sortRank s = n)
    (hq : sortRank (.type i) + 1 = n) :
    middleShape n i Γ ρ A v = match A with
      | .srt r => if r = .type i then .universe v.asArity else .small .unit
      | .pi D B => middleProduct (arityAt (.type i) D)
          (fun x => middleShape n i Γ ρ D x)
          (fun x y => middleShape n i (D :: Γ) (push x ρ) B y) v
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
  rw [middleShape_eq, if_neg hne, if_neg hnl]
  cases A <;> rfl

/-- All three possible universe levels give the same dependent product carrier. -/
theorem middleShape_pi (h : BoundedTyping n Γ (.pi A B) (.srt s))
    (hq : sortRank (.type i) + 1 = n) (hρ : ShapeContext (.type i) Γ ρ) :
    middleShape n i Γ ρ (.pi A B) v = middleProduct (arityAt (.type i) A)
      (fun x => middleShape n i Γ ρ A x)
      (fun x y => middleShape n i (A :: Γ) (push x ρ) B y) v := by
  obtain ⟨sA, sB, sC, hA, hB, hr, hsA, hsB, hsC, hc⟩ := h.generation
  have he := conv_srt_inj hc
  subst sC
  rcases sort_level_cases hsC hq with he | hlt | ht
  · subst s
    have hda := h.top_pi_domain_unit hq
    rw [middleShape_at_universe h, nextArity_pi h hq, hda, middleProduct_unit]
    rw [middleShape_small hA (rule_predicative_domain hr) hq hρ,
      middleShape_small hB (rule_predicative_codomain hr) hq (hρ.up hda.symm),
      MiddleCode.arrow_small]
  · rw [middleShape_lower h hlt]
    symm
    apply middleProduct_trivial
    intro x hx
    exact middleShape_lower hB (Nat.lt_of_le_of_lt (rule_codomain_le hr) hlt)
  · exact middleShape_top h ht hq

/-- Below the top sort, comparison reduces to the already interpreted upper shape. -/
theorem middleShape_compare (hA : BoundedTyping n Γ A (.srt s))
    (hB : BoundedTyping n Δ B (.srt s)) (hq : sortRank (.type i) + 1 = n)
    (he : nextArity n i Γ ρ A = nextArity n i Δ δ B)
    (ht : sortRank s = n → middleShape n i Γ ρ A v = middleShape n i Δ δ B v) :
    middleShape n i Γ ρ A v = middleShape n i Δ δ B v := by
  rcases sort_level_cases hA.sort_bound hq with hs | hs | hs
  · subst s
    rw [middleShape_at_universe hA, middleShape_at_universe hB, he]
  · rw [middleShape_lower hA hs, middleShape_lower hB hs]
  · exact ht hs

end Submission.Helpers
