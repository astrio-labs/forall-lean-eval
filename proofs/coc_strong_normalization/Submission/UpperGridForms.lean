import Submission.UpperGridSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def UpperGridCode.IsArity (r : Nat) (C : UpperGridCode r) : Prop :=
  ∃ a : Arity, C = .small (.small a)

theorem UpperGridCode.IsArity.small {C : UpperGridCode r} (h : IsArity r C) : C.IsSmall := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨.small a, rfl⟩

theorem upperGridArrow_isArity {A B : UpperGridCode r}
    (hA : UpperGridCode.IsArity r A) (hB : UpperGridCode.IsArity r B) :
    UpperGridCode.IsArity r ((carrierGridArrows (r + 3) 2).code A B) := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  exact ⟨a.arrow b, (carrierGrid_arrow_small (r + 2) 1 (.small a) (.small b)).trans
    (congrArg LayerCode.small (carrierGrid_arrow_small (r + 1) 0 a b))⟩

theorem upperGridProduct_trivial (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = .small (.small .unit)) :
    upperGridProduct r a D B d c u f = .small (.small .unit) := by
  apply (carrierGridQuantifiers (r + 2) 1).trivial
  intro x
  apply (carrierGridQuantifiers (r + 2) 1).trivial
  intro y
  rw [hc ⟨a, x⟩ rfl ⟨D ⟨a, x⟩, y⟩ rfl]
  exact (carrierGridArrows (r + 3) 2).trivial _

theorem upperGridProduct_isSmall (r : Nat)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r) (k : Arity)
    (hD : D .unit = .small k) (hd : ∀ y, (d .unit y).IsSmall)
    (hc : ∀ y z w, (c .unit y z w).IsSmall) :
    (upperGridProduct r .unit D B d c u f).IsSmall := by
  unfold upperGridProduct
  erw [(carrierGridQuantifiers (r + 2) 1).single]
  change ((carrierGridQuantifiers (r + 2) 1).code (D .unit) _).IsSmall
  have hall (E : (carrierGrid (r + 3) 1).Code) (he : E = .small k)
      (g : (carrierGrid (r + 3) 1).El E → UpperGridCode r)
      (hg : ∀ y, (g y).IsSmall) : ((carrierGridQuantifiers (r + 2) 1).code E g).IsSmall := by
    subst E
    exact LayerCode.compactAll_isSmall (carrierGridQuantifiers (r + 1) 0)
      (carrierGridTerminal (r + 2) 0) (carrierGridTerminal (r + 2) 1) k g hg
  apply hall _ hD
  intro y
  exact LayerCode.compactArrow_isSmall (carrierGridArrows (r + 2) 1) (hd _) (hc _ _ _)

theorem upperGridProduct_isArity (r : Nat)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r)
    (hD : D .unit = .small .unit) (hd : ∀ y, UpperGridCode.IsArity r (d .unit y))
    (hc : ∀ y z w, UpperGridCode.IsArity r (c .unit y z w)) :
    UpperGridCode.IsArity r (upperGridProduct r .unit D B d c u f) := by
  unfold upperGridProduct
  erw [(carrierGridQuantifiers (r + 2) 1).single]
  change UpperGridCode.IsArity r ((carrierGridQuantifiers (r + 2) 1).code (D .unit) _)
  have hall (E : (carrierGrid (r + 3) 1).Code) (he : E = .small .unit)
      (g : (carrierGrid (r + 3) 1).El E → UpperGridCode r)
      (hg : ∀ y, UpperGridCode.IsArity r (g y)) :
      UpperGridCode.IsArity r ((carrierGridQuantifiers (r + 2) 1).code E g) := by
    subst E
    erw [(carrierGridQuantifiers (r + 2) 1).single]
    exact hg _
  apply hall _ hD
  intro y
  exact upperGridArrow_isArity (hd _) (hc _ _ _)

/-- Formation in a source universe controls the exact code image. -/
def UpperGridForm (r : Nat) (s : Srt) (C : UpperGridCode r) : Prop :=
  if sortRank s < r + 2 then C = .small (.small .unit)
  else if sortRank s = r + 2 then UpperGridCode.IsArity r C
  else if sortRank s = r + 3 then C.IsSmall else True

theorem UpperGridForm.lower (h : UpperGridForm r s C) (hs : sortRank s < r + 2) :
    C = .small (.small .unit) := by simpa only [UpperGridForm, if_pos hs] using h

theorem UpperGridForm.arity (h : UpperGridForm r s C) (hs : sortRank s ≤ r + 2) :
    UpperGridCode.IsArity r C := by
  by_cases hl : sortRank s < r + 2
  · exact ⟨.unit, h.lower hl⟩
  · have he : sortRank s = r + 2 := by omega
    simpa only [UpperGridForm, if_neg hl, if_pos he] using h

theorem UpperGridForm.small (h : UpperGridForm r s C) (hs : sortRank s ≤ r + 3) : C.IsSmall := by
  by_cases hl : sortRank s ≤ r + 2
  · exact (h.arity hl).small
  · have he : sortRank s = r + 3 := by omega
    have hn : ¬sortRank s < r + 2 := by omega
    have hn' : sortRank s ≠ r + 2 := by omega
    simpa only [UpperGridForm, if_neg hn, if_neg hn', if_pos he] using h

theorem upperGridDecode_form (r : Nat) (s : Srt) (k : Arity) (v : UpperGridValue r)
    (u : ShapeValue) (f : UpperGridValue r) : UpperGridForm r s (upperGridDecode r (some s) k v u f) := by
  classical
  by_cases hl : sortRank s < r + 2
  · have hn : sortRank s ≠ r + 2 := by omega
    have hn' : sortRank s ≠ r + 3 := by omega
    simp only [UpperGridForm, if_pos hl, upperGridDecode, Option.map_some, Option.some.injEq,
      if_neg hn, if_neg hn']
    erw [if_neg hn, if_neg hn']
  · by_cases he : sortRank s = r + 2
    · simp only [UpperGridForm, if_neg hl, if_pos he, upperGridDecode, Option.map_some,
        Option.some.injEq]
      erw [if_pos he]
      exact ⟨_, rfl⟩
    · by_cases he' : sortRank s = r + 3
      · simp only [UpperGridForm, if_neg hl, if_neg he, if_pos he', upperGridDecode, Option.map_some,
          Option.some.injEq]
        erw [if_neg he, if_pos he']
        exact ⟨_, rfl⟩
      · simp only [UpperGridForm, if_neg hl, if_neg he, if_neg he']

theorem upperGridSort_form (r : Nat) (h : Ax s s') (u : ShapeValue) (f : UpperGridValue r) :
    UpperGridForm r s' (upperGridSort r s u f) := by
  classical
  have hr : sortRank s' = sortRank s + 1 := by cases h <;> rfl
  by_cases hl : sortRank s' < r + 2
  · have h1 : sortRank s ≠ r + 1 := by omega
    have h2 : sortRank s ≠ r + 2 := by omega
    have h3 : sortRank s ≠ r + 3 := by omega
    simp only [UpperGridForm, if_pos hl, upperGridSort]
    erw [if_neg h1, if_neg h2, if_neg h3]
  · by_cases he : sortRank s' = r + 2
    · have h1 : sortRank s = r + 1 := by omega
      simp only [UpperGridForm, if_neg hl, if_pos he, upperGridSort]
      erw [if_pos h1]
      exact ⟨.prop, rfl⟩
    · by_cases he' : sortRank s' = r + 3
      · have h1 : sortRank s ≠ r + 1 := by omega
        have h2 : sortRank s = r + 2 := by omega
        simp only [UpperGridForm, if_neg hl, if_neg he, if_pos he', upperGridSort]
        erw [if_neg h1, if_pos h2]
        exact ⟨_, rfl⟩
      · simp only [UpperGridForm, if_neg hl, if_neg he, if_neg he']

theorem firstGridShape_small (h : BoundedTyping (r + 3) Γ A (.srt s))
    (hs : sortRank s ≤ sortRank (.type (r + 1))) (hρ : ShapeContext (.type (r + 1)) Γ ρ) :
    firstGridShape r Γ ρ A u = .small (nextArity (r + 3) (r + 1) Γ ρ A) :=
  congrArg (firstGridCode r) (middleShape_small h hs rfl hρ)

/-- The lower-carrier factorization is proved from source formation at every
bound at least four, including impredicative products over arbitrary domains. -/
theorem upperGridSemantics_form {r : Nat} {Γ : List Tm} {A : Tm} {s : Srt}
    {ρ : Nat → ShapeValue} {δ : Nat → UpperGridValue r} {u : ShapeValue} {f : UpperGridValue r}
    (h : BoundedTyping (r + 4) Γ A (.srt s))
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    UpperGridForm r s ((upperGridSemantics r Γ ρ δ A).2 u f) := by
  induction A generalizing Γ s ρ δ u f with
  | var j =>
    change UpperGridForm r s (upperGridDecode r (typeSort (r + 4) Γ (.var j)) _ _ u f)
    rw [typeSort_eq h]
    exact upperGridDecode_form _ _ _ _ _ _
  | srt t =>
    obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    exact upperGridSort_form r ha u f
  | app g a =>
    change UpperGridForm r s (upperGridDecode r (typeSort (r + 4) Γ (.app g a)) _ _ u f)
    rw [typeSort_eq h]
    exact upperGridDecode_form _ _ _ _ _ _
  | lam D b =>
    obtain ⟨B, s', hPi, hb, hr, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | pi D B ihD ihB =>
    obtain ⟨sD, sB, s', hD, hB, hr, hsD, hsB, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    rw [upperGridSemantics]
    dsimp only
    unfold upperGridCanonical
    by_cases hl : sortRank s < r + 2
    · rw [UpperGridForm, if_pos hl]
      apply upperGridProduct_trivial
      intro x hx y hy z w
      exact (ihB hB (hρ.up hx)).lower (Nat.lt_of_le_of_lt (rule_codomain_le hr) hl)
    · by_cases he : sortRank s = r + 2
      · rw [UpperGridForm, if_neg hl, if_pos he]
        have hd : sortRank sD ≤ sortRank s := by
          cases s with
          | prop => simp only [sortRank] at he; omega
          | type j => exact rule_predicative_domain hr
        have hb := rule_codomain_le hr
        have hda : arityAt (.type (r + 2)) D = .unit :=
          hD.below_top_kind rfl (by change sortRank sD < r + 4; omega)
        rw [hda]
        apply upperGridProduct_isArity
        · exact firstGridShape_lower hD (by change sortRank sD < r + 3; omega)
        · intro y; exact (ihD hD hρ).arity (by omega)
        · intro y z w; exact (ihB hB (hρ.up hda.symm)).arity (by omega)
      · by_cases he' : sortRank s = r + 3
        · rw [UpperGridForm, if_neg hl, if_neg he, if_pos he']
          have hd : sortRank sD ≤ sortRank s := by
            cases s with
            | prop => simp only [sortRank] at he'; omega
            | type j => exact rule_predicative_domain hr
          have hb := rule_codomain_le hr
          have hda : arityAt (.type (r + 2)) D = .unit :=
            hD.below_top_kind rfl (by change sortRank sD < r + 4; omega)
          rw [hda]
          apply upperGridProduct_isSmall (k := nextArity (r + 4) (r + 2) Γ ρ D)
          · exact firstGridShape_small hD (by change sortRank sD ≤ r + 3; omega) hρ
          · intro y; exact (ihD hD hρ).small (by omega)
          · intro y z w; exact (ihB hB (hρ.up hda.symm)).small (by omega)
        · simp only [UpperGridForm, if_neg hl, if_neg he, if_neg he']

end Submission.Helpers
