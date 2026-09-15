import Submission.SecondLayerSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

variable {r : Nat}
  {D : ShapeValue → (carrierGrid (r + 4) 1).Code}
  {B : ShapeValue → ShapeValue → (carrierGrid (r + 4) 1).Code}
  {d : ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code}
  {c : ShapeValue → UpperGridValue (r + 1) → ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code}
  {E : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r}
  {F : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r →
    ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r}
  {u : ShapeValue} {f : UpperGridValue (r + 1)} {g : SecondLayerValue r}

def SecondLayerCode.IsArity (r : Nat) (C : SecondLayerCode r) : Prop := ∃ a : Arity, C = .small (.small (.small a))
def SecondLayerCode.IsSmallTwo (r : Nat) (C : SecondLayerCode r) : Prop :=
  ∃ a : (carrierGrid (r + 2) 1).Code, C = .small (.small a)

theorem SecondLayerCode.IsArity.smallTwo {C : SecondLayerCode r} (h : IsArity r C) : IsSmallTwo r C := by
  obtain ⟨a, rfl⟩ := h; exact ⟨.small a, rfl⟩

theorem SecondLayerCode.IsSmallTwo.small {C : SecondLayerCode r} (h : IsSmallTwo r C) : C.IsSmall := by
  obtain ⟨a, rfl⟩ := h; exact ⟨.small a, rfl⟩

theorem SecondLayerCode.isSmallTwo_iff (C : SecondLayerCode r) :
    IsSmallTwo r C ↔ C = .small (.small C.asSmall.asSmall) := by
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro h; exact ⟨_, h⟩

theorem secondLayerArrow_isArity {A B : SecondLayerCode r}
    (hA : SecondLayerCode.IsArity r A) (hB : SecondLayerCode.IsArity r B) :
    SecondLayerCode.IsArity r ((carrierGridArrows (r + 4) 3).code A B) := by
  obtain ⟨a, rfl⟩ := hA; obtain ⟨b, rfl⟩ := hB
  refine ⟨a.arrow b, ?_⟩
  erw [carrierGrid_arrow_small (r + 3) 2, carrierGrid_arrow_small (r + 2) 1, carrierGrid_arrow_small (r + 1) 0]
  rfl

theorem secondLayerArrow_isSmallTwo {A B : SecondLayerCode r}
    (hA : SecondLayerCode.IsSmallTwo r A) (hB : SecondLayerCode.IsSmallTwo r B) :
    SecondLayerCode.IsSmallTwo r ((carrierGridArrows (r + 4) 3).code A B) := by
  obtain ⟨a, rfl⟩ := hA; obtain ⟨b, rfl⟩ := hB
  refine ⟨(carrierGridArrows (r + 2) 1).code a b, ?_⟩
  erw [carrierGrid_arrow_small (r + 3) 2, carrierGrid_arrow_small (r + 2) 1]

theorem CarrierQuantifiers.single_property (Q : CarrierQuantifiers I S)
    {P : S.Code → Prop} (A : I.Code) (B : I.El A → S.Code)
    (ha : A = I.defaultCode) (h : ∀ x, P (B x)) : P (Q.code A B) := by
  subst A
  rw [Q.single]
  exact h _

theorem secondLayerAll_isSmall (A : (carrierGrid (r + 4) 2).Code)
    (B : (carrierGrid (r + 4) 2).El A → SecondLayerCode r)
    (ha : A.IsSmall) (h : ∀ x, (B x).IsSmall) :
    ((carrierGridQuantifiers (r + 3) 2).code A B).IsSmall := by
  obtain ⟨a, rfl⟩ := ha
  exact LayerCode.compactAll_isSmall (carrierGridQuantifiers (r + 2) 1)
    (carrierGridTerminal (r + 3) 1) (carrierGridTerminal (r + 3) 2) a B h

theorem secondLayerAll_isSmallTwo (A : (carrierGrid (r + 4) 2).Code)
    (B : (carrierGrid (r + 4) 2).El A → SecondLayerCode r)
    (ha : UpperGridCode.IsArity (r + 1) A) (h : ∀ x, SecondLayerCode.IsSmallTwo r (B x)) :
    SecondLayerCode.IsSmallTwo r ((carrierGridQuantifiers (r + 3) 2).code A B) := by
  obtain ⟨a, rfl⟩ := ha
  have he : B = fun x => .small (.small (B x).asSmall.asSmall) :=
    funext (fun x => (SecondLayerCode.isSmallTwo_iff (B x)).mp (h x))
  erw [he, carrierGrid_all_small (r + 2) 1, carrierGrid_all_small (r + 1) 0]
  exact ⟨_, rfl⟩

theorem secondLayerHorizontal_small (a : Arity) :
    (carrierGridHorizontal (r + 4) 1 (by omega)).code (.small a) = .small (.small a) := by
  simp only [carrierGridHorizontal, CarrierRepresentation.ofEq, LayerCode.representation,
    LayerCode.representCode, LayerCode.smallRepresentation]
  rfl

theorem secondLayerProduct_trivial (a : Arity)
    (hF : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y →
      ∀ v w q, F x y z v w q = .small (.small (.small .unit))) :
    secondLayerProduct r a D B d c E F u f g = .small (.small (.small .unit)) := by
  unfold secondLayerProduct
  apply (carrierGridQuantifiers (r + 3) 2).trivial
  intro x
  apply (carrierGridQuantifiers (r + 3) 2).trivial
  intro y
  apply (carrierGridQuantifiers (r + 3) 2).trivial
  intro z
  dsimp only
  erw [hF _ rfl _ rfl _ rfl]
  exact (carrierGridArrows (r + 4) 3).trivial _

theorem secondLayerProduct_isSmall (k : Arity)
    (hD : D .unit = .small k) (hd : ∀ y, (d .unit y).IsSmall)
    (hE : ∀ y z, (E .unit y z).IsSmall) (hF : ∀ y z v w q, (F .unit y z v w q).IsSmall) :
    (secondLayerProduct r .unit D B d c E F u f g).IsSmall := by
  unfold secondLayerProduct
  erw [(carrierGridQuantifiers (r + 3) 2).single]
  apply secondLayerAll_isSmall
  · erw [hD]; exact ⟨.small k, secondLayerHorizontal_small k⟩
  · intro y
    apply secondLayerAll_isSmall _ _ (hd _)
    intro z
    exact LayerCode.compactArrow_isSmall (carrierGridArrows (r + 3) 2) (hE _ _) (hF _ _ _ _ _)

theorem secondLayerProduct_isSmallTwo
    (hD : D .unit = .small .unit) (hd : ∀ y, UpperGridCode.IsArity (r + 1) (d .unit y))
    (hE : ∀ y z, SecondLayerCode.IsSmallTwo r (E .unit y z))
    (hF : ∀ y z v w q, SecondLayerCode.IsSmallTwo r (F .unit y z v w q)) :
    SecondLayerCode.IsSmallTwo r (secondLayerProduct r .unit D B d c E F u f g) := by
  unfold secondLayerProduct
  erw [(carrierGridQuantifiers (r + 3) 2).single]
  apply (carrierGridQuantifiers (r + 3) 2).single_property
  · erw [hD]; exact secondLayerHorizontal_small .unit
  · intro y
    apply secondLayerAll_isSmallTwo _ _ (hd _)
    intro z
    exact secondLayerArrow_isSmallTwo (hE _ _) (hF _ _ _ _ _)

theorem secondLayerProduct_isArity
    (hD : D .unit = .small .unit) (hd : ∀ y, d .unit y = .small (.small .unit))
    (hE : ∀ y z, SecondLayerCode.IsArity r (E .unit y z))
    (hF : ∀ y z v w q, SecondLayerCode.IsArity r (F .unit y z v w q)) :
    SecondLayerCode.IsArity r (secondLayerProduct r .unit D B d c E F u f g) := by
  unfold secondLayerProduct
  erw [(carrierGridQuantifiers (r + 3) 2).single]
  apply (carrierGridQuantifiers (r + 3) 2).single_property
  · erw [hD]; exact secondLayerHorizontal_small .unit
  · intro y
    apply (carrierGridQuantifiers (r + 3) 2).single_property _ _ (hd _)
    intro z
    exact secondLayerArrow_isArity (hE _ _) (hF _ _ _ _ _)

/-- The three proper universe ranks occupy three exact nested code images. -/
def SecondLayerForm (r : Nat) (s : Srt) (C : SecondLayerCode r) : Prop :=
  if sortRank s < r + 2 then C = .small (.small (.small .unit))
  else if sortRank s = r + 2 then SecondLayerCode.IsArity r C
  else if sortRank s = r + 3 then SecondLayerCode.IsSmallTwo r C
  else if sortRank s = r + 4 then C.IsSmall else True

theorem SecondLayerForm.lower {C : SecondLayerCode r} (h : SecondLayerForm r s C) (hs : sortRank s < r + 2) :
    C = .small (.small (.small .unit)) := by simpa only [SecondLayerForm, if_pos hs] using h

theorem SecondLayerForm.arity {C : SecondLayerCode r} (h : SecondLayerForm r s C) (hs : sortRank s ≤ r + 2) :
    SecondLayerCode.IsArity r C := by
  by_cases hl : sortRank s < r + 2
  · exact ⟨.unit, h.lower hl⟩
  · have he : sortRank s = r + 2 := by omega
    simpa only [SecondLayerForm, if_neg hl, if_pos he] using h

theorem SecondLayerForm.smallTwo {C : SecondLayerCode r} (h : SecondLayerForm r s C) (hs : sortRank s ≤ r + 3) :
    SecondLayerCode.IsSmallTwo r C := by
  by_cases hl : sortRank s ≤ r + 2
  · exact (h.arity hl).smallTwo
  · have he : sortRank s = r + 3 := by omega
    have hn : ¬sortRank s < r + 2 := by omega
    have hn' : sortRank s ≠ r + 2 := by omega
    simpa only [SecondLayerForm, if_neg hn, if_neg hn', if_pos he] using h

theorem SecondLayerForm.small {C : SecondLayerCode r} (h : SecondLayerForm r s C) (hs : sortRank s ≤ r + 4) : C.IsSmall := by
  by_cases hl : sortRank s ≤ r + 3
  · exact (h.smallTwo hl).small
  · have he : sortRank s = r + 4 := by omega
    have hn : ¬sortRank s < r + 2 := by omega
    have hn' : sortRank s ≠ r + 2 := by omega
    have hn'' : sortRank s ≠ r + 3 := by omega
    simpa only [SecondLayerForm, if_neg hn, if_neg hn', if_neg hn'', if_pos he] using h

theorem secondLayerDecode_form (r : Nat) (s : Srt) (k : Arity) (m : UpperGridValue (r + 1))
    (v : SecondLayerValue r) (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    SecondLayerForm r s (secondLayerDecode r (some s) k m v u f g) := by
  classical
  by_cases hl : sortRank s < r + 2
  · have h2 : sortRank s ≠ r + 2 := by omega
    have h3 : sortRank s ≠ r + 3 := by omega
    have h4 : sortRank s ≠ r + 4 := by omega
    simp only [SecondLayerForm, if_pos hl, secondLayerDecode, Option.map_some, Option.some.injEq]
    erw [if_neg h2, if_neg h3, if_neg h4]
  · by_cases h2 : sortRank s = r + 2
    · simp only [SecondLayerForm, if_neg hl, if_pos h2, secondLayerDecode, Option.map_some, Option.some.injEq]
      erw [if_pos h2]
      exact ⟨_, rfl⟩
    · by_cases h3 : sortRank s = r + 3
      · simp only [SecondLayerForm, if_neg hl, if_neg h2, if_pos h3, secondLayerDecode, Option.map_some, Option.some.injEq]
        erw [if_neg h2, if_pos h3]
        exact ⟨_, rfl⟩
      · by_cases h4 : sortRank s = r + 4
        · simp only [SecondLayerForm, if_neg hl, if_neg h2, if_neg h3, if_pos h4, secondLayerDecode, Option.map_some, Option.some.injEq]
          erw [if_neg h2, if_neg h3, if_pos h4]
          exact ⟨_, rfl⟩
        · simp only [SecondLayerForm, if_neg hl, if_neg h2, if_neg h3, if_neg h4]

theorem secondLayerSort_form (r : Nat) (h : Ax s s')
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    SecondLayerForm r s' (secondLayerSort r s u f g) := by
  classical
  have hr : sortRank s' = sortRank s + 1 := by cases h <;> rfl
  by_cases hl : sortRank s' < r + 2
  · have h1 : sortRank s ≠ r + 1 := by omega
    have h2 : sortRank s ≠ r + 2 := by omega
    have h3 : sortRank s ≠ r + 3 := by omega
    have h4 : sortRank s ≠ r + 4 := by omega
    simp only [SecondLayerForm, if_pos hl, secondLayerSort]
    erw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  · by_cases h2 : sortRank s' = r + 2
    · have h1 : sortRank s = r + 1 := by omega
      simp only [SecondLayerForm, if_neg hl, if_pos h2, secondLayerSort]
      erw [if_pos h1]
      exact ⟨.prop, rfl⟩
    · by_cases h3 : sortRank s' = r + 3
      · have h1 : sortRank s ≠ r + 1 := by omega
        have h2' : sortRank s = r + 2 := by omega
        simp only [SecondLayerForm, if_neg hl, if_neg h2, if_pos h3, secondLayerSort]
        erw [if_neg h1, if_pos h2']
        exact ⟨_, rfl⟩
      · by_cases h4 : sortRank s' = r + 4
        · have h1 : sortRank s ≠ r + 1 := by omega
          have h2' : sortRank s ≠ r + 2 := by omega
          have h3' : sortRank s = r + 3 := by omega
          simp only [SecondLayerForm, if_neg hl, if_neg h2, if_neg h3, if_pos h4, secondLayerSort]
          erw [if_neg h1, if_neg h2', if_pos h3']
          exact ⟨_, rfl⟩
        · simp only [SecondLayerForm, if_neg hl, if_neg h2, if_neg h3, if_neg h4]

/-- Source formation supplies the nested universe factorization at every
bound `r + 5`, including impredicative products over arbitrary domains. -/
theorem secondLayerSemantics_form {r : Nat} {Γ : List Tm} {A : Tm} {s : Srt}
    {ρ : Nat → ShapeValue} {δ : Nat → UpperGridValue (r + 1)} {ε : Nat → SecondLayerValue r}
    {u : ShapeValue} {f : UpperGridValue (r + 1)} {g : SecondLayerValue r}
    (h : BoundedTyping (r + 5) Γ A (.srt s)) (hρ : ShapeContext (.type (r + 3)) Γ ρ) :
    SecondLayerForm r s ((secondLayerSemantics r Γ ρ δ ε A).2 u f g) := by
  induction A generalizing Γ s ρ δ ε u f g with
  | var j =>
    change SecondLayerForm r s (secondLayerDecode r (typeSort (r + 5) Γ (.var j)) _ _ _ u f g)
    rw [typeSort_eq h]
    exact secondLayerDecode_form _ _ _ _ _ _ _ _
  | srt t =>
    obtain ⟨s', ha, hr, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    exact secondLayerSort_form r ha u f g
  | app t a =>
    change SecondLayerForm r s (secondLayerDecode r (typeSort (r + 5) Γ (.app t a)) _ _ _ u f g)
    rw [typeSort_eq h]
    exact secondLayerDecode_form _ _ _ _ _ _ _ _
  | lam D b =>
    obtain ⟨B, s', hPi, hb, hr, hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | pi D B ihD ihB =>
    obtain ⟨sD, sB, s', hD, hB, hr, hsD, hsB, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    rw [secondLayerSemantics]
    dsimp only
    unfold secondLayerCanonical
    by_cases hl : sortRank s < r + 2
    · rw [SecondLayerForm, if_pos hl]
      apply secondLayerProduct_trivial
      intro x hx y hy z hz v w q
      exact (ihB hB (hρ.up hx)).lower (Nat.lt_of_le_of_lt (rule_codomain_le hr) hl)
    · have hd : sortRank sD ≤ sortRank s := by
        cases s with
        | prop => simp only [sortRank] at hl; omega
        | type j => exact rule_predicative_domain hr
      have hb := rule_codomain_le hr
      by_cases h2 : sortRank s = r + 2
      · rw [SecondLayerForm, if_neg hl, if_pos h2]
        have hda : arityAt (.type (r + 3)) D = .unit := hD.below_top_kind rfl (by change sortRank sD < r + 5; omega)
        rw [hda]
        apply secondLayerProduct_isArity
        · exact firstGridShape_lower hD (by change sortRank sD < r + 4; omega)
        · intro y; exact (upperGridSemantics_form hD hρ).lower (by omega)
        · intro y z; exact (ihD hD hρ).arity (by omega)
        · intro y z v w q; exact (ihB hB (hρ.up hda.symm)).arity (by omega)
      · by_cases h3 : sortRank s = r + 3
        · rw [SecondLayerForm, if_neg hl, if_neg h2, if_pos h3]
          have hda : arityAt (.type (r + 3)) D = .unit := hD.below_top_kind rfl (by change sortRank sD < r + 5; omega)
          rw [hda]
          apply secondLayerProduct_isSmallTwo
          · exact firstGridShape_lower hD (by change sortRank sD < r + 4; omega)
          · intro y; exact (upperGridSemantics_form hD hρ).arity (by omega)
          · intro y z; exact (ihD hD hρ).smallTwo (by omega)
          · intro y z v w q; exact (ihB hB (hρ.up hda.symm)).smallTwo (by omega)
        · by_cases h4 : sortRank s = r + 4
          · rw [SecondLayerForm, if_neg hl, if_neg h2, if_neg h3, if_pos h4]
            have hda : arityAt (.type (r + 3)) D = .unit := hD.below_top_kind rfl (by change sortRank sD < r + 5; omega)
            rw [hda]
            apply secondLayerProduct_isSmall (k := nextArity (r + 5) (r + 3) Γ ρ D)
            · exact firstGridShape_small hD (by change sortRank sD ≤ r + 4; omega) hρ
            · intro y; exact (upperGridSemantics_form hD hρ).small (by omega)
            · intro y z; exact (ihD hD hρ).small (by omega)
            · intro y z v w q; exact (ihB hB (hρ.up hda.symm)).small (by omega)
          · simp only [SecondLayerForm, if_neg hl, if_neg h2, if_neg h3, if_neg h4]

end Submission.Helpers
