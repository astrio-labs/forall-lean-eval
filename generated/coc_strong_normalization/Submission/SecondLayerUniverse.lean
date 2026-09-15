import Submission.SecondLayerForms

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

variable {r : Nat} {δ : Nat → UpperGridValue (r + 1)} {ε : Nat → SecondLayerValue r}
  {u : ShapeValue} {f : UpperGridValue (r + 1)} {g : SecondLayerValue r}

noncomputable def secondLayerSortCode (r : Nat) (s : Srt) (k : Arity) (m : UpperGridValue (r + 1)) :
    (carrierGrid (r + 4) 2).Code := upperGridSort (r + 1) s ⟨.prop, k⟩ m

theorem inferredSecondGrid_sort (h : BoundedTyping (r + 5) Γ t (.srt s))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    inferredSecondGrid (r + 1) Γ ρ δ t = secondLayerSortCode r s
      (nextArity (r + 5) (r + 3) Γ ρ t) (upperGridSemantics (r + 1) Γ ρ δ t).1 := by
  rw [inferredSecondGrid_eq h hρ hδ]
  rfl

theorem secondLayerEncode_code (r : Nat) (s : Srt) (k : Arity) (m : UpperGridValue (r + 1))
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r) :
    (secondLayerEncode r (some s) k m C).code = secondLayerSortCode r s k m := by
  classical
  unfold secondLayerEncode secondLayerSortCode upperGridSort
  simp only [Option.map_some, Option.some.injEq]
  split
  · rename_i h
    erw [if_pos h]
  · rename_i h
    erw [if_neg h]
    split
    · rename_i h'
      erw [if_pos h']
    · rename_i h'
      erw [if_neg h']
      split
      · rename_i h''
        erw [if_pos h'']
        rfl
      · rename_i h''
        erw [if_neg h'']
        rfl

theorem secondLayerEncode_typed_code (h : BoundedTyping (r + 5) Γ t (.srt s))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ)
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r) :
    (secondLayerEncode r (some s) (nextArity (r + 5) (r + 3) Γ ρ t)
      (upperGridSemantics (r + 1) Γ ρ δ t).1 C).code = inferredSecondGrid (r + 1) Γ ρ δ t := by
  rw [secondLayerEncode_code, inferredSecondGrid_sort h hρ hδ]

theorem secondLayerSemantics_pi_value (h : BoundedTyping (r + 5) Γ (.pi A B) (.srt s))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε (.pi A B)).1 = secondLayerEncode r (some s)
      (nextArity (r + 5) (r + 3) Γ ρ (.pi A B)) (upperGridSemantics (r + 1) Γ ρ δ (.pi A B)).1
      (secondLayerSemantics r Γ ρ δ ε (.pi A B)).2 := by
  change TowerValue.force _ (secondLayerEncode _ _ _ _ _) = _
  rw [typeSort_eq h]
  exact TowerValue.force_eq _ (secondLayerEncode_typed_code h hρ hδ _)

theorem secondLayerSemantics_sort_value (h : BoundedTyping (r + 5) Γ (.srt t) (.srt s))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) (hδ : FirstGridContext (r + 2) Γ ρ δ) :
    (secondLayerSemantics r Γ ρ δ ε (.srt t)).1 = secondLayerEncode r (some s)
      (nextArity (r + 5) (r + 3) Γ ρ (.srt t)) (upperGridSemantics (r + 1) Γ ρ δ (.srt t)).1
      (secondLayerSort r t) := by
  change TowerValue.force _ (secondLayerEncode _ _ _ _ _) = _
  rw [typeSort_eq h]
  exact TowerValue.force_eq _ (secondLayerEncode_typed_code h hρ hδ _)

theorem secondLayerDecode_encode_low (r : Nat) (k : Arity) (m : UpperGridValue (r + 1))
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerDecode r (some (.type (r + 1))) k m (secondLayerEncode r (some (.type (r + 1))) k m C) u f g =
      .small (.small (.small (secondLayerAsArity r (C .unit (upperGridUnit (r + 1)) (secondLayerUnit r))))) := by
  classical
  unfold secondLayerDecode secondLayerEncode
  simp only [Option.map_some, sortRank, ↓reduceIte]
  exact congrArg (fun a : Arity => (LayerCode.small (LayerCode.small (LayerCode.small a)) : SecondLayerCode r))
    (TowerValue.cast_mk (S := carrierGrid (r + 4) 2) (.small (.small .prop)) _)

theorem secondLayerDecode_encode_middle (r : Nat) (k : Arity) (m : UpperGridValue (r + 1))
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerDecode r (some (.type (r + 2))) k m (secondLayerEncode r (some (.type (r + 2))) k m C) u f g =
      .small (.small (C .unit (upperGridUnit (r + 1))
        (g.force (.small (.small (m.cast (.small .prop)))))).asSmall.asSmall) := by
  classical
  have hn : r + 3 ≠ r + 2 := by omega
  unfold secondLayerDecode secondLayerEncode
  simp only [Option.map_some, sortRank, Option.some.injEq]
  erw [if_neg hn, if_neg hn]
  simp only [ite_true]
  exact congrArg (fun a : (carrierGrid (r + 2) 1).Code => (LayerCode.small (LayerCode.small a) : SecondLayerCode r))
    (congrFun (TowerValue.cast_mk (S := carrierGrid (r + 4) 2) (.small (.atom (m.cast (.small .prop)))) _)
      (g.cast (.small (.small (m.cast (.small .prop))))))

theorem secondLayerDecode_encode_high (r : Nat) (k : Arity) (m : UpperGridValue (r + 1))
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerDecode r (some (.type (r + 3))) k m (secondLayerEncode r (some (.type (r + 3))) k m C) u f g =
      .small (C .unit (f.force (.small k))
        (g.force (.small (m.cast (.atom k) (f.cast (.small k)))))).asSmall := by
  classical
  have hn : r + 4 ≠ r + 2 := by omega
  have hn' : r + 4 ≠ r + 3 := by omega
  unfold secondLayerDecode secondLayerEncode
  simp only [Option.map_some, sortRank, Option.some.injEq]
  erw [if_neg hn, if_neg hn', if_neg hn, if_neg hn']
  simp only [ite_true]
  erw [TowerValue.cast_mk, CarrierObject.roundtrip]
  rfl

theorem TowerValue.cast_force {S : CarrierSystem} (v : TowerValue S) (A : S.Code) :
    (v.force A).cast A = v.cast A := TowerValue.cast_mk A (v.cast A)

theorem secondLayerForce_unit (r : Nat) (g : SecondLayerValue r) :
    TowerValue.force (S := carrierGrid (r + 4) 2) (.small (.small .unit)) g = secondLayerUnit r := by
  exact congrArg (TowerValue.mk (S := carrierGrid (r + 4) 2) (.small (.small .unit)))
    (show g.cast (.small (.small .unit)) = () from @Subsingleton.elim Unit inferInstance _ _)

theorem secondLayerCanonical_unit (r : Nat) (D : (carrierGrid (r + 4) 1).Code)
    (d : ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code)
    (C : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r)
    (u : ShapeValue) (f : UpperGridValue (r + 1)) (g : SecondLayerValue r) :
    secondLayerCanonical r .unit (fun _ => D) d C u f g = C .unit (f.force D) (g.force (d .unit (f.force D))) := by
  unfold secondLayerCanonical
  dsimp only
  rw [ShapeValue.eq_unit (u.force .unit) rfl]

theorem secondLayer_small_asArity {C : SecondLayerCode r} (h : SecondLayerCode.IsArity r C) :
    LayerCode.small (LayerCode.small (LayerCode.small (secondLayerAsArity r C))) = C := by
  obtain ⟨a, rfl⟩ := h; rfl

theorem secondLayer_small_asSmallTwo {C : SecondLayerCode r} (h : SecondLayerCode.IsSmallTwo r C) :
    LayerCode.small (LayerCode.small C.asSmall.asSmall) = C := ((SecondLayerCode.isSmallTwo_iff C).mp h).symm

theorem secondLayer_small_asSmall {C : SecondLayerCode r} (h : C.IsSmall) : LayerCode.small C.asSmall = C :=
  ((LayerCode.isSmall_iff C).mp h).symm

theorem secondGridShape_lower (h : BoundedTyping (r + 5) Γ A (.srt s)) (hs : sortRank s < r + 3)
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) :
    secondGridShape (r + 1) Γ ρ δ A u f = .small (.small .unit) := (upperGridSemantics_form h hρ).lower hs

theorem secondGridShape_middle (h : BoundedTyping (r + 5) Γ A (.srt (.type (r + 2))))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) :
    secondGridShape (r + 1) Γ ρ δ A u f =
      .small (.small ((upperGridSemantics (r + 1) Γ ρ δ A).1.cast (.small .prop))) := by
  have he := upperGridSemantics_decode (δ := δ) (u := u) (f := f) h (by change r + 3 < r + 5; omega) hρ
  unfold upperGridDecode at he
  simp only [Option.map_some, sortRank, ↓reduceIte] at he
  exact he

theorem secondGridShape_high (h : BoundedTyping (r + 5) Γ A (.srt (.type (r + 3))))
    (hρ : ShapeContext (.type (r + 3)) Γ ρ) :
    secondGridShape (r + 1) Γ ρ δ A u f =
      .small ((upperGridSemantics (r + 1) Γ ρ δ A).1.cast (.atom (nextArity (r + 5) (r + 3) Γ ρ A))
        (f.cast (.small (nextArity (r + 5) (r + 3) Γ ρ A)))) := by
  have he := upperGridSemantics_decode (δ := δ) (u := u) (f := f) h (by change r + 4 < r + 5; omega) hρ
  have hn : r + 4 ≠ r + 3 := by omega
  unfold upperGridDecode at he
  simp only [Option.map_some, sortRank, Option.some.injEq] at he
  erw [if_neg hn, if_pos True.intro] at he
  exact he

end Submission.Helpers
