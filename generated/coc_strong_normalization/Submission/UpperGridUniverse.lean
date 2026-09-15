import Submission.UpperGridForms

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def upperGridSortCode (r : Nat) (s : Srt) (k : Arity) : (carrierGrid (r + 3) 1).Code :=
  if sortRank s = r + 2 then .small .prop else if sortRank s = r + 3 then .atom k else .small .unit

theorem firstGridShape_sort (hw : BoundedWf (r + 4) Γ) (hs : sortRank s ≤ r + 4) :
    firstGridShape (r + 1) Γ ρ (.srt s) u = upperGridSortCode r s u.asArity := by
  classical
  by_cases hl : sortRank s < r + 2
  · obtain ⟨s', ha⟩ : ∃ s', Ax s s' := by cases s with
      | prop => exact ⟨.type 0, .prop⟩
      | type j => exact ⟨.type (j + 1), .type j⟩
    have hr := ax_rank ha
    have h : BoundedTyping (r + 4) Γ (.srt s) (.srt s') := .srt hw ha (by omega) (by omega)
    rw [firstGridShape_lower h (by change sortRank s' < r + 3; omega)]
    have hn : sortRank s ≠ r + 2 := by omega
    have hn' : sortRank s ≠ r + 3 := by omega
    unfold upperGridSortCode
    erw [if_neg hn, if_neg hn']
  · by_cases he : sortRank s = r + 2
    · have hst : s = .type (r + 1) := sortRank_injective he
      subst s
      have h : BoundedTyping (r + 4) Γ (.srt (.type (r + 1))) (.srt (.type (r + 2))) :=
        .srt hw (.type _) (by change r + 2 ≤ r + 4; omega) (by change r + 3 ≤ r + 4; omega)
      rw [firstGridShape_at_universe h, nextArity_predecessor hw (.type (r + 1)) rfl]
      simp only [upperGridSortCode, sortRank, ↓reduceIte]
      rfl
    · by_cases he' : sortRank s = r + 3
      · have hst : s = .type (r + 2) := sortRank_injective he'
        subst s
        rw [firstGridShape_top_sort hw]
        unfold upperGridSortCode
        erw [if_neg he, if_pos he']
      · have ht : r + 4 ≤ sortRank s := by omega
        have hshape := middleShape_untypable_sort (Γ := Γ) (ρ := ρ) (v := u) ht
          (show sortRank (.type (r + 2)) + 1 = r + 4 from rfl)
        have heq := congrArg (firstGridCode (r + 1)) hshape
        exact heq.trans (by unfold upperGridSortCode; erw [if_neg he, if_neg he']; rfl)

theorem inferredFirstGrid_sort (h : BoundedTyping (r + 4) Γ t (.srt s))
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    inferredFirstGrid (r + 1) Γ ρ t = upperGridSortCode r s (nextArity (r + 4) (r + 2) Γ ρ t) := by
  rw [inferredFirstGrid_eq h hρ]
  exact firstGridShape_sort h.wf h.sort_bound

theorem upperGridEncode_code (r : Nat) (s : Srt) (k : Arity)
    (C : ShapeValue → UpperGridValue r → UpperGridCode r) :
    (upperGridEncode r (some s) k C).code = upperGridSortCode r s k := by
  classical
  unfold upperGridEncode upperGridSortCode
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
      rfl

theorem upperGridEncode_typed_code (h : BoundedTyping (r + 4) Γ t (.srt s))
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) (C : ShapeValue → UpperGridValue r → UpperGridCode r) :
    (upperGridEncode r (some s) (nextArity (r + 4) (r + 2) Γ ρ t) C).code =
      inferredFirstGrid (r + 1) Γ ρ t := by
  rw [upperGridEncode_code, inferredFirstGrid_sort h hρ]

theorem upperGridSemantics_pi_value {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A B : Tm}
    (h : BoundedTyping (r + 4) Γ (.pi A B) (.srt s)) (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ (.pi A B)).1 = upperGridEncode r (some s)
      (nextArity (r + 4) (r + 2) Γ ρ (.pi A B)) (upperGridSemantics r Γ ρ δ (.pi A B)).2 := by
  rw [upperGridSemantics]
  dsimp only
  rw [typeSort_eq h]
  exact TowerValue.force_eq _ (upperGridEncode_typed_code h hρ _)

theorem upperGridSemantics_sort_value {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {s t : Srt}
    (h : BoundedTyping (r + 4) Γ (.srt t) (.srt s)) (hρ : ShapeContext (.type (r + 2)) Γ ρ) :
    (upperGridSemantics r Γ ρ δ (.srt t)).1 = upperGridEncode r (some s)
      (nextArity (r + 4) (r + 2) Γ ρ (.srt t)) (upperGridSort r t) := by
  rw [upperGridSemantics]
  dsimp only
  rw [typeSort_eq h]
  exact TowerValue.force_eq _ (upperGridEncode_typed_code h hρ _)

theorem upperGridForce_unit (r : Nat) (f : UpperGridValue r) :
    TowerValue.force (S := carrierGrid (r + 3) 1) (.small .unit) f = upperGridUnit r := by
  exact congrArg (TowerValue.mk (S := carrierGrid (r + 3) 1) (.small .unit))
    (show f.cast (.small .unit) = () from @Subsingleton.elim Unit inferInstance _ _)

theorem TowerValue.force_force {S : CarrierSystem} (f : TowerValue S) (D : S.Code) :
    TowerValue.force D (TowerValue.force D f) = TowerValue.force D f :=
  TowerValue.force_eq _ rfl

theorem upperGridCanonical_unit (r : Nat) (D : (carrierGrid (r + 3) 1).Code)
    (C : ShapeValue → UpperGridValue r → UpperGridCode r) (u : ShapeValue) (f : UpperGridValue r) :
    upperGridCanonical r .unit (fun _ => D) C u f = C .unit (f.force D) := by
  unfold upperGridCanonical
  rw [ShapeValue.eq_unit (u.force .unit) rfl]

theorem upperGrid_small_asArity {C : UpperGridCode r} (h : UpperGridCode.IsArity r C) :
    LayerCode.small (LayerCode.small (upperGridAsArity r C)) = C := by
  obtain ⟨a, rfl⟩ := h
  rfl

theorem upperGrid_small_asSmall {C : UpperGridCode r} (h : C.IsSmall) : LayerCode.small C.asSmall = C :=
  ((LayerCode.isSmall_iff C).mp h).symm

theorem upperGridDecode_encode_low (r : Nat) (k : Arity)
    (C : ShapeValue → UpperGridValue r → UpperGridCode r) (u : ShapeValue) (f : UpperGridValue r) :
    upperGridDecode r (some (.type (r + 1))) k (upperGridEncode r (some (.type (r + 1))) k C) u f =
      .small (.small (upperGridAsArity r (C .unit (upperGridUnit r)))) := by
  classical
  unfold upperGridDecode upperGridEncode
  simp only [Option.map_some, sortRank, ↓reduceIte]
  exact congrArg (fun a : Arity => (LayerCode.small (LayerCode.small a) : UpperGridCode r))
    (TowerValue.cast_mk (S := carrierGrid (r + 3) 1) (.small .prop) _)

theorem upperGridDecode_encode_high (r : Nat) (k : Arity)
    (C : ShapeValue → UpperGridValue r → UpperGridCode r) (u : ShapeValue) (f : UpperGridValue r) :
    upperGridDecode r (some (.type (r + 2))) k (upperGridEncode r (some (.type (r + 2))) k C) u f =
      .small (C .unit (f.force (.small k))).asSmall := by
  classical
  have hn : r + 3 ≠ r + 2 := by omega
  unfold upperGridDecode upperGridEncode
  simp only [Option.map_some, sortRank, Option.some.injEq]
  erw [if_neg hn]
  simp only [ite_true]
  erw [if_neg hn]
  exact congrArg LayerCode.small (congrFun (TowerValue.cast_mk (S := carrierGrid (r + 3) 1)
    (.atom k) (fun z => (C .unit ⟨.small k, z⟩).asSmall)) (f.cast (.small k)))

end Submission.Helpers
