import Submission.UniverseDecoderCausality

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem universeTypePrefix_congr (r k : Nat) (C D : CausalGridType (r + 1 + k))
    (d : Nat) (hd : d ≤ r + 1)
    (h : ∀ i hi, i ≤ d + k → C.code i hi = D.code i hi) :
    universeTypePrefix r k C d hd = universeTypePrefix r k D d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [universeTypePrefix, universeTypePrefix,
      ih (by omega) (fun i hi hil => h i hi (by omega)), h (d + 1 + k) (by omega) (Nat.le_refl _)]

theorem universeReify_proper_congr (r k : Nat) (C D : CausalGridType (r + 1 + k))
    (J K : CausalGridPredicate (r + 1 + k)) (d : Nat) (hd : d ≤ r)
    (h : ∀ i hi, i ≤ d + 1 + k → C.code i hi = D.code i hi) :
    universeReify r k C J d = universeReify r k D K d := by
  rw [universeReify_proper r k C J d hd, universeReify_proper r k D K d hd]
  unfold universeTypeField
  rw [universeTypePrefix_congr r k C D d (by omega) (fun i hi hil => h i hi (by omega)),
    h (d + 1 + k) (by omega) (Nat.le_refl _)]

/-- Reifying a causal family is a causal value map. At the candidate boundary
the input prefix already contains the whole finite value. -/
noncomputable def FiniteGridFamily.reifyMap (r k : Nat) (B : FiniteGridFamily (r + 1 + k)) :
    FiniteGridMap (r + 1 + k) where
  eval x := (B.fiber x).reify r k
  causal j hj x y h := by
    by_cases he : j = r + 1 + k
    · subst j
      rw [FiniteGridValue.eq_of_agree _ x y h]
    · by_cases hk : k ≤ j
      · obtain ⟨d, he⟩ : ∃ d, j = d + k := ⟨j - k, (Nat.sub_add_cancel hk).symm⟩
        subst j
        change universeReifyValues r k (B.fiber x).carrier _ (d + k) =
          universeReifyValues r k (B.fiber y).carrier _ (d + k)
        rw [universeReifyValues_at, universeReifyValues_at]
        apply universeReify_proper_congr r k _ _ _ _ d (by omega)
        intro i hi hil
        funext v
        exact B.causal i hi x y (h.mono (by omega)) v
      · change universeReifyValues r k (B.fiber x).carrier _ j =
          universeReifyValues r k (B.fiber y).carrier _ j
        unfold universeReifyValues
        rw [dif_neg hk, dif_neg hk]

noncomputable def FiniteGridFamily.reifyPropMap (B : FiniteGridFamily R) : FiniteGridMap R where
  eval x := (B.fiber x).reifyProp
  causal j hj x y h := by
    by_cases he : j = R
    · subst j
      rw [FiniteGridValue.eq_of_agree _ x y h]
    · change propReifyValues R _ j = propReifyValues R _ j
      unfold propReifyValues
      rw [dif_neg he, dif_neg he]

theorem FiniteGridFamily.reifyMap_valid (r k : Nat) (B : FiniteGridFamily (r + 1 + k))
    (x : FiniteGridValue (r + 1 + k)) :
    (FiniteGridType.sort (r + 1 + k) (.type r)).Valid ((B.reifyMap r k).eval x) :=
  (B.fiber x).reify_valid r k

theorem FiniteGridFamily.reifyPropMap_valid (B : FiniteGridFamily R) (x : FiniteGridValue R) :
    (FiniteGridType.sort R .prop).Valid (B.reifyPropMap.eval x) := (B.fiber x).reifyProp_valid

end Submission.Helpers
