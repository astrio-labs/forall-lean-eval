import Submission.UniverseReification

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

noncomputable def propReifyValues (R : Nat) (J : CausalGridPredicate R) : TowerFamily (carrierGrid R) :=
  fun j => if he : j = R then gridValueCast rfl he.symm
    ⟨carrierGridCandidateCode R, (carrierGridCandidateRetraction R).encode (J.candidate (TowerFamily.point (carrierGrid R)))⟩
    else TowerFamily.point (carrierGrid R) j

theorem propReifyValues_bottom (R : Nat) (J : CausalGridPredicate R) :
    propReifyValues R J R =
      ⟨carrierGridCandidateCode R, (carrierGridCandidateRetraction R).encode (J.candidate (TowerFamily.point (carrierGrid R)))⟩ := by
  unfold propReifyValues
  rw [dif_pos rfl]
  rfl

theorem propReifyValues_typed (R : Nat) (J : CausalGridPredicate R) :
    (uniformSortType R .prop).Coherent (R + 1) (Nat.le_refl _) (propReifyValues R J) := by
  intro j hj
  change (propReifyValues R J j).code = uniformSortCode R j (by omega) .prop (propReifyValues R J)
  by_cases he : j = R
  · subst j
    rw [propReifyValues_bottom]
    unfold uniformSortCode
    dsimp only
    rw [dif_pos rfl]
    rfl
  · unfold propReifyValues uniformSortCode
    dsimp only
    rw [dif_neg he, dif_neg he]
    rfl

noncomputable def propValueCandidate (R : Nat) (v : TowerFamily (carrierGrid R)) : Candidate :=
  (carrierGridCandidateRetraction R).decode ((v R).cast (carrierGridCandidateCode R))

/-- A proposition's coherent proof values are terminal at every coordinate.
This is a semantic equality and makes no assertion about source bounds. -/
theorem prop_coherent_values (R : Nat) (C : CausalGridType R) (hC : C.Formed .prop)
    (v : TowerFamily (carrierGrid R)) (hv : C.Coherent (R + 1) (Nat.le_refl _) v) :
    TowerFamily.AgreeBelow (R + 1) v (TowerFamily.point (carrierGrid R)) := by
  intro j hj
  apply gridValue_eq_point R j (v j)
  exact (hv j hj).trans ((hC j (by omega) v).lower (by simp only [sortRank]; omega))

/-- Impredicative proposition reification preserves the actual reducibility
candidate on every coherent argument, at every finite source row. -/
theorem propReifyValues_candidate (R : Nat) (C : CausalGridType R) (J : CausalGridPredicate R)
    (hC : C.Formed .prop) (v : TowerFamily (carrierGrid R))
    (hv : C.Coherent (R + 1) (Nat.le_refl _) v) :
    propValueCandidate R (propReifyValues R J) = J.candidate v := by
  unfold propValueCandidate
  rw [propReifyValues_bottom, TowerValue.cast_mk, (carrierGridCandidateRetraction R).roundtrip]
  exact (J.causal v _ (prop_coherent_values R C hC v hv)).symm

end Submission.Helpers
