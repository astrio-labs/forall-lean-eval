import Submission.UniverseTypePrefix

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- A complete type has a final reducibility family after all carrier values
have been read. Its dependency bound includes the bottom value. -/
structure CausalGridPredicate (R : Nat) where
  candidate : TowerFamily (carrierGrid R) → Candidate
  causal : TowerFamily.DependsBelow (R + 1) candidate

noncomputable def universeReify (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (d : Nat) : TowerValue (carrierGrid (r + 1 + k) (d + k)) := by
  classical
  exact if hd : d ≤ r then
    (universeTypePrefix r k C d (by omega)).encodeCode hd k (universeTypeField r k C d hd)
  else if he : d = r + 1 then
    gridValueCast rfl (congrArg (fun d => d + k) he.symm)
      ((universeTypePrefix r k C (r + 1) (Nat.le_refl _)).encodeCandidate k (fun x =>
        J.candidate (universeArgumentLift r k
          (((universeTypePrefix r k C (r + 1) (Nat.le_refl _)).arguments k).encode x))))
  else TowerFamily.point (carrierGrid (r + 1 + k)) (d + k)

theorem universeReify_proper (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (d : Nat) (hd : d ≤ r) :
    universeReify r k C J d =
      (universeTypePrefix r k C d (by omega)).encodeCode hd k (universeTypeField r k C d hd) := by
  unfold universeReify
  rw [dif_pos hd]

theorem universeReify_final (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) :
    universeReify r k C J (r + 1) =
      (universeTypePrefix r k C (r + 1) (Nat.le_refl _)).encodeCandidate k (fun x =>
        J.candidate (universeArgumentLift r k
          (((universeTypePrefix r k C (r + 1) (Nat.le_refl _)).arguments k).encode x))) := by
  unfold universeReify
  rw [dif_neg (Nat.not_succ_le_self _), dif_pos rfl]
  rfl

/-- Reading the preceding encoded fields reconstructs exactly the prefix
used to encode the next one. -/
theorem universeReify_prefix (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (d : Nat) (hd : d ≤ r + 1) :
    UniversePrefix.fromValues r k d hd (universeReify r k C J) = universeTypePrefix r k C d hd := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [UniversePrefix.fromValues, ih (by omega), universeReify_proper r k C J d (by omega),
      UniversePrefix.decodeCode_encodeCode]
    rfl

theorem universeReify_code (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (d : Nat) (hd : d ≤ r + 1) :
    (universeReify r k C J d).code = ((universeTypePrefix r k C d hd).shiftObject hd k).code := by
  by_cases hl : d ≤ r
  · rw [universeReify_proper r k C J d hl]
    exact (universeTypePrefix r k C d hd).shiftCodeObject_code hl k
  · have he : d = r + 1 := by omega
    subst d
    rw [universeReify_final]
    exact (universeTypePrefix r k C (r + 1) hd).shiftCandidateObject_code k

/-- Formation and the ordinary carrier equations of an argument suffice for
faithful type decoding. Neither projection invariance nor image membership
is an additional assumption. -/
theorem universeReify_decode (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (hC : C.Formed (.type r))
    (d : Nat) (hd : d ≤ r) (v : TowerFamily (carrierGrid (r + 1 + k)))
    (hv : C.Coherent (d + 1 + k) (by omega) v) :
    (universeTypePrefix r k C d (by omega)).readCodeFamily hd k
      (universeReify r k C J d) (universeArgumentSlice r k v) = C.code (d + 1 + k) (by omega) v := by
  rw [universeReify_proper r k C J d hd]
  unfold UniversePrefix.readCodeFamily
  rw [UniversePrefix.decodeCode_encodeCode]
  dsimp only [familyDecode, universeTypeField]
  rw [C.causal (d + 1 + k) (by omega) _ v
    (universeTypePrefix_recover r k C hC d (by omega) v hv)]
  exact universeOutputCodes_formed r d k _ (hC _ (by omega) v)

/-- The same reconstruction reaches the final reducibility family; there
is no missing vertical value transport at the bottom coordinate. -/
theorem universeReify_candidate (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (hC : C.Formed (.type r))
    (v : TowerFamily (carrierGrid (r + 1 + k)))
    (hv : C.Coherent (r + 2 + k) (by omega) v) :
    (universeTypePrefix r k C (r + 1) (Nat.le_refl _)).readCandidateFamily k
      (universeReify r k C J (r + 1)) (universeArgumentSlice r k v) = J.candidate v := by
  rw [universeReify_final]
  unfold UniversePrefix.readCandidateFamily
  rw [UniversePrefix.decodeCandidate_encodeCandidate]
  exact J.causal _ v ((universeTypePrefix_recover r k C hC (r + 1) (Nat.le_refl _) v hv).mono (by omega))

noncomputable def universeReifyValues (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) : TowerFamily (carrierGrid (r + 1 + k)) :=
  fun j => if hj : k ≤ j then gridValueCast rfl (Nat.sub_add_cancel hj) (universeReify r k C J (j - k))
    else TowerFamily.point (carrierGrid (r + 1 + k)) j

theorem universeReifyValues_at (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (d : Nat) :
    universeReifyValues r k C J (d + k) = universeReify r k C J d := by
  unfold universeReifyValues
  rw [dif_pos (show k ≤ d + k by omega)]
  exact gridValueCast_family (by omega) _ (universeReify r k C J)

theorem universeReifyValues_active_code (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) (d : Nat) (hd : d ≤ r + 1) :
    (universeReifyValues r k C J (d + k)).code =
      uniformSortCode (r + 1 + k) (d + k) (by omega) (.type r) (universeReifyValues r k C J) := by
  rw [universeReifyValues_at, uniformSortCode_at r k d hd]
  unfold universeSortAt
  have hv : (fun i => universeReifyValues r k C J (i + k)) = universeReify r k C J :=
    funext (universeReifyValues_at r k C J)
  rw [hv, universeReify_prefix]
  exact universeReify_code r k C J d hd

/-- Reification also has exactly the value carrier of its declared universe,
uniformly across the active, terminal, and candidate coordinates. -/
theorem universeReifyValues_typed (r k : Nat) (C : CausalGridType (r + 1 + k))
    (J : CausalGridPredicate (r + 1 + k)) :
    (uniformSortType (r + 1 + k) (.type r)).Coherent (r + 2 + k) (by omega) (universeReifyValues r k C J) := by
  intro j hj
  by_cases hk : k ≤ j
  · obtain ⟨d, he⟩ : ∃ d, j = d + k := ⟨j - k, (Nat.sub_add_cancel hk).symm⟩
    subst j
    exact universeReifyValues_active_code r k C J d (by omega)
  · change (universeReifyValues r k C J j).code =
      uniformSortCode (r + 1 + k) j (by omega) (.type r) (universeReifyValues r k C J)
    rw [uniformSortCode_lower _ _ (by omega) (Ax.type r) _ (by simp only [sortRank]; omega)]
    unfold universeReifyValues
    rw [dif_neg hk]
    rfl

end Submission.Helpers
