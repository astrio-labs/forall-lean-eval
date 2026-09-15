import Submission.SourceGridProducts

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem uniformUniverseDecode_formed (R : Nat) (s : Srt) (hs : sortRank s ≤ R)
    (v : FiniteGridValue R) : (uniformUniverseDecode R (some s) v).Formed s := by
  cases s with
  | prop => exact decodePropType_formed R v
  | type i =>
    obtain ⟨k, he⟩ : ∃ k, R = i + 1 + k := ⟨R - (i + 1), by simp only [sortRank] at hs; omega⟩
    subst R
    rw [uniformUniverseDecode_at]
    exact decodeUniverseType_formed i k v

theorem sourceGridUpgrade_formed (R j : Nat) (old next : FiniteGridType R)
    (ho : old.Formed s) (hn : next.Formed s) : (sourceGridUpgrade R j old next).Formed s := by
  intro i hi v
  change GridFormation R i s (if i = j + 1 then _ else _)
  split
  · exact hn i hi v
  · exact ho i hi v

theorem SourceGridMeaning.interp_formed (M : SourceGridMeaning R) (Γ : List Tm) (s : Srt)
    (h : ∀ ρ, (M.rawType Γ ρ).Formed s) (ρ : GridEnvironment R) : (M.interp Γ ρ).Formed s :=
  fun i hi v => h (GridEnvironment.truncate i ρ) i hi v

theorem sourceGridBaseType_formed (h : BoundedTyping (r + 2) Γ A (.srt s)) :
    (sourceGridBaseType r A).Formed s := by
  intro i hi v
  change GridFormation (r + 1) i s
    (if he : i = 0 then gridCodeCast rfl he.symm (arityAt (.type r) A : (carrierGrid (r + 1) 0).Code)
      else (carrierGrid (r + 1) i).defaultCode)
  split
  · rename_i he
    subst i
    change GridFormation (r + 1) 0 s (arityAt (.type r) A)
    refine ⟨fun hs => h.below_top_kind rfl (by omega), ?_⟩
    exact GridCodeImage.base _
  · exact gridFormation_default hi s

/-- Formation is preserved by the structural successor interpreter. The
assumption concerns only the previous coordinate stage, not normalization. -/
theorem sourceGridStep_raw_formed (r j : Nat) (hj : j ≤ r + 1)
    (old : Tm → SourceGridMeaning (r + 1))
    (hold : ∀ Γ ρ A s, BoundedTyping (r + 2) Γ A (.srt s) → ((old A).interp Γ ρ).Formed s)
    (A : Tm) (Γ : List Tm) (s : Srt) (h : BoundedTyping (r + 2) Γ A (.srt s))
    (ρ : GridEnvironment (r + 1)) : ((sourceGridStep r j hj old A).rawType Γ ρ).Formed s := by
  induction A generalizing Γ s ρ with
  | var x =>
    apply sourceGridUpgrade_formed _ _ _ _ (hold Γ ρ _ s h)
    rw [typeSort_eq h]
    exact uniformUniverseDecode_formed _ s (by have hs := h.var_below_top; omega) _
  | srt q =>
    obtain ⟨s', ha, hs, hs', hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst s'
    exact sourceGridUpgrade_formed _ _ _ _ (hold Γ ρ _ s h) (FiniteGridType.sort_formed _ ha)
  | app f a ihf iha =>
    apply sourceGridUpgrade_formed _ _ _ _ (hold Γ ρ _ s h)
    rw [typeSort_eq h]
    exact uniformUniverseDecode_formed _ s (by have hs := h.app_below_top; omega) _
  | lam D b ihD ihb =>
    obtain ⟨B, s', hPi, hb, hs', hc⟩ := h.generation
    exact (not_conv_pi_srt hc).elim
  | pi D B ihD ihB =>
    obtain ⟨sA, sB, sC, hD, hB, hr, hsA, hsB, hsC, hc⟩ := h.generation
    have he := conv_srt_inj hc
    subst sC
    apply sourceGridUpgrade_formed _ _ _ _ (hold Γ ρ _ s h)
    apply finitePiType_formed r _ _ hr
    · exact (sourceGridStep r j hj old D).interp_formed Γ sA (fun δ => ihD Γ sA hD δ) ρ
    · intro a ha
      exact (sourceGridStep r j hj old B).interp_formed (D :: Γ) sB
        (fun δ => ihB (D :: Γ) sB hB δ) (push a ρ)

theorem sourceGridStages_formed (r d : Nat) (hd : d ≤ r + 2)
    (Γ : List Tm) (ρ : GridEnvironment (r + 1)) (A : Tm) (s : Srt)
    (h : BoundedTyping (r + 2) Γ A (.srt s)) : ((sourceGridStages r d hd A).interp Γ ρ).Formed s := by
  induction d generalizing Γ ρ A s with
  | zero => exact sourceGridBaseType_formed h
  | succ d ih =>
    exact (sourceGridStep r d (by omega) (sourceGridStages r d (by omega)) A).interp_formed Γ s
      (fun δ => sourceGridStep_raw_formed r d (by omega) (sourceGridStages r d (by omega))
        (fun Δ ε B q hB => ih (by omega) Δ ε B q hB) A Γ s h δ) ρ

/-- The new interpretation satisfies universe formation for every source
bound r+2, every source typing derivation, and every finite environment. -/
theorem sourceGridInterpretation_formed (h : BoundedTyping (r + 2) Γ A (.srt s))
    (ρ : GridEnvironment (r + 1)) : (sourceGridInterpretation r Γ ρ A).Formed s :=
  sourceGridStages_formed r (r + 2) (Nat.le_refl _) Γ ρ A s h

end Submission.Helpers
