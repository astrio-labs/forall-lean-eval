import Submission.Uniqueness

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- `Prop` has rank zero; `Type i` has rank `i + 1`. -/
def sortRank : Srt → Nat
  | .prop => 0
  | .type i => i + 1

mutual
/-- A well-formed context with an explicit bound on the sorts in its derivation. -/
inductive BoundedWf (n : Nat) : List Tm → Prop where
  | nil : BoundedWf n []
  | cons : BoundedWf n Γ → BoundedTyping n Γ A (.srt s) → BoundedWf n (A :: Γ)

/-- The original typing rules with one finite bound on all sort parameters. -/
inductive BoundedTyping (n : Nat) : List Tm → Tm → Tm → Prop where
  | srt : BoundedWf n Γ → Ax s s' → sortRank s ≤ n → sortRank s' ≤ n →
      BoundedTyping n Γ (.srt s) (.srt s')
  | var : BoundedWf n Γ → Γ[i]? = some A →
      BoundedTyping n Γ (.var i) (lift (i + 1) 0 A)
  | pi : BoundedTyping n Γ A (.srt s₁) → BoundedTyping n (A :: Γ) B (.srt s₂) →
      Rl s₁ s₂ s₃ → sortRank s₁ ≤ n → sortRank s₂ ≤ n → sortRank s₃ ≤ n →
      BoundedTyping n Γ (.pi A B) (.srt s₃)
  | lam : BoundedTyping n Γ (.pi A B) (.srt s) → BoundedTyping n (A :: Γ) b B →
      sortRank s ≤ n → BoundedTyping n Γ (.lam A b) (.pi A B)
  | app : BoundedTyping n Γ f (.pi A B) → BoundedTyping n Γ a A →
      BoundedTyping n Γ (.app f a) (subst 0 a B)
  | conv : BoundedTyping n Γ t A → BoundedTyping n Γ B (.srt s) → Conv A B →
      sortRank s ≤ n → BoundedTyping n Γ t B
end

theorem BoundedTyping.mono (h : BoundedTyping n Γ t A) (hn : n ≤ m) :
    BoundedTyping m Γ t A := by
  induction h using BoundedTyping.rec (motive_1 := fun Γ _ => BoundedWf m Γ) with
  | nil => exact .nil
  | cons hw hA ihw ihA => exact .cons ihw ihA
  | srt hw ha hs hs' ihw => exact .srt ihw ha (Nat.le_trans hs hn) (Nat.le_trans hs' hn)
  | var hw hi ihw => exact .var ihw hi
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    exact .pi ihA ihB hr (Nat.le_trans hs₁ hn) (Nat.le_trans hs₂ hn) (Nat.le_trans hs₃ hn)
  | lam hPi hb hs ihPi ihb => exact .lam ihPi ihb (Nat.le_trans hs hn)
  | app hf ha ihf iha => exact .app ihf iha
  | conv ht hB hc hs iht ihB => exact .conv iht ihB hc (Nat.le_trans hs hn)

theorem BoundedWf.mono (h : BoundedWf n Γ) (hn : n ≤ m) : BoundedWf m Γ := by
  induction Γ with
  | nil => exact .nil
  | cons A Γ ih =>
    cases h with
    | cons hw hA => exact .cons (ih hw) (hA.mono hn)

theorem BoundedTyping.forget (h : BoundedTyping n Γ t A) : Typing Γ t A := by
  induction h using BoundedTyping.rec (motive_1 := fun Γ _ => Wf Γ) with
  | nil => exact .nil
  | cons hw hA ihw ihA => exact .cons ihw ihA
  | srt hw ha hs hs' ihw => exact .srt ihw ha
  | var hw hi ihw => exact .var ihw hi
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB => exact .pi ihA ihB hr
  | lam hPi hb hs ihPi ihb => exact .lam ihPi ihb
  | app hf ha ihf iha => exact .app ihf iha
  | conv ht hB hc hs iht ihB => exact .conv iht ihB hc

/-- Every typing derivation uses only finitely many universe levels. -/
theorem typing_bounded (h : Typing Γ t A) : ∃ n, BoundedTyping n Γ t A := by
  induction h using Typing.rec (motive_1 := fun Γ _ => ∃ n, BoundedWf n Γ) with
  | nil => exact ⟨0, .nil⟩
  | cons hw hA ihw ihA =>
    obtain ⟨n, hn⟩ := ihw
    obtain ⟨m, hm⟩ := ihA
    exact ⟨n + m, .cons (hn.mono (by omega)) (hm.mono (by omega))⟩
  | @srt Γ s s' hw ha ihw =>
    obtain ⟨n, hn⟩ := ihw
    refine ⟨n + sortRank s + sortRank s', .srt (hn.mono (by omega)) ha ?_ ?_⟩ <;> omega
  | var hw hi ihw =>
    obtain ⟨n, hn⟩ := ihw
    exact ⟨n, .var hn hi⟩
  | @pi Γ A B s₁ s₂ s₃ hA hB hr ihA ihB =>
    obtain ⟨n, hn⟩ := ihA
    obtain ⟨m, hm⟩ := ihB
    refine ⟨n + m + sortRank s₁ + sortRank s₂ + sortRank s₃,
      .pi (hn.mono (by omega)) (hm.mono (by omega)) hr ?_ ?_ ?_⟩ <;> omega
  | @lam Γ A B b s hPi hb ihPi ihb =>
    obtain ⟨n, hn⟩ := ihPi
    obtain ⟨m, hm⟩ := ihb
    refine ⟨n + m + sortRank s, .lam (hn.mono (by omega)) (hm.mono (by omega)) ?_⟩
    omega
  | app hf ha ihf iha =>
    obtain ⟨n, hn⟩ := ihf
    obtain ⟨m, hm⟩ := iha
    exact ⟨n + m, .app (hn.mono (by omega)) (hm.mono (by omega))⟩
  | @conv Γ t A B s ht hB hc iht ihB =>
    obtain ⟨n, hn⟩ := iht
    obtain ⟨m, hm⟩ := ihB
    refine ⟨n + m + sortRank s, .conv (hn.mono (by omega)) (hm.mono (by omega)) hc ?_⟩
    omega

theorem no_bounded_typing_zero (h : BoundedTyping 0 Γ t A) : False := by
  induction h using BoundedTyping.rec (motive_1 := fun Γ _ => Γ = []) with
  | nil => rfl
  | cons hw hA ihw ihA => exact ihA.elim
  | srt hw ha hs hs' ihw =>
    cases ha <;> simp only [sortRank] at hs' <;> omega
  | var hw hi ihw =>
    simp [ihw] at hi
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB => exact ihA
  | lam hPi hb hs ihPi ihb => exact ihPi
  | app hf ha ihf iha => exact ihf
  | conv ht hB hc hs iht ihB => exact iht

/-- A normalization theorem uniform in the finite bound suffices for CCω. -/
theorem normalization_of_bounded
    (hSN : ∀ n Γ t A, BoundedTyping n Γ t A → SN t)
    (h : Typing Γ t A) : SN t := by
  obtain ⟨n, hn⟩ := typing_bounded h
  exact hSN n Γ t A hn

end Submission.Helpers
