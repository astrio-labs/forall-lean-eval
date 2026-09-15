import Submission.Helpers

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Generation records retain the conversion at the end of a typing derivation. -/
def Generation (Γ : List Tm) (t C : Tm) : Prop :=
  match t with
  | .var i => ∃ A, Γ[i]? = some A ∧ Conv (lift (i + 1) 0 A) C
  | .srt s => ∃ s', Ax s s' ∧ Conv (.srt s') C
  | .pi A B => ∃ s₁ s₂ s₃, Typing Γ A (.srt s₁) ∧
      Typing (A :: Γ) B (.srt s₂) ∧ Rl s₁ s₂ s₃ ∧ Conv (.srt s₃) C
  | .lam A b => ∃ B s, Typing Γ (.pi A B) (.srt s) ∧
      Typing (A :: Γ) b B ∧ Conv (.pi A B) C
  | .app f a => ∃ A B, Typing Γ f (.pi A B) ∧
      Typing Γ a A ∧ Conv (subst 0 a B) C

theorem generation_conv (h : Generation Γ t A) (hc : Conv A B) : Generation Γ t B := by
  cases t with
  | var i =>
    obtain ⟨C, hC, he⟩ := h
    exact ⟨C, hC, conv_trans he hc⟩
  | srt s =>
    obtain ⟨s', hs, he⟩ := h
    exact ⟨s', hs, conv_trans he hc⟩
  | pi C D =>
    obtain ⟨s₁, s₂, s₃, hC, hD, hr, he⟩ := h
    exact ⟨s₁, s₂, s₃, hC, hD, hr, conv_trans he hc⟩
  | lam C b =>
    obtain ⟨D, s, hD, hb, he⟩ := h
    exact ⟨D, s, hD, hb, conv_trans he hc⟩
  | app f a =>
    obtain ⟨C, D, hf, ha, he⟩ := h
    exact ⟨C, D, hf, ha, conv_trans he hc⟩

theorem typing_generation (h : Typing Γ t A) : Generation Γ t A := by
  induction h using Typing.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw hax _ => exact ⟨_, hax, .refl _⟩
  | var hw hv _ => exact ⟨_, hv, .refl _⟩
  | pi hA hB hr _ _ => exact ⟨_, _, _, hA, hB, hr, .refl _⟩
  | lam hPi hb _ _ => exact ⟨_, _, hPi, hb, .refl _⟩
  | app hf ha _ _ => exact ⟨_, _, hf, ha, .refl _⟩
  | conv ht hB hc iht _ => exact generation_conv iht hc

theorem typing_wf (h : Typing Γ t A) : Wf Γ := by
  induction h using Typing.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw hax _ => exact hw
  | var hw hv _ => exact hw
  | pi hA hB hr ihA _ => exact ihA
  | lam hPi hb ihPi _ => exact ihPi
  | app hf ha ihf _ => exact ihf
  | conv ht hB hc iht _ => exact iht

theorem pi_domain (h : Typing Γ (.pi A B) C) : ∃ s, Typing Γ A (.srt s) := by
  obtain ⟨s₁, s₂, s₃, hA, _, _, _⟩ := typing_generation h
  exact ⟨s₁, hA⟩

theorem pi_codomain (h : Typing Γ (.pi A B) C) :
    ∃ s, Typing (A :: Γ) B (.srt s) := by
  obtain ⟨s₁, s₂, s₃, _, hB, _, _⟩ := typing_generation h
  exact ⟨s₂, hB⟩

/-- A context morphism for renaming records lookup and its lifted type. -/
def RenCtx (Γ Δ : List Tm) (ρ : Nat → Nat) : Prop :=
  ∀ i A, Γ[i]? = some A → ∃ B, Δ[ρ i]? = some B ∧
    ren ρ (lift (i + 1) 0 A) = lift (ρ i + 1) 0 B

theorem ren_up_shift (ρ : Nat → Nat) (d : Nat) (t : Tm) :
    ren (upRen ρ) (lift (d + 1) 0 t) = ren Nat.succ (ren ρ (lift d 0 t)) := by
  rw [← ren_succ_lift, ren_comp, ren_comp]
  rfl

theorem RenCtx.up (h : RenCtx Γ Δ ρ) (A : Tm) :
    RenCtx (A :: Γ) (ren ρ A :: Δ) (upRen ρ) := by
  intro i C hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst C
    refine ⟨ren ρ A, rfl, ?_⟩
    simp only [upRen, ren_up_shift, lift_zero]
    exact (lift_one _).symm
  | succ i =>
    obtain ⟨D, hD, he⟩ := h i C hi
    refine ⟨D, hD, ?_⟩
    simpa only [upRen, ren_up_shift, he] using ren_succ_lift (ρ i + 1) D

theorem RenCtx.weaken (Γ : List Tm) (A : Tm) : RenCtx Γ (A :: Γ) Nat.succ := by
  intro i B hi
  exact ⟨B, hi, ren_succ_lift (i + 1) B⟩

theorem typing_ren (h : Typing Γ t A) (hw : Wf Δ) (hρ : RenCtx Γ Δ ρ) :
    Typing Δ (ren ρ t) (ren ρ A) := by
  induction h using Typing.rec (motive_1 := fun _ _ => True)
      generalizing Δ ρ with
  | nil => trivial
  | cons => trivial
  | srt _ hax _ => exact .srt hw hax
  | var _ hv _ =>
    obtain ⟨B, hB, he⟩ := hρ _ _ hv
    simpa only [ren, he] using (Typing.var hw hB)
  | pi hA hB hr ihA ihB =>
    have hA' := ihA hw hρ
    exact .pi hA' (ihB (.cons hw hA') (hρ.up _)) hr
  | lam hPi hb ihPi ihb =>
    have hPi' := ihPi hw hρ
    obtain ⟨s, hA'⟩ := pi_domain hPi'
    exact .lam hPi' (ihb (.cons hw hA') (hρ.up _))
  | app hf ha ihf iha =>
    rw [ren, ren_subst]
    exact .app (ihf hw hρ) (iha hw hρ)
  | conv ht hB hc iht ihB =>
    exact .conv (iht hw hρ) (ihB hw hρ) (conv_ren hc ρ)

theorem typing_weaken (h : Typing Γ t A) (hB : Typing Γ B (.srt s)) :
    Typing (B :: Γ) (ren Nat.succ t) (ren Nat.succ A) :=
  typing_ren h (.cons (typing_wf hB) hB) (.weaken Γ B)

/-- A typed simultaneous substitution sends each context variable to its required type. -/
def SubCtx (Γ Δ : List Tm) (σ : Nat → Tm) : Prop :=
  ∀ i A, Γ[i]? = some A → Typing Δ (σ i) (sub σ (lift (i + 1) 0 A))

theorem SubCtx.up (h : SubCtx Γ Δ σ) (hw : Wf Δ)
    (hA : Typing Δ (sub σ A) (.srt s)) :
    SubCtx (A :: Γ) (sub σ A :: Δ) (upSub σ) := by
  intro i C hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst C
    simpa only [upSub, Nat.zero_add, lift_one, sub_up_ren] using
      (Typing.var (i := 0) (.cons hw hA) (A := sub σ A) rfl)
  | succ i =>
    have hv := typing_weaken (h i C hi) hA
    simpa only [upSub, ← ren_succ_lift (i + 1), sub_up_ren] using hv

theorem typing_sub (h : Typing Γ t A) (hw : Wf Δ) (hσ : SubCtx Γ Δ σ) :
    Typing Δ (sub σ t) (sub σ A) := by
  induction h using Typing.rec (motive_1 := fun _ _ => True)
      generalizing Δ σ with
  | nil => trivial
  | cons => trivial
  | srt _ hax _ => exact .srt hw hax
  | var _ hv _ => exact hσ _ _ hv
  | pi hA hB hr ihA ihB =>
    have hA' := ihA hw hσ
    exact .pi hA' (ihB (.cons hw hA') (hσ.up hw hA')) hr
  | lam hPi hb ihPi ihb =>
    have hPi' := ihPi hw hσ
    obtain ⟨s, hA'⟩ := pi_domain hPi'
    exact .lam hPi' (ihb (.cons hw hA') (hσ.up hw hA'))
  | app hf ha ihf iha =>
    rw [sub, sub_subst]
    exact .app (ihf hw hσ) (iha hw hσ)
  | conv ht hB hc iht ihB =>
    exact .conv (iht hw hσ) (ihB hw hσ) (conv_sub hc σ)

theorem SubCtx.single (ha : Typing Γ a A) : SubCtx (A :: Γ) Γ (single a) := by
  intro i C hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst C
    simpa only [Helpers.single, Nat.zero_add, lift_one, single_ren_succ] using ha
  | succ i =>
    simpa only [Helpers.single, ← ren_succ_lift (i + 1), single_ren_succ] using
      (Typing.var (typing_wf ha) hi)

theorem typing_subst (hb : Typing (A :: Γ) b B) (ha : Typing Γ a A) :
    Typing Γ (subst 0 a b) (subst 0 a B) := by
  simp only [subst_eq_sub]
  exact typing_sub hb (typing_wf ha) (.single ha)

theorem typing_context_conv (hb : Typing (A :: Γ) b B)
    (hA : Typing Γ A (.srt s)) (hA' : Typing Γ A' (.srt s')) (hc : Conv A A') :
    Typing (A' :: Γ) b B := by
  have hw := typing_wf hA'
  have hσ : SubCtx (A :: Γ) (A' :: Γ) Tm.var := by
    intro i C hi
    rw [sub_var]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst C
      simp only [Nat.zero_add, lift_one]
      apply Typing.conv (Typing.var (i := 0) (.cons hw hA') rfl)
        (typing_weaken hA hA')
      simpa only [Nat.zero_add, lift_one] using conv_ren (conv_symm hc) Nat.succ
    | succ i => exact .var (.cons hw hA') hi
  simpa only [sub_var] using typing_sub hb (.cons hw hA') hσ


theorem wf_lookup (hw : Wf Γ) (hi : Γ[i]? = some A) :
    ∃ s, Typing Γ (lift (i + 1) 0 A) (.srt s) := by
  induction Γ generalizing i with
  | nil => simp at hi
  | cons C Γ ih =>
    cases hw with
    | cons hw hC =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst A
        exact ⟨_, by simpa only [Nat.zero_add, lift_one, ren] using typing_weaken hC hC⟩
      | succ i =>
        obtain ⟨s, hA⟩ := ih hw hi
        exact ⟨s, by simpa only [ren, ren_succ_lift] using typing_weaken hA hC⟩

theorem sort_has_sort (hw : Wf Γ) (s : Srt) : ∃ s', Typing Γ (.srt s) (.srt s') := by
  cases s with
  | prop => exact ⟨_, .srt hw .prop⟩
  | type i => exact ⟨_, .srt hw (.type i)⟩

theorem type_correctness (h : Typing Γ t A) : ∃ s, Typing Γ A (.srt s) := by
  induction h using Typing.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw hax _ => exact sort_has_sort hw _
  | var hw hi _ => exact wf_lookup hw hi
  | pi hA hB hr _ _ => exact sort_has_sort (typing_wf hA) _
  | lam hPi hb _ _ => exact ⟨_, hPi⟩
  | app hf ha ihf _ =>
    obtain ⟨s, hPi⟩ := ihf
    obtain ⟨sB, hB⟩ := pi_codomain hPi
    exact ⟨sB, typing_subst hB ha⟩
  | conv ht hB hc _ _ => exact ⟨_, hB⟩

theorem beta_typing (hf : Typing Γ (.lam A b) (.pi C D)) (ha : Typing Γ a C) :
    Typing Γ (subst 0 a b) (subst 0 a D) := by
  obtain ⟨B, s, hPi, hb, hc⟩ := typing_generation hf
  obtain ⟨hcA, hcB⟩ := conv_pi_inj hc
  obtain ⟨sA, hA⟩ := pi_domain hPi
  have haA : Typing Γ a A := .conv ha hA (conv_symm hcA)
  have hsub := typing_subst hb haA
  obtain ⟨sT, hT⟩ := type_correctness hf
  obtain ⟨sD, hD⟩ := pi_codomain hT
  apply Typing.conv hsub (typing_subst hD ha)
  simpa only [subst_eq_sub] using conv_sub hcB (single a)

theorem preservation (h : Typing Γ t A) (hs : Step t t') : Typing Γ t' A := by
  induction h using Typing.rec (motive_1 := fun _ _ => True)
      generalizing t' with
  | nil => trivial
  | cons => trivial
  | srt => cases hs
  | var => cases hs
  | pi hA hB hr ihA ihB =>
    cases hs with
    | piDom B hAA' =>
      have hA' := ihA hAA'
      exact .pi hA' (typing_context_conv hB hA hA' (.fwd (.refl _) hAA')) hr
    | piCod A hBB' => exact .pi hA (ihB hBB') hr
  | lam hPi hb ihPi ihb =>
    cases hs with
    | lamTy b hAA' =>
      have hPi' := ihPi (.piDom _ hAA')
      obtain ⟨sA, hA⟩ := pi_domain hPi
      obtain ⟨sA', hA'⟩ := pi_domain hPi'
      have hb' := typing_context_conv hb hA hA' (.fwd (.refl _) hAA')
      exact .conv (.lam hPi' hb') hPi (.bwd (.refl _) (.piDom _ hAA'))
    | lamBody A hbb' => exact .lam hPi (ihb hbb')
  | app hf ha ihf iha =>
    cases hs with
    | beta A b a => exact beta_typing hf ha
    | appFun a hff' => exact .app (ihf hff') ha
    | appArg f haa' =>
      obtain ⟨sT, hT⟩ := type_correctness hf
      obtain ⟨sB, hB⟩ := pi_codomain hT
      exact .conv (.app hf (iha haa')) (typing_subst hB ha)
        (conv_subst_arg (.bwd (.refl _) haa') _)
  | conv ht hB hc iht _ => exact .conv (iht hs) hB hc

end Submission.Helpers
