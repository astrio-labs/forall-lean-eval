import Submission.UniverseBounds
import Submission.Reducibility

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Inversion of bounded typing retains the bound used by each product rule. -/
def BoundedGeneration (n : Nat) (Γ : List Tm) (t C : Tm) : Prop :=
  match t with
  | .var i => ∃ A, Γ[i]? = some A ∧ Conv (lift (i + 1) 0 A) C
  | .srt s => ∃ s', Ax s s' ∧ sortRank s ≤ n ∧ sortRank s' ≤ n ∧ Conv (.srt s') C
  | .pi A B => ∃ s₁ s₂ s₃, BoundedTyping n Γ A (.srt s₁) ∧
      BoundedTyping n (A :: Γ) B (.srt s₂) ∧ Rl s₁ s₂ s₃ ∧
      sortRank s₁ ≤ n ∧ sortRank s₂ ≤ n ∧ sortRank s₃ ≤ n ∧ Conv (.srt s₃) C
  | .lam A b => ∃ B s, BoundedTyping n Γ (.pi A B) (.srt s) ∧
      BoundedTyping n (A :: Γ) b B ∧ sortRank s ≤ n ∧ Conv (.pi A B) C
  | .app f a => ∃ A B, BoundedTyping n Γ f (.pi A B) ∧
      BoundedTyping n Γ a A ∧ Conv (subst 0 a B) C

theorem bounded_generation_conv (h : BoundedGeneration n Γ t A) (hc : Conv A B) :
    BoundedGeneration n Γ t B := by
  cases t with
  | var i =>
    obtain ⟨C, hC, he⟩ := h
    exact ⟨C, hC, conv_trans he hc⟩
  | srt s =>
    obtain ⟨s', hs, hn, hn', he⟩ := h
    exact ⟨s', hs, hn, hn', conv_trans he hc⟩
  | pi C D =>
    obtain ⟨s₁, s₂, s₃, hC, hD, hr, hn₁, hn₂, hn₃, he⟩ := h
    exact ⟨s₁, s₂, s₃, hC, hD, hr, hn₁, hn₂, hn₃, conv_trans he hc⟩
  | lam C b =>
    obtain ⟨D, s, hD, hb, hn, he⟩ := h
    exact ⟨D, s, hD, hb, hn, conv_trans he hc⟩
  | app f a =>
    obtain ⟨C, D, hf, ha, he⟩ := h
    exact ⟨C, D, hf, ha, conv_trans he hc⟩

theorem BoundedTyping.generation (h : BoundedTyping n Γ t A) :
    BoundedGeneration n Γ t A := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw hax hs hs' _ => exact ⟨_, hax, hs, hs', .refl _⟩
  | var hw hv _ => exact ⟨_, hv, .refl _⟩
  | pi hA hB hr hs₁ hs₂ hs₃ _ _ => exact ⟨_, _, _, hA, hB, hr, hs₁, hs₂, hs₃, .refl _⟩
  | lam hPi hb hs _ _ => exact ⟨_, _, hPi, hb, hs, .refl _⟩
  | app hf ha _ _ => exact ⟨_, _, hf, ha, .refl _⟩
  | conv ht hB hc hs iht _ => exact bounded_generation_conv iht hc

theorem BoundedTyping.wf (h : BoundedTyping n Γ t A) : BoundedWf n Γ := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw hax hs hs' _ => exact hw
  | var hw hv _ => exact hw
  | pi hA hB hr hs₁ hs₂ hs₃ ihA _ => exact ihA
  | lam hPi hb hs ihPi _ => exact ihPi
  | app hf ha ihf _ => exact ihf
  | conv ht hB hc hs iht _ => exact iht

theorem BoundedTyping.pi_domain (h : BoundedTyping n Γ (.pi A B) C) :
    ∃ s, BoundedTyping n Γ A (.srt s) ∧ sortRank s ≤ n := by
  obtain ⟨s₁, s₂, s₃, hA, _, _, hs₁, _, _, _⟩ := h.generation
  exact ⟨s₁, hA, hs₁⟩

theorem BoundedTyping.pi_codomain (h : BoundedTyping n Γ (.pi A B) C) :
    ∃ s, BoundedTyping n (A :: Γ) B (.srt s) ∧ sortRank s ≤ n := by
  obtain ⟨s₁, s₂, s₃, _, hB, _, _, hs₂, _, _⟩ := h.generation
  exact ⟨s₂, hB, hs₂⟩

theorem BoundedTyping.rename (h : BoundedTyping n Γ t A)
    (hw : BoundedWf n Δ) (hρ : RenCtx Γ Δ ρ) :
    BoundedTyping n Δ (ren ρ t) (ren ρ A) := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True)
      generalizing Δ ρ with
  | nil => trivial
  | cons => trivial
  | srt _ hax hs hs' _ => exact .srt hw hax hs hs'
  | var _ hv _ =>
    obtain ⟨B, hB, he⟩ := hρ _ _ hv
    simpa only [ren, he] using (BoundedTyping.var hw hB)
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    have hA' := ihA hw hρ
    exact .pi hA' (ihB (.cons hw hA') (hρ.up _)) hr hs₁ hs₂ hs₃
  | lam hPi hb hs ihPi ihb =>
    have hPi' := ihPi hw hρ
    obtain ⟨s, hA', _⟩ := hPi'.pi_domain
    exact .lam hPi' (ihb (.cons hw hA') (hρ.up _)) hs
  | app hf ha ihf iha =>
    rw [ren, ren_subst]
    exact .app (ihf hw hρ) (iha hw hρ)
  | conv ht hB hc hs iht ihB =>
    exact .conv (iht hw hρ) (ihB hw hρ) (conv_ren hc ρ) hs

theorem BoundedTyping.weaken (h : BoundedTyping n Γ t A)
    (hB : BoundedTyping n Γ B (.srt s)) :
    BoundedTyping n (B :: Γ) (ren Nat.succ t) (ren Nat.succ A) :=
  h.rename (.cons hB.wf hB) (.weaken Γ B)

/-- Substitutions whose typing derivations obey the same finite bound. -/
def BoundedSubCtx (n : Nat) (Γ Δ : List Tm) (σ : Nat → Tm) : Prop :=
  ∀ i A, Γ[i]? = some A → BoundedTyping n Δ (σ i) (sub σ (lift (i + 1) 0 A))

theorem BoundedSubCtx.up (h : BoundedSubCtx n Γ Δ σ) (hw : BoundedWf n Δ)
    (hA : BoundedTyping n Δ (sub σ A) (.srt s)) :
    BoundedSubCtx n (A :: Γ) (sub σ A :: Δ) (upSub σ) := by
  intro i C hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst C
    simpa only [upSub, Nat.zero_add, lift_one, sub_up_ren] using
      (BoundedTyping.var (i := 0) (.cons hw hA) (A := sub σ A) rfl)
  | succ i =>
    have hv := (h i C hi).weaken hA
    simpa only [upSub, ← ren_succ_lift (i + 1), sub_up_ren] using hv

theorem BoundedTyping.substitute (h : BoundedTyping n Γ t A)
    (hw : BoundedWf n Δ) (hσ : BoundedSubCtx n Γ Δ σ) :
    BoundedTyping n Δ (sub σ t) (sub σ A) := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True)
      generalizing Δ σ with
  | nil => trivial
  | cons => trivial
  | srt _ hax hs hs' _ => exact .srt hw hax hs hs'
  | var _ hv _ => exact hσ _ _ hv
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    have hA' := ihA hw hσ
    exact .pi hA' (ihB (.cons hw hA') (hσ.up hw hA')) hr hs₁ hs₂ hs₃
  | lam hPi hb hs ihPi ihb =>
    have hPi' := ihPi hw hσ
    obtain ⟨s, hA', _⟩ := hPi'.pi_domain
    exact .lam hPi' (ihb (.cons hw hA') (hσ.up hw hA')) hs
  | app hf ha ihf iha =>
    rw [sub, sub_subst]
    exact .app (ihf hw hσ) (iha hw hσ)
  | conv ht hB hc hs iht ihB =>
    exact .conv (iht hw hσ) (ihB hw hσ) (conv_sub hc σ) hs

theorem BoundedSubCtx.single (ha : BoundedTyping n Γ a A) :
    BoundedSubCtx n (A :: Γ) Γ (single a) := by
  intro i C hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst C
    simpa only [Helpers.single, Nat.zero_add, lift_one, single_ren_succ] using ha
  | succ i =>
    simpa only [Helpers.single, ← ren_succ_lift (i + 1), single_ren_succ] using
      (BoundedTyping.var ha.wf hi)

theorem BoundedTyping.subst (hb : BoundedTyping n (A :: Γ) b B)
    (ha : BoundedTyping n Γ a A) :
    BoundedTyping n Γ (subst 0 a b) (subst 0 a B) := by
  simp only [subst_eq_sub]
  exact hb.substitute ha.wf (.single ha)

theorem BoundedTyping.context_conv (hb : BoundedTyping n (A :: Γ) b B)
    (hA : BoundedTyping n Γ A (.srt s)) (hA' : BoundedTyping n Γ A' (.srt s'))
    (hs : sortRank s ≤ n) (hc : Conv A A') : BoundedTyping n (A' :: Γ) b B := by
  have hw := hA'.wf
  have hσ : BoundedSubCtx n (A :: Γ) (A' :: Γ) Tm.var := by
    intro i C hi
    rw [sub_var]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst C
      simp only [Nat.zero_add, lift_one]
      apply BoundedTyping.conv (BoundedTyping.var (i := 0) (.cons hw hA') rfl)
        (hA.weaken hA') ?_ hs
      simpa only [Nat.zero_add, lift_one] using conv_ren (conv_symm hc) Nat.succ
    | succ i => exact .var (.cons hw hA') hi
  simpa only [sub_var] using hb.substitute (.cons hw hA') hσ

theorem BoundedWf.lookup (hw : BoundedWf n Γ) (hi : Γ[i]? = some A) :
    ∃ s, BoundedTyping n Γ (lift (i + 1) 0 A) (.srt s) := by
  induction Γ generalizing i with
  | nil => simp at hi
  | cons C Γ ih =>
    cases hw with
    | cons hw hC =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst A
        exact ⟨_, by simpa only [Nat.zero_add, lift_one, ren] using hC.weaken hC⟩
      | succ i =>
        obtain ⟨s, hA⟩ := ih hw hi
        exact ⟨s, by simpa only [ren, ren_succ_lift] using hA.weaken hC⟩

/-- At a finite bound the type can be the top sort, which has no type at that bound. -/
theorem BoundedTyping.regularity (h : BoundedTyping n Γ t A) :
    (∃ s, A = .srt s) ∨ ∃ s, BoundedTyping n Γ A (.srt s) := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | cons => trivial
  | srt hw hax hs hs' _ => exact .inl ⟨_, rfl⟩
  | var hw hi _ => exact .inr (hw.lookup hi)
  | pi hA hB hr hs₁ hs₂ hs₃ _ _ => exact .inl ⟨_, rfl⟩
  | lam hPi hb hs _ _ => exact .inr ⟨_, hPi⟩
  | app hf ha ihf _ =>
    rcases ihf with ⟨s, he⟩ | ⟨s, hPi⟩
    · cases he
    · obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
      exact .inr ⟨sB, hB.subst ha⟩
  | conv ht hB hc hs _ _ => exact .inr ⟨_, hB⟩

theorem BoundedTyping.pi_type (h : BoundedTyping n Γ f (.pi A B)) :
    ∃ s, BoundedTyping n Γ (.pi A B) (.srt s) := by
  rcases h.regularity with ⟨s, he⟩ | hs
  · cases he
  · exact hs

theorem bounded_beta_typing (hf : BoundedTyping n Γ (.lam A b) (.pi C D))
    (ha : BoundedTyping n Γ a C) :
    BoundedTyping n Γ (subst 0 a b) (subst 0 a D) := by
  obtain ⟨B, s, hPi, hb, _, hc⟩ := hf.generation
  obtain ⟨hcA, hcB⟩ := conv_pi_inj hc
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  have haA : BoundedTyping n Γ a A := .conv ha hA (conv_symm hcA) hsA
  have hsub := hb.subst haA
  obtain ⟨sT, hT⟩ := hf.pi_type
  obtain ⟨sD, hD, hsD⟩ := hT.pi_codomain
  apply BoundedTyping.conv hsub (hD.subst ha) ?_ hsD
  simpa only [subst_eq_sub] using conv_sub hcB (single a)

/-- A beta step preserves the original bound, including reductions in annotations. -/
theorem BoundedTyping.preservation (h : BoundedTyping n Γ t A) (hs : Step t t') :
    BoundedTyping n Γ t' A := by
  induction h using BoundedTyping.rec (motive_1 := fun _ _ => True)
      generalizing t' with
  | nil => trivial
  | cons => trivial
  | srt => cases hs
  | var => cases hs
  | pi hA hB hr hs₁ hs₂ hs₃ ihA ihB =>
    cases hs with
    | piDom B hAA' =>
      have hA' := ihA hAA'
      exact .pi hA' (hB.context_conv hA hA' hs₁ (.fwd (.refl _) hAA')) hr hs₁ hs₂ hs₃
    | piCod A hBB' => exact .pi hA (ihB hBB') hr hs₁ hs₂ hs₃
  | lam hPi hb hsn ihPi ihb =>
    cases hs with
    | lamTy b hAA' =>
      have hPi' := ihPi (.piDom _ hAA')
      obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
      obtain ⟨sA', hA', _⟩ := hPi'.pi_domain
      have hb' := hb.context_conv hA hA' hsA (.fwd (.refl _) hAA')
      exact .conv (.lam hPi' hb' hsn) hPi (.bwd (.refl _) (.piDom _ hAA')) hsn
    | lamBody A hbb' => exact .lam hPi (ihb hbb') hsn
  | app hf ha ihf iha =>
    cases hs with
    | beta A b a => exact bounded_beta_typing hf ha
    | appFun a hff' => exact .app (ihf hff') ha
    | appArg f haa' =>
      obtain ⟨sT, hT⟩ := hf.pi_type
      obtain ⟨sB, hB, hsB⟩ := hT.pi_codomain
      exact .conv (.app hf (iha haa')) (hB.subst ha)
        (conv_subst_arg (.bwd (.refl _) haa') _) hsB
  | conv ht hB hc hsn iht _ => exact .conv (iht hs) hB hc hsn

theorem BoundedTyping.preservation_steps (h : BoundedTyping n Γ t A)
    (hs : Steps t t') : BoundedTyping n Γ t' A := by
  induction hs with
  | refl => exact h
  | head hs hr ih => exact ih (h.preservation hs)

theorem BoundedTyping.preservation_par (h : BoundedTyping n Γ t A)
    (hs : Par t t') : BoundedTyping n Γ t' A := h.preservation_steps hs.steps

theorem BoundedTyping.preservation_red (h : BoundedTyping n Γ t A)
    (hs : Red t t') : BoundedTyping n Γ t' A := by
  induction hs with
  | refl => exact h
  | head hs hr ih => exact ih (h.preservation_par hs)

end Submission.Helpers
