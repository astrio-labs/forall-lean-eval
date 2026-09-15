import ChallengeDeps

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization

set_option autoImplicit true

/-- Renaming and simultaneous substitution, including their action under a binder. -/
def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def ren (ρ : Nat → Nat) : Tm → Tm
  | .var i => .var (ρ i)
  | .srt s => .srt s
  | .app f a => .app (ren ρ f) (ren ρ a)
  | .lam A b => .lam (ren ρ A) (ren (upRen ρ) b)
  | .pi A B => .pi (ren ρ A) (ren (upRen ρ) B)

def upSub (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | n + 1 => ren Nat.succ (σ n)

def sub (σ : Nat → Tm) : Tm → Tm
  | .var i => σ i
  | .srt s => .srt s
  | .app f a => .app (sub σ f) (sub σ a)
  | .lam A b => .lam (sub σ A) (sub (upSub σ) b)
  | .pi A B => .pi (sub σ A) (sub (upSub σ) B)

@[simp] theorem upRen_id : upRen id = id := by
  funext i; cases i <;> rfl

@[simp] theorem upRen_comp (ρ τ : Nat → Nat) :
    upRen ρ ∘ upRen τ = upRen (ρ ∘ τ) := by
  funext i; cases i <;> rfl

@[simp] theorem ren_id (t : Tm) : ren id t = t := by
  induction t <;> simp_all [ren]

theorem ren_comp (ρ τ : Nat → Nat) (t : Tm) :
    ren ρ (ren τ t) = ren (ρ ∘ τ) t := by
  induction t generalizing ρ τ <;> simp_all [ren, upRen_comp]

@[simp] theorem upSub_var : upSub Tm.var = Tm.var := by
  funext i; cases i <;> rfl

@[simp] theorem sub_var (t : Tm) : sub Tm.var t = t := by
  induction t <;> simp_all [sub]

theorem sub_ren (σ : Nat → Tm) (ρ : Nat → Nat) (t : Tm) :
    sub σ (ren ρ t) = sub (σ ∘ ρ) t := by
  have h (σ : Nat → Tm) (ρ : Nat → Nat) :
      upSub σ ∘ upRen ρ = upSub (σ ∘ ρ) := by
    funext i; cases i <;> rfl
  induction t generalizing σ ρ <;> simp_all [sub, ren]

theorem ren_sub (ρ : Nat → Nat) (σ : Nat → Tm) (t : Tm) :
    ren ρ (sub σ t) = sub (fun i => ren ρ (σ i)) t := by
  have h (ρ : Nat → Nat) (σ : Nat → Tm) :
      (fun i => ren (upRen ρ) (upSub σ i)) = upSub (fun i => ren ρ (σ i)) := by
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [upSub, ren_comp]; rfl
  induction t generalizing σ ρ <;> simp_all [sub, ren]

theorem sub_up_ren (σ : Nat → Tm) (t : Tm) :
    sub (upSub σ) (ren Nat.succ t) = ren Nat.succ (sub σ t) := by
  rw [sub_ren, ren_sub]
  rfl

theorem sub_comp (σ τ : Nat → Tm) (t : Tm) :
    sub σ (sub τ t) = sub (fun i => sub σ (τ i)) t := by
  have h (σ τ : Nat → Tm) :
      (fun i => sub (upSub σ) (upSub τ i)) = upSub (fun i => sub σ (τ i)) := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact sub_up_ren σ (τ i)
  induction t generalizing σ τ <;> simp_all [sub]

def shift (d c i : Nat) : Nat := if i < c then i else i + d

@[simp] theorem upRen_shift (d c : Nat) : upRen (shift d c) = shift d (c + 1) := by
  funext i
  cases i with
  | zero => simp [upRen, shift]
  | succ i =>
    simp only [upRen, shift, Nat.succ_lt_succ_iff, Nat.add_right_comm]
    split <;> rfl

theorem ren_shift (d c : Nat) (t : Tm) : ren (shift d c) t = lift d c t := by
  induction t generalizing c <;> simp_all [ren, lift, shift]
  split <;> rfl

@[simp] theorem lift_zero (c : Nat) (t : Tm) : lift 0 c t = t := by
  rw [← ren_shift]
  have h : shift 0 c = id := by funext i; simp [shift]
  rw [h, ren_id]

theorem lift_one (t : Tm) : lift 1 0 t = ren Nat.succ t := by
  rw [← ren_shift]
  rfl


theorem ren_succ_lift (k : Nat) (t : Tm) :
    ren Nat.succ (lift k 0 t) = lift (k + 1) 0 t := by
  rw [← ren_shift, ← ren_shift, ren_comp]
  congr 1

def replace (k : Nat) (u : Tm) (i : Nat) : Tm :=
  if i < k then .var i else if i = k then lift k 0 u else .var (i - 1)

@[simp] theorem upSub_replace (k : Nat) (u : Tm) :
    upSub (replace k u) = replace (k + 1) u := by
  funext i
  cases i with
  | zero => simp [upSub, replace]
  | succ i =>
    simp only [upSub, replace, Nat.succ_lt_succ_iff, Nat.succ.injEq]
    split
    · rfl
    · split
      · exact ren_succ_lift k u
      · simp only [ren, Tm.var.injEq]
        omega

theorem sub_replace (k : Nat) (u t : Tm) : sub (replace k u) t = subst k u t := by
  induction t generalizing k <;> simp_all [sub, subst, replace]

def single (u : Tm) : Nat → Tm
  | 0 => u
  | i + 1 => .var i

@[simp] theorem replace_zero (u : Tm) : replace 0 u = single u := by
  funext i
  cases i <;> simp [replace, single]

theorem subst_eq_sub (u t : Tm) : subst 0 u t = sub (single u) t := by
  rw [← sub_replace, replace_zero]

@[simp] theorem single_ren_succ (u t : Tm) :
    sub (single u) (ren Nat.succ t) = t := by
  rw [sub_ren]
  exact sub_var t

theorem ren_subst (ρ : Nat → Nat) (u t : Tm) :
    ren ρ (subst 0 u t) = subst 0 (ren ρ u) (ren (upRen ρ) t) := by
  simp only [subst_eq_sub, ren_sub, sub_ren]
  congr 1
  funext i
  cases i <;> rfl

theorem sub_subst (σ : Nat → Tm) (u t : Tm) :
    sub σ (subst 0 u t) = subst 0 (sub σ u) (sub (upSub σ) t) := by
  simp only [subst_eq_sub, sub_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [single, upSub, sub]

/-- Parallel beta reduction. -/
inductive Par : Tm → Tm → Prop where
  | var (i : Nat) : Par (.var i) (.var i)
  | srt (s : Srt) : Par (.srt s) (.srt s)
  | app : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | lam : Par A A' → Par b b' → Par (.lam A b) (.lam A' b')
  | pi : Par A A' → Par B B' → Par (.pi A B) (.pi A' B')
  | beta (A : Tm) : Par b b' → Par a a' →
      Par (.app (.lam A b) a) (subst 0 a' b')

theorem Par.refl (t : Tm) : Par t t := by
  induction t with
  | var i => exact .var i
  | srt s => exact .srt s
  | app f a ihf iha => exact .app ihf iha
  | lam A b ihA ihb => exact .lam ihA ihb
  | pi A B ihA ihB => exact .pi ihA ihB

theorem Par.rename (h : Par t u) (ρ : Nat → Nat) : Par (ren ρ t) (ren ρ u) := by
  induction h generalizing ρ with
  | var i => exact .var _
  | srt s => exact .srt _
  | app _ _ ihf iha => exact .app (ihf _) (iha _)
  | lam _ _ ihA ihb => exact .lam (ihA _) (ihb _)
  | pi _ _ ihA ihB => exact .pi (ihA _) (ihB _)
  | beta A _ _ ihb iha =>
    rw [ren_subst]
    exact .beta _ (ihb _) (iha _)

theorem Par.substitute (h : Par t u) (σ τ : Nat → Tm)
    (hστ : ∀ i, Par (σ i) (τ i)) : Par (sub σ t) (sub τ u) := by
  have hup (σ τ : Nat → Tm) (h : ∀ i, Par (σ i) (τ i)) :
      ∀ i, Par (upSub σ i) (upSub τ i) := by
    intro i
    cases i with
    | zero => exact .var _
    | succ i => exact (h i).rename _
  induction h generalizing σ τ with
  | var i => exact hστ i
  | srt s => exact .srt _
  | app _ _ ihf iha => exact .app (ihf _ _ hστ) (iha _ _ hστ)
  | lam _ _ ihA ihb => exact .lam (ihA _ _ hστ) (ihb _ _ (hup _ _ hστ))
  | pi _ _ ihA ihB => exact .pi (ihA _ _ hστ) (ihB _ _ (hup _ _ hστ))
  | beta A _ _ ihb iha =>
    rw [sub_subst]
    exact .beta _ (ihb _ _ (hup _ _ hστ)) (iha _ _ hστ)

theorem Par.subst (hb : Par b b') (ha : Par a a') :
    Par (subst 0 a b) (subst 0 a' b') := by
  simp only [subst_eq_sub]
  apply hb.substitute
  intro i
  cases i with
  | zero => exact ha
  | succ i => exact .var _

def dev : Tm → Tm
  | .var i => .var i
  | .srt s => .srt s
  | .app (.lam _ b) a => subst 0 (dev a) (dev b)
  | .app f a => .app (dev f) (dev a)
  | .lam A b => .lam (dev A) (dev b)
  | .pi A B => .pi (dev A) (dev B)

theorem Par.develop (h : Par t u) : Par u (dev t) := by
  induction h with
  | var i => exact .var _
  | srt s => exact .srt _
  | @app f f' a a' hf ha ihf iha =>
    cases f with
    | var i => exact .app ihf iha
    | srt s => exact .app ihf iha
    | app g c => exact .app ihf iha
    | pi A B => exact .app ihf iha
    | lam A b =>
      cases hf with
      | lam hA hb =>
        cases ihf with
        | lam ihA ihb => exact .beta _ ihb iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | beta A _ _ ihb iha => exact ihb.subst iha

theorem Par.diamond (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w := ⟨dev t, hu.develop, hv.develop⟩

/-- The reflexive transitive closure of parallel reduction. -/
inductive Red : Tm → Tm → Prop where
  | refl (t : Tm) : Red t t
  | head : Par t u → Red u v → Red t v

theorem Par.red (h : Par t u) : Red t u := .head h (.refl _)

theorem Red.trans (h : Red t u) (h' : Red u v) : Red t v := by
  induction h with
  | refl => exact h'
  | head hp hr ih => exact .head hp (ih h')

theorem Red.strip (h : Red t u) (h' : Par t v) :
    ∃ w, Par u w ∧ Red v w := by
  induction h generalizing v with
  | refl => exact ⟨v, h', .refl _⟩
  | head hp hr ih =>
    obtain ⟨w, hw₁, hw₂⟩ := hp.diamond h'
    obtain ⟨z, hz₁, hz₂⟩ := ih hw₁
    exact ⟨z, hz₁, .head hw₂ hz₂⟩

theorem Red.confluent (hu : Red t u) (hv : Red t v) :
    ∃ w, Red u w ∧ Red v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, .refl _⟩
  | head hp hr ih =>
    obtain ⟨z, hz₁, hz₂⟩ := hv.strip hp
    obtain ⟨w, hw₁, hw₂⟩ := ih hz₂
    exact ⟨w, hw₁, .head hz₁ hw₂⟩

theorem step_par (h : Step t u) : Par t u := by
  induction h with
  | beta A b a => exact .beta A (.refl b) (.refl a)
  | appFun a h ih => exact .app ih (.refl a)
  | appArg f h ih => exact .app (.refl f) ih
  | lamTy b h ih => exact .lam ih (.refl b)
  | lamBody A h ih => exact .lam (.refl A) ih
  | piDom B h ih => exact .pi ih (.refl B)
  | piCod A h ih => exact .pi (.refl A) ih

theorem conv_join (h : Conv t u) : ∃ w, Red t w ∧ Red u w := by
  induction h with
  | refl => exact ⟨_, .refl _, .refl _⟩
  | fwd h hs ih =>
    obtain ⟨w, hw₁, hw₂⟩ := ih
    obtain ⟨z, hz₁, hz₂⟩ := hw₂.strip (step_par hs)
    exact ⟨z, hw₁.trans hz₁.red, hz₂⟩
  | bwd h hs ih =>
    obtain ⟨w, hw₁, hw₂⟩ := ih
    exact ⟨w, hw₁, .head (step_par hs) hw₂⟩


theorem conv_trans (h : Conv t u) (h' : Conv u v) : Conv t v := by
  induction h' with
  | refl => exact h
  | fwd _ hs ih => exact .fwd ih hs
  | bwd _ hs ih => exact .bwd ih hs

theorem conv_symm (h : Conv t u) : Conv u t := by
  induction h with
  | refl => exact .refl _
  | fwd _ hs ih => exact conv_trans (.bwd (.refl _) hs) ih
  | bwd _ hs ih => exact conv_trans (.fwd (.refl _) hs) ih

theorem conv_map (F : Tm → Tm) (hF : ∀ {t u}, Step t u → Step (F t) (F u))
    (h : Conv t u) : Conv (F t) (F u) := by
  induction h with
  | refl => exact .refl _
  | fwd _ hs ih => exact .fwd ih (hF hs)
  | bwd _ hs ih => exact .bwd ih (hF hs)

theorem conv_app (hf : Conv f f') (ha : Conv a a') : Conv (.app f a) (.app f' a') :=
  conv_trans (conv_map (fun f => .app f a) (Step.appFun a) hf)
    (conv_map (Tm.app f') (Step.appArg f') ha)

theorem conv_lam (hA : Conv A A') (hb : Conv b b') : Conv (.lam A b) (.lam A' b') :=
  conv_trans (conv_map (fun A => .lam A b) (Step.lamTy b) hA)
    (conv_map (Tm.lam A') (Step.lamBody A') hb)

theorem conv_pi (hA : Conv A A') (hB : Conv B B') : Conv (.pi A B) (.pi A' B') :=
  conv_trans (conv_map (fun A => .pi A B) (Step.piDom B) hA)
    (conv_map (Tm.pi A') (Step.piCod A') hB)

theorem Par.conv (h : Par t u) : Conv t u := by
  induction h with
  | var i => exact .refl _
  | srt s => exact .refl _
  | app _ _ ihf iha => exact conv_app ihf iha
  | lam _ _ ihA ihb => exact conv_lam ihA ihb
  | pi _ _ ihA ihB => exact conv_pi ihA ihB
  | beta A _ _ ihb iha =>
    exact .fwd (conv_app (conv_lam (.refl A) ihb) iha) (.beta _ _ _)

theorem Red.conv (h : Red t u) : Conv t u := by
  induction h with
  | refl => exact .refl _
  | head hp hr ih => exact conv_trans hp.conv ih

theorem conv_ren (h : Conv t u) (ρ : Nat → Nat) : Conv (ren ρ t) (ren ρ u) := by
  induction h with
  | refl => exact .refl _
  | fwd _ hs ih => exact conv_trans ih ((step_par hs).rename ρ).conv
  | bwd _ hs ih => exact conv_trans ih (conv_symm ((step_par hs).rename ρ).conv)

theorem conv_sub (h : Conv t u) (σ : Nat → Tm) : Conv (sub σ t) (sub σ u) := by
  induction h with
  | refl => exact .refl _
  | fwd _ hs ih =>
    exact conv_trans ih ((step_par hs).substitute σ σ (fun _ => .refl _)).conv
  | bwd _ hs ih =>
    exact conv_trans ih (conv_symm ((step_par hs).substitute σ σ (fun _ => .refl _)).conv)

theorem conv_sub_env (h : ∀ i, Conv (σ i) (τ i)) (t : Tm) : Conv (sub σ t) (sub τ t) := by
  have hup {σ τ : Nat → Tm} (h : ∀ i, Conv (σ i) (τ i)) :
      ∀ i, Conv (upSub σ i) (upSub τ i) := by
    intro i
    cases i with
    | zero => exact .refl _
    | succ i => exact conv_ren (h i) _
  induction t generalizing σ τ with
  | var i => exact h i
  | srt s => exact .refl _
  | app f a ihf iha => exact conv_app (ihf h) (iha h)
  | lam A b ihA ihb => exact conv_lam (ihA h) (ihb (hup h))
  | pi A B ihA ihB => exact conv_pi (ihA h) (ihB (hup h))

theorem conv_subst_arg (h : Conv a a') (b : Tm) : Conv (subst 0 a b) (subst 0 a' b) := by
  simp only [subst_eq_sub]
  apply conv_sub_env
  intro i
  cases i with
  | zero => exact h
  | succ i => exact .refl _

theorem red_pi (h : Red t u) : ∀ A B, t = .pi A B →
    ∃ A' B', u = .pi A' B' ∧ Red A A' ∧ Red B B' := by
  induction h with
  | refl t =>
    intro A B ht
    exact ⟨A, B, ht, .refl _, .refl _⟩
  | head hp hr ih =>
    intro A B ht
    subst ht
    cases hp with
    | pi hA hB =>
      obtain ⟨A', B', hu, hA', hB'⟩ := ih _ _ rfl
      exact ⟨A', B', hu, .head hA hA', .head hB hB'⟩

theorem red_srt (h : Red t u) : ∀ s, t = .srt s → u = .srt s := by
  induction h with
  | refl t => exact fun _ h => h
  | head hp hr ih =>
    intro s ht
    subst ht
    cases hp with
    | srt => exact ih _ rfl

theorem red_var (h : Red t u) : ∀ i, t = .var i → u = .var i := by
  induction h with
  | refl t => exact fun _ h => h
  | head hp hr ih =>
    intro i ht
    subst ht
    cases hp with
    | var => exact ih _ rfl

theorem conv_pi_inj (h : Conv (.pi A B) (.pi A' B')) : Conv A A' ∧ Conv B B' := by
  obtain ⟨w, hw, hw'⟩ := conv_join h
  obtain ⟨C, D, he, hA, hB⟩ := red_pi hw A B rfl
  obtain ⟨C', D', he', hA', hB'⟩ := red_pi hw' A' B' rfl
  have heq := Tm.pi.inj (he.symm.trans he')
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨conv_trans hA.conv (conv_symm hA'.conv),
    conv_trans hB.conv (conv_symm hB'.conv)⟩

theorem conv_srt_inj (h : Conv (.srt s) (.srt s')) : s = s' := by
  obtain ⟨w, hw, hw'⟩ := conv_join h
  exact Tm.srt.inj ((red_srt hw s rfl).symm.trans (red_srt hw' s' rfl))

theorem not_conv_pi_srt : ¬ Conv (.pi A B) (.srt s) := by
  intro h
  obtain ⟨w, hw, hw'⟩ := conv_join h
  obtain ⟨C, D, he, _, _⟩ := red_pi hw A B rfl
  have := he.symm.trans (red_srt hw' s rfl)
  cases this

theorem not_conv_var_srt : ¬ Conv (.var i) (.srt s) := by
  intro h
  obtain ⟨w, hw, hw'⟩ := conv_join h
  have := (red_var hw i rfl).symm.trans (red_srt hw' s rfl)
  cases this

theorem not_conv_pi_var : ¬ Conv (.pi A B) (.var i) := by
  intro h
  obtain ⟨w, hw, hw'⟩ := conv_join h
  obtain ⟨C, D, he, _, _⟩ := red_pi hw A B rfl
  have := he.symm.trans (red_var hw' i rfl)
  cases this

end Submission.Helpers
