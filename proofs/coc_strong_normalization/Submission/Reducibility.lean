import Submission.Helpers

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- Finite sequences of ordinary beta steps. -/
inductive Steps : Tm → Tm → Prop where
  | refl (t : Tm) : Steps t t
  | head : Step t u → Steps u v → Steps t v

theorem Steps.trans (h : Steps t u) (h' : Steps u v) : Steps t v := by
  induction h with
  | refl => exact h'
  | head hs hr ih => exact .head hs (ih h')

theorem Steps.map (h : Steps t u) (F : Tm → Tm)
    (hF : ∀ {t u}, Step t u → Step (F t) (F u)) : Steps (F t) (F u) := by
  induction h with
  | refl => exact .refl _
  | head hs hr ih => exact .head (hF hs) ih

theorem Steps.app (hf : Steps f f') (ha : Steps a a') : Steps (.app f a) (.app f' a') :=
  (hf.map (fun f => .app f a) (Step.appFun a)).trans
    (ha.map (Tm.app f') (Step.appArg f'))

theorem Steps.lam (hA : Steps A A') (hb : Steps b b') : Steps (.lam A b) (.lam A' b') :=
  (hA.map (fun A => .lam A b) (Step.lamTy b)).trans
    (hb.map (Tm.lam A') (Step.lamBody A'))

theorem Steps.pi (hA : Steps A A') (hB : Steps B B') : Steps (.pi A B) (.pi A' B') :=
  (hA.map (fun A => .pi A B) (Step.piDom B)).trans
    (hB.map (Tm.pi A') (Step.piCod A'))

theorem Par.steps (h : Par t u) : Steps t u := by
  induction h with
  | var => exact .refl _
  | srt => exact .refl _
  | app _ _ ihf iha => exact ihf.app iha
  | lam _ _ ihA ihb => exact ihA.lam ihb
  | pi _ _ ihA ihB => exact ihA.pi ihB
  | beta A _ _ ihb iha =>
    exact ((Steps.lam (.refl A) ihb).app iha).trans (.head (.beta _ _ _) (.refl _))

theorem step_sub (h : Step t u) (σ : Nat → Tm) : Step (sub σ t) (sub σ u) := by
  induction h generalizing σ with
  | beta A b a =>
    rw [sub_subst]
    exact .beta _ _ _
  | appFun a h ih => exact .appFun _ (ih _)
  | appArg f h ih => exact .appArg _ (ih _)
  | lamTy b h ih => exact .lamTy _ (ih _)
  | lamBody A h ih => exact .lamBody _ (ih _)
  | piDom B h ih => exact .piDom _ (ih _)
  | piCod A h ih => exact .piCod _ (ih _)

theorem sn_step (h : SN t) (hs : Step t u) : SN u := h.inv hs

theorem sn_steps (h : SN t) (hs : Steps t u) : SN u := by
  induction hs with
  | refl => exact h
  | head hs hr ih => exact ih (sn_step h hs)

theorem sn_of_sub (σ : Nat → Tm) (h : SN (sub σ t)) : SN t := by
  generalize he : sub σ t = v at h
  induction h generalizing t with
  | intro v hv ih =>
    apply Acc.intro t
    intro u hu
    apply ih (sub σ u)
    · rw [← he]
      exact step_sub hu σ
    · rfl

theorem sn_lam (hA : SN A) (hb : SN b) : SN (.lam A b) := by
  induction hA generalizing b with
  | intro A hA ihA =>
    induction hb with
    | intro b hb ihb =>
      apply Acc.intro
      intro u hu
      cases hu with
      | lamTy b h => exact ihA _ h (.intro _ hb)
      | lamBody A h => exact ihb _ h

theorem sn_pi (hA : SN A) (hB : SN B) : SN (.pi A B) := by
  induction hA generalizing B with
  | intro A hA ihA =>
    induction hB with
    | intro B hB ihB =>
      apply Acc.intro
      intro u hu
      cases hu with
      | piDom B h => exact ihA _ h (.intro _ hB)
      | piCod A h => exact ihB _ h

/-- Neutrality for reducibility candidates excludes abstractions. -/
def Neutral (t : Tm) : Prop := ∀ A b, t ≠ .lam A b

/-- Girard's three closure conditions, for the fully annotated reduction relation. -/
structure Candidate where
  contains : Tm → Prop
  normalizes : ∀ {t}, contains t → SN t
  reduce : ∀ {t u}, contains t → Step t u → contains u
  expand : ∀ {t}, Neutral t → (∀ u, Step t u → contains u) → contains t

theorem Candidate.steps (C : Candidate) (h : C.contains t) (hs : Steps t u) : C.contains u := by
  induction hs with
  | refl => exact h
  | head hs hr ih => exact ih (C.reduce h hs)

theorem Candidate.var (C : Candidate) (i : Nat) : C.contains (.var i) := by
  apply C.expand
  · intro A b h; cases h
  · intro u h; cases h

def Candidate.sn : Candidate where
  contains := SN
  normalizes := id
  reduce := sn_step
  expand := fun _ h => .intro _ h

theorem Candidate.beta (C : Candidate) (hA : SN A) (hb : SN b) (ha : SN a)
    (h : C.contains (subst 0 a b)) : C.contains (.app (.lam A b) a) := by
  induction hA generalizing b a with
  | intro A hA ihA =>
    induction hb generalizing a with
    | intro b hb ihb =>
      induction ha with
      | intro a ha iha =>
        apply C.expand
        · intro D c he; cases he
        · intro u hu
          cases hu with
          | beta => exact h
          | appFun a hf =>
            cases hf with
            | lamTy b hAA' => exact ihA _ hAA' (.intro _ hb) (.intro _ ha) h
            | lamBody A hbb' =>
              apply ihb _ hbb' (.intro _ ha)
              apply C.reduce h
              simpa only [subst_eq_sub] using step_sub hbb' (single a)
          | appArg f haa' =>
            apply iha _ haa'
            exact C.steps h ((Par.refl _).subst (step_par haa')).steps

theorem candidate_arrow_expand (A B : Candidate) (hn : Neutral t)
    (h : ∀ u, Step t u → ∀ a, A.contains a → B.contains (.app u a))
    (ha : A.contains a) : B.contains (.app t a) := by
  have hsn := A.normalizes ha
  revert ha
  induction hsn with
  | intro a hs ih =>
    intro ha
    apply B.expand
    · intro D c he; cases he
    · intro v hv
      cases hv with
      | beta D b _a => exact (hn D b rfl).elim
      | appFun a ht => exact h _ ht a ha
      | appArg t haa' => exact ih _ haa' (A.reduce ha haa')

def Candidate.arrow (A B : Candidate) : Candidate where
  contains t := SN t ∧ ∀ a, A.contains a → B.contains (.app t a)
  normalizes h := h.1
  reduce h hs := ⟨sn_step h.1 hs, fun a ha => B.reduce (h.2 a ha) (.appFun _ hs)⟩
  expand hn h := ⟨.intro _ (fun u hu => (h u hu).1),
    fun a ha => candidate_arrow_expand (a := a) A B hn (fun u hu => (h u hu).2) ha⟩

theorem Candidate.lambda (A B : Candidate) (hD : SN D)
    (h : ∀ a, A.contains a → B.contains (subst 0 a b)) :
    (A.arrow B).contains (.lam D b) := by
  have hb : SN b := by
    apply sn_of_sub (single (.var 0))
    simpa only [subst_eq_sub] using B.normalizes (h (.var 0) (A.var 0))
  exact ⟨sn_lam hD hb, fun a ha => B.beta hD hb (A.normalizes ha) (h a ha)⟩

/-- Arbitrary intersections retain an explicit normalization condition, including the empty case. -/
def Candidate.inter {I : Sort u} (C : I → Candidate) : Candidate where
  contains t := SN t ∧ ∀ i, (C i).contains t
  normalizes h := h.1
  reduce h hs := ⟨sn_step h.1 hs, fun i => (C i).reduce (h.2 i) hs⟩
  expand hn h := ⟨.intro _ (fun v hv => (h v hv).1),
    fun i => (C i).expand hn (fun v hv => (h v hv).2 i)⟩

/-- An inhabited semantic carrier together with a candidate for every semantic value. -/
structure RealizedType where
  Carrier : Type u
  point : Carrier
  realizes : Carrier → Candidate

def RealizedType.pi (A : RealizedType.{u}) (B : A.Carrier → RealizedType.{v}) :
    RealizedType.{max u v} where
  Carrier := ∀ x, (B x).Carrier
  point x := (B x).point
  realizes f := Candidate.inter (fun x => (A.realizes x).arrow ((B x).realizes (f x)))


theorem RealizedType.pi_apply (A : RealizedType.{u}) (B : A.Carrier → RealizedType.{v})
    {f : (A.pi B).Carrier} {x : A.Carrier}
    (hf : ((A.pi B).realizes f).contains t) (hx : (A.realizes x).contains a) :
    ((B x).realizes (f x)).contains (.app t a) :=
  (hf.2 x).2 a hx

theorem RealizedType.pi_lambda (A : RealizedType.{u}) (B : A.Carrier → RealizedType.{v})
    (f : (A.pi B).Carrier) (hD : SN D)
    (hb : ∀ x a, (A.realizes x).contains a →
      ((B x).realizes (f x)).contains (subst 0 a b)) :
    ((A.pi B).realizes f).contains (.lam D b) := by
  have h (x : A.Carrier) :=
    Candidate.lambda (A.realizes x) ((B x).realizes (f x)) hD (hb x)
  exact ⟨(h A.point).1, h⟩

end Submission.Helpers
