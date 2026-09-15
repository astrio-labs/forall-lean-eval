import Submission.FiberInference

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def FiberValue.force (A : FiberCode) (v : FiberValue) : FiberValue := ⟨A, v.cast A⟩

@[simp] theorem FiberValue.force_code (A : FiberCode) (v : FiberValue) :
    (v.force A).code = A := rfl

theorem FiberValue.force_eq (v : FiberValue) (h : v.code = A) : v.force A = v :=
  v.mk_cast h

noncomputable def fiberApply (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (u : ShapeValue) (f : FiberValue) (x : ShapeValue) (y : FiberValue) : FiberValue :=
  FiberValue.piApply a (fun z => D ⟨a, z⟩)
    (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) f (x.cast a) y

noncomputable def fiberLambda (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (u : ShapeValue) (f : ShapeValue → FiberValue → FiberValue) : FiberValue :=
  FiberValue.piLambda a (fun z => D ⟨a, z⟩)
    (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) (fun z => f ⟨a, z⟩)

theorem fiberLambda_code (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (u : ShapeValue) (f : ShapeValue → FiberValue → FiberValue) :
    (fiberLambda a D B u f).code = fiberProduct a D B u := rfl

theorem fiberApply_code (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (u : ShapeValue) (f : FiberValue) (x : ShapeValue) (y : FiberValue)
    (hx : x.code = a) : (fiberApply a D B u f x y).code = B x (u.apply x) := by
  change B ⟨a, x.cast a⟩ (u.apply ⟨a, x.cast a⟩) = _
  rw [x.mk_cast hx]

theorem fiberBeta (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (u : ShapeValue) (f : ShapeValue → FiberValue → FiberValue)
    (x : ShapeValue) (y : FiberValue) (hx : x.code = a)
    (hy : y.code = D x) (hf : (f x y).code = B x (u.apply x)) :
    fiberApply a D B u (fiberLambda a D B u f) x y = f x y := by
  unfold fiberApply fiberLambda
  have h := FiberValue.piBeta a (fun z => D ⟨a, z⟩)
    (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩))
    (fun z => f ⟨a, z⟩) (x.cast a) y
  simp only [x.mk_cast hx] at h
  exact h hy hf

theorem fiberApply_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z) :
    fiberApply a D B u f x y = fiberApply a' D' B' u f x y := by
  subst a'
  have hd : (fun z : a.ShapeEl => D ⟨a, z⟩) = fun z => D' ⟨a, z⟩ :=
    funext (fun z => hD ⟨a, z⟩ rfl)
  have hb : (fun z : a.ShapeEl => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) =
      fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩) :=
    funext (fun z => hB ⟨a, z⟩ rfl _)
  unfold fiberApply
  rw [hd, hb]

theorem fiberLambda_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hf : ∀ x, x.code = a → ∀ y, y.code = D x → f x y = f' x y) :
    fiberLambda a D B u f = fiberLambda a' D' B' u f' := by
  subst a'
  have hd : (fun z : a.ShapeEl => D ⟨a, z⟩) = fun z => D' ⟨a, z⟩ :=
    funext (fun z => hD ⟨a, z⟩ rfl)
  have hb : (fun z : a.ShapeEl => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) =
      fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩) :=
    funext (fun z => hB ⟨a, z⟩ rfl _)
  unfold fiberLambda
  rw [hd, hb]
  apply FiberValue.piLambda_congr
  intro z y hy
  apply hf ⟨a, z⟩ rfl y
  exact hy.trans (hD ⟨a, z⟩ rfl).symm

/-- An applicable term has a chosen product type; its components are only used up to conversion. -/
noncomputable def chosenProduct (n : Nat) (Γ : List Tm) (t : Tm) : Tm × Tm := by
  classical
  exact if h : ∃ p : Tm × Tm, BoundedTyping n Γ t (.pi p.1 p.2) then
    Classical.choose h else (.srt .prop, .srt .prop)

theorem chosenProduct_typing (h : BoundedTyping n Γ t (.pi A B)) :
    BoundedTyping n Γ t (.pi (chosenProduct n Γ t).1 (chosenProduct n Γ t).2) := by
  have hex : ∃ p : Tm × Tm, BoundedTyping n Γ t (.pi p.1 p.2) := ⟨(A, B), h⟩
  simpa only [chosenProduct, dif_pos hex] using Classical.choose_spec hex

theorem chosenProduct_conv (h : BoundedTyping n Γ t (.pi A B)) :
    Conv (chosenProduct n Γ t).1 A ∧ Conv (chosenProduct n Γ t).2 B :=
  conv_pi_inj (typing_unique (chosenProduct_typing h).forget h.forget)

/-- Conversion of product types preserves both the upper domain and all lower fibres. -/
theorem fiberProduct_types_conv
    (hPi : BoundedTyping n Γ (.pi A B) (.srt s))
    (hPi' : BoundedTyping n Γ (.pi A' B') (.srt s'))
    (hc : Conv (.pi A B) (.pi A' B')) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) :
    arityAt (.type i) A = arityAt (.type i) A' ∧
    (∀ x, fiberShape n i Γ ρ A x = fiberShape n i Γ ρ A' x) ∧
    (∀ x, x.code = arityAt (.type i) A → ∀ y,
      fiberShape n i (A :: Γ) (push x ρ) B y =
        fiberShape n i (A' :: Γ) (push x ρ) B' y) := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi.pi_codomain
  obtain ⟨sA', hA', hsA'⟩ := hPi'.pi_domain
  obtain ⟨sB', hB', hsB'⟩ := hPi'.pi_codomain
  obtain ⟨hcA, hcB⟩ := conv_pi_inj hc
  refine ⟨arityAt_conv (hA.goodAt hq) (hA'.goodAt hq) hcA, ?_, ?_⟩
  · intro x
    exact fiberShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hq hρ hcA
  · intro x hx y
    have hB'' := hB'.context_conv hA' hA hsA' (conv_symm hcA)
    calc
      fiberShape n i (A :: Γ) (push x ρ) B y =
          fiberShape n i (A :: Γ) (push x ρ) B' y :=
        fiberShape_conv (.inl ⟨sB, hB⟩) (.inl ⟨sB', hB''⟩) hq (hρ.up hx) hcB
      _ = fiberShape n i (A' :: Γ) (push x ρ) B' y :=
        (fiberShape_context_conversion hB'' hA hA' hsA hcA hq).symm

end Submission.Helpers
