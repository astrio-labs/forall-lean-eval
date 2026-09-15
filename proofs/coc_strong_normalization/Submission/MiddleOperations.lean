import Submission.MiddleInference
import Submission.FiberOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def MiddleValue.piApply (A : Arity) (D B : A.ShapeEl → MiddleCode)
    (f : MiddleValue) (x : A.ShapeEl) (a : MiddleValue) : MiddleValue :=
  ⟨B x, MiddleCode.piApply A D B (f.cast (.pi A D B)) x (a.cast (D x))⟩

noncomputable def MiddleValue.piLambda (A : Arity) (D B : A.ShapeEl → MiddleCode)
    (f : A.ShapeEl → MiddleValue → MiddleValue) : MiddleValue :=
  ⟨.pi A D B, MiddleCode.piLambda A D B
    (fun x a => (f x ⟨D x, a⟩).cast (B x))⟩

theorem MiddleValue.piBeta (A : Arity) (D B : A.ShapeEl → MiddleCode)
    (f : A.ShapeEl → MiddleValue → MiddleValue) (x : A.ShapeEl) (a : MiddleValue)
    (ha : a.code = D x) (hf : (f x a).code = B x) :
    MiddleValue.piApply A D B (MiddleValue.piLambda A D B f) x a = f x a := by
  unfold MiddleValue.piApply MiddleValue.piLambda
  rw [MiddleValue.cast_mk, MiddleCode.piBeta, a.mk_cast ha]
  exact (f x a).mk_cast hf

theorem MiddleValue.piLambda_congr (A : Arity) (D B : A.ShapeEl → MiddleCode)
    (f g : A.ShapeEl → MiddleValue → MiddleValue)
    (h : ∀ x a, a.code = D x → f x a = g x a) :
    MiddleValue.piLambda A D B f = MiddleValue.piLambda A D B g := by
  unfold MiddleValue.piLambda
  congr 2
  funext x a
  rw [h x ⟨D x, a⟩ rfl]

noncomputable def middleApply (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (u : ShapeValue) (f : MiddleValue) (x : ShapeValue) (y : MiddleValue) : MiddleValue :=
  MiddleValue.piApply a (fun z => D ⟨a, z⟩)
    (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) f (x.cast a) y

noncomputable def middleLambda (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (u : ShapeValue) (f : ShapeValue → MiddleValue → MiddleValue) : MiddleValue :=
  MiddleValue.piLambda a (fun z => D ⟨a, z⟩)
    (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) (fun z => f ⟨a, z⟩)

theorem middleLambda_code (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (u : ShapeValue) (f : ShapeValue → MiddleValue → MiddleValue) :
    (middleLambda a D B u f).code = middleProduct a D B u := rfl

theorem middleApply_code (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (u : ShapeValue) (f : MiddleValue) (x : ShapeValue) (y : MiddleValue)
    (hx : x.code = a) : (middleApply a D B u f x y).code = B x (u.apply x) := by
  change B ⟨a, x.cast a⟩ (u.apply ⟨a, x.cast a⟩) = _
  rw [x.mk_cast hx]

theorem middleBeta (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (u : ShapeValue) (f : ShapeValue → MiddleValue → MiddleValue)
    (x : ShapeValue) (y : MiddleValue) (hx : x.code = a)
    (hy : y.code = D x) (hf : (f x y).code = B x (u.apply x)) :
    middleApply a D B u (middleLambda a D B u f) x y = f x y := by
  unfold middleApply middleLambda
  have h := MiddleValue.piBeta a (fun z => D ⟨a, z⟩)
    (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩))
    (fun z => f ⟨a, z⟩) (x.cast a) y
  simp only [x.mk_cast hx] at h
  exact h hy hf

theorem middleApply_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z) :
    middleApply a D B u f x y = middleApply a' D' B' u f x y := by
  subst a'
  have hd : (fun z : a.ShapeEl => D ⟨a, z⟩) = fun z => D' ⟨a, z⟩ :=
    funext (fun z => hD ⟨a, z⟩ rfl)
  have hb : (fun z : a.ShapeEl => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) =
      fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩) :=
    funext (fun z => hB ⟨a, z⟩ rfl _)
  unfold middleApply
  rw [hd, hb]

theorem middleLambda_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hf : ∀ x, x.code = a → ∀ y, y.code = D x → f x y = f' x y) :
    middleLambda a D B u f = middleLambda a' D' B' u f' := by
  subst a'
  have hd : (fun z : a.ShapeEl => D ⟨a, z⟩) = fun z => D' ⟨a, z⟩ :=
    funext (fun z => hD ⟨a, z⟩ rfl)
  have hb : (fun z : a.ShapeEl => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) =
      fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩) :=
    funext (fun z => hB ⟨a, z⟩ rfl _)
  unfold middleLambda
  rw [hd, hb]
  apply MiddleValue.piLambda_congr
  intro z y hy
  apply hf ⟨a, z⟩ rfl y
  exact hy.trans (hD ⟨a, z⟩ rfl).symm

/-- Conversion of product types preserves both the upper domain and all lower fibres. -/
theorem middleProduct_types_conv
    (hPi : BoundedTyping n Γ (.pi A B) (.srt s))
    (hPi' : BoundedTyping n Γ (.pi A' B') (.srt s'))
    (hc : Conv (.pi A B) (.pi A' B')) (hq : sortRank (.type i) + 1 = n)
    (hρ : ShapeContext (.type i) Γ ρ) :
    arityAt (.type i) A = arityAt (.type i) A' ∧
    (∀ x, middleShape n i Γ ρ A x = middleShape n i Γ ρ A' x) ∧
    (∀ x, x.code = arityAt (.type i) A → ∀ y,
      middleShape n i (A :: Γ) (push x ρ) B y =
        middleShape n i (A' :: Γ) (push x ρ) B' y) := by
  obtain ⟨sA, hA, hsA⟩ := hPi.pi_domain
  obtain ⟨sB, hB, hsB⟩ := hPi.pi_codomain
  obtain ⟨sA', hA', hsA'⟩ := hPi'.pi_domain
  obtain ⟨sB', hB', hsB'⟩ := hPi'.pi_codomain
  obtain ⟨hcA, hcB⟩ := conv_pi_inj hc
  refine ⟨arityAt_conv (hA.goodAt hq) (hA'.goodAt hq) hcA, ?_, ?_⟩
  · intro x
    exact middleShape_conv (.inl ⟨sA, hA⟩) (.inl ⟨sA', hA'⟩) hq hρ hcA
  · intro x hx y
    have hB'' := hB'.context_conv hA' hA hsA' (conv_symm hcA)
    calc
      middleShape n i (A :: Γ) (push x ρ) B y =
          middleShape n i (A :: Γ) (push x ρ) B' y :=
        middleShape_conv (.inl ⟨sB, hB⟩) (.inl ⟨sB', hB''⟩) hq (hρ.up hx) hcB
      _ = middleShape n i (A' :: Γ) (push x ρ) B' y :=
        (middleShape_context_conversion hB'' hA hA' hsA hcA hq).symm

end Submission.Helpers
