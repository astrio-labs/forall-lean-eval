import Submission.UpperGridTyping

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem upperGridProduct_congr {r : Nat} {a a' : Arity}
    {D D' : ShapeValue → (carrierGrid (r + 3) 1).Code}
    {B B' : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code}
    {d d' : ShapeValue → UpperGridValue r → UpperGridCode r}
    {c c' : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r}
    {u : ShapeValue} {f : UpperGridValue r} (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w) :
    upperGridProduct r a D B d c u f = upperGridProduct r a' D' B' d' c' u f := by
  subst a'
  unfold upperGridProduct
  congr 1
  funext x
  simp only [firstGridApply_congr rfl hD hB]
  erw [hD ⟨a, x⟩ rfl]
  congr 1
  funext y
  erw [hd ⟨a, x⟩ rfl _ (hD ⟨a, x⟩ rfl).symm,
    hc ⟨a, x⟩ rfl _ (hD ⟨a, x⟩ rfl).symm]

theorem inferredFirstGrid_ren (h : BoundedTyping (p + 3) Γ t A) (hw : BoundedWf (p + 3) Δ)
    (hr : RenCtx Γ Δ r) (hρ : ShapeContext (.type (p + 1)) Γ ρ)
    (hδ : ShapeContext (.type (p + 1)) Δ δ) (he : ∀ j, δ (r j) = ρ j) :
    inferredFirstGrid p Δ δ (ren r t) = inferredFirstGrid p Γ ρ t :=
  congrArg (firstGridCode p) (inferredMiddle_ren h hw hr rfl hρ hδ he)

end Submission.Helpers
