import Submission.SecondGridCongruence

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

variable {I S J : CarrierSystem}

theorem CarrierQuantifiers.overCode_congr (Q : CarrierQuantifiers I S)
    {A A' : I.Code} {B B' : TowerValue I → S.Code} (ha : A = A')
    (hb : ∀ x, x.code = A → B x = B' x) :
    Q.code A (fun x => B ⟨A, x⟩) = Q.code A' (fun x => B' ⟨A', x⟩) := by
  subst A'
  apply congrArg (Q.code A)
  funext x
  exact hb ⟨A, x⟩ rfl

theorem CarrierQuantifiers.representedCode_congr (Q : CarrierQuantifiers I S) (R : CarrierRepresentation J I)
    {A A' : J.Code} {B B' : TowerValue J → S.Code} (ha : A = A')
    (hb : ∀ x, x.code = A → B x = B' x) :
    Q.code (R.code A) (fun x => B ⟨A, (R.values A).decode x⟩) =
      Q.code (R.code A') (fun x => B' ⟨A', (R.values A').decode x⟩) := by
  subst A'
  apply congrArg (Q.code (R.code A))
  funext x
  exact hb ⟨A, (R.values A).decode x⟩ rfl

variable {r : Nat} {a a' : Arity}
  {D D' : ShapeValue → (carrierGrid (r + 4) 1).Code}
  {B B' : ShapeValue → ShapeValue → (carrierGrid (r + 4) 1).Code}
  {d d' : ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code}
  {c c' : ShapeValue → UpperGridValue (r + 1) → ShapeValue → UpperGridValue (r + 1) → (carrierGrid (r + 4) 2).Code}
  {E E' : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r}
  {F F' : ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r →
    ShapeValue → UpperGridValue (r + 1) → SecondLayerValue r → SecondLayerCode r}
  {u : ShapeValue} {f : UpperGridValue (r + 1)} {g : SecondLayerValue r}

theorem secondLayerProduct_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w)
    (hE : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y → E x y z = E' x y z)
    (hF : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y →
      ∀ v w q, F x y z v w q = F' x y z v w q) :
    secondLayerProduct r a D B d c E F u f g = secondLayerProduct r a' D' B' d' c' E' F' u f g := by
  subst a'
  unfold secondLayerProduct
  apply congrArg ((carrierGridQuantifiers (r + 3) 2).code (.small (.small a)))
  funext x
  apply (carrierGridQuantifiers (r + 3) 2).representedCode_congr (carrierGridHorizontal (r + 4) 1 (by omega))
    (B := fun y => (carrierGridQuantifiers (r + 3) 2).code (d ⟨a, x⟩ y) (fun z =>
      (carrierGridArrows (r + 4) 3).code (E ⟨a, x⟩ y ⟨d ⟨a, x⟩ y, z⟩)
        (F ⟨a, x⟩ y ⟨d ⟨a, x⟩ y, z⟩ (u.apply ⟨a, x⟩) (firstGridApply (r + 2) a D B u f ⟨a, x⟩ y)
          (secondGridApply (r + 1) a D B d c u f g ⟨a, x⟩ y ⟨d ⟨a, x⟩ y, z⟩))))
    (B' := fun y => (carrierGridQuantifiers (r + 3) 2).code (d' ⟨a, x⟩ y) (fun z =>
      (carrierGridArrows (r + 4) 3).code (E' ⟨a, x⟩ y ⟨d' ⟨a, x⟩ y, z⟩)
        (F' ⟨a, x⟩ y ⟨d' ⟨a, x⟩ y, z⟩ (u.apply ⟨a, x⟩) (firstGridApply (r + 2) a D' B' u f ⟨a, x⟩ y)
          (secondGridApply (r + 1) a D' B' d' c' u f g ⟨a, x⟩ y ⟨d' ⟨a, x⟩ y, z⟩))))
    (hD ⟨a, x⟩ rfl)
  intro y hy
  apply (carrierGridQuantifiers (r + 3) 2).overCode_congr
    (B := fun z => (carrierGridArrows (r + 4) 3).code (E ⟨a, x⟩ y z)
      (F ⟨a, x⟩ y z (u.apply ⟨a, x⟩) (firstGridApply (r + 2) a D B u f ⟨a, x⟩ y)
        (secondGridApply (r + 1) a D B d c u f g ⟨a, x⟩ y z)))
    (B' := fun z => (carrierGridArrows (r + 4) 3).code (E' ⟨a, x⟩ y z)
      (F' ⟨a, x⟩ y z (u.apply ⟨a, x⟩) (firstGridApply (r + 2) a D' B' u f ⟨a, x⟩ y)
        (secondGridApply (r + 1) a D' B' d' c' u f g ⟨a, x⟩ y z)))
    (hd ⟨a, x⟩ rfl y hy)
  intro z hz
  erw [hE ⟨a, x⟩ rfl y hy z hz, hF ⟨a, x⟩ rfl y hy z hz,
    firstGridApply_congr rfl hD hB, secondGridApply_congr rfl hD hB hd hc]

end Submission.Helpers
