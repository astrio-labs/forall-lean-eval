import Submission.SecondLayerDecoding

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

variable {I S : CarrierSystem}

theorem CarrierQuantifiers.twoValueLambda_congr (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code)
    (f f' : (x : I.El a) → I.El (D x) → TowerValue S → TowerValue S)
    (hf : ∀ x y z, z.code = d x y → f x y z = f' x y z) :
    Q.twoValueLambda P a D d c f = Q.twoValueLambda P a D d c f' := by
  have he : (fun x y z => (f x y ⟨d x y, z⟩).cast (c x y)) =
      fun x y z => (f' x y ⟨d x y, z⟩).cast (c x y) := by
    funext x y z
    rw [hf x y ⟨d x y, z⟩ rfl]
  unfold twoValueLambda
  rw [he]

noncomputable def CarrierQuantifiers.twoOverApply (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (C E : I.El a → TowerValue I → S.Code)
    (f : TowerValue S) (x : I.El a) (y : TowerValue I) (z : TowerValue S) : TowerValue S :=
  Q.twoValueApply P a D (fun x y => C x ⟨D x, y⟩) (fun x y => E x ⟨D x, y⟩) f x (y.cast (D x)) z

noncomputable def CarrierQuantifiers.twoOverLambda (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (C E : I.El a → TowerValue I → S.Code)
    (f : I.El a → TowerValue I → TowerValue S → TowerValue S) : TowerValue S :=
  Q.twoValueLambda P a D (fun x y => C x ⟨D x, y⟩) (fun x y => E x ⟨D x, y⟩) (fun x y => f x ⟨D x, y⟩)

theorem CarrierQuantifiers.twoOverApply_congr (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    {a : I.Code} {D D' : I.El a → I.Code} {f z : TowerValue S} {x : I.El a} {y : TowerValue I}
    {C C' E E' : I.El a → TowerValue I → S.Code} (hD : D = D')
    (hC : ∀ x y, y.code = D x → C x y = C' x y)
    (hE : ∀ x y, y.code = D x → E x y = E' x y) :
    Q.twoOverApply P a D C E f x y z = Q.twoOverApply P a D' C' E' f x y z := by
  subst D'
  have hc : (fun x w => C x (TowerValue.mk (D x) w)) =
      fun x w => C' x (TowerValue.mk (D x) w) := funext (fun x => funext (fun w => hC x ⟨D x, w⟩ rfl))
  have he : (fun x w => E x (TowerValue.mk (D x) w)) =
      fun x w => E' x (TowerValue.mk (D x) w) := funext (fun x => funext (fun w => hE x ⟨D x, w⟩ rfl))
  unfold twoOverApply
  rw [hc, he]

theorem CarrierQuantifiers.twoOverLambda_congr (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    {a : I.Code} {D D' : I.El a → I.Code}
    {f f' : I.El a → TowerValue I → TowerValue S → TowerValue S}
    {C C' E E' : I.El a → TowerValue I → S.Code} (hD : D = D')
    (hC : ∀ x y, y.code = D x → C x y = C' x y)
    (hE : ∀ x y, y.code = D x → E x y = E' x y)
    (hf : ∀ x y, y.code = D x → ∀ z, z.code = C x y → f x y z = f' x y z) :
    Q.twoOverLambda P a D C E f = Q.twoOverLambda P a D' C' E' f' := by
  subst D'
  have hc : (fun x w => C x (TowerValue.mk (D x) w)) =
      fun x w => C' x (TowerValue.mk (D x) w) := funext (fun x => funext (fun w => hC x ⟨D x, w⟩ rfl))
  have he : (fun x w => E x (TowerValue.mk (D x) w)) =
      fun x w => E' x (TowerValue.mk (D x) w) := funext (fun x => funext (fun w => hE x ⟨D x, w⟩ rfl))
  unfold twoOverLambda
  rw [hc, he]
  apply Q.twoValueLambda_congr
  intro x y z hz
  exact hf x ⟨D x, y⟩ rfl z (hz.trans (hC x ⟨D x, y⟩ rfl).symm)

variable {p : Nat} {a a' : Arity}
  {D D' : ShapeValue → (carrierGrid (p + 3) 1).Code}
  {B B' : ShapeValue → ShapeValue → (carrierGrid (p + 3) 1).Code}
  {d d' : ShapeValue → UpperGridValue p → UpperGridCode p}
  {c c' : ShapeValue → UpperGridValue p → ShapeValue → UpperGridValue p → UpperGridCode p}
  {u x : ShapeValue} {f y : UpperGridValue p} {z : SecondGridValue p}

theorem secondGridApply_congr {g : SecondGridValue p} (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w) :
    secondGridApply p a D B d c u f g x y z = secondGridApply p a' D' B' d' c' u f g x y z := by
  subst a'
  apply (carrierGridQuantifiers (p + 2) 1).twoOverApply_congr (carrierGridArrows (p + 3) 2) (a := .small a)
    (C := fun x => d ⟨a, x⟩) (C' := fun x => d' ⟨a, x⟩)
    (E := fun x y => c ⟨a, x⟩ y (u.apply ⟨a, x⟩) (firstGridApply (p + 1) a D B u f ⟨a, x⟩ y))
    (E' := fun x y => c' ⟨a, x⟩ y (u.apply ⟨a, x⟩) (firstGridApply (p + 1) a D' B' u f ⟨a, x⟩ y))
    (f := g) (x := x.cast a) (y := y) (z := z)
    (funext (fun x : a.ShapeEl => hD ⟨a, x⟩ rfl))
  · intro x y hy; exact hd ⟨a, x⟩ rfl y hy
  · intro x y hy
    rw [hc ⟨a, x⟩ rfl y hy, firstGridApply_congr rfl hD hB]

theorem secondGridLambda_congr {g g' : ShapeValue → UpperGridValue p → SecondGridValue p → SecondGridValue p}
    (ha : a = a') (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w)
    (hg : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y → g x y z = g' x y z) :
    secondGridLambda p a D B d c u f g = secondGridLambda p a' D' B' d' c' u f g' := by
  subst a'
  apply (carrierGridQuantifiers (p + 2) 1).twoOverLambda_congr (carrierGridArrows (p + 3) 2) (a := .small a)
    (C := fun x => d ⟨a, x⟩) (C' := fun x => d' ⟨a, x⟩)
    (E := fun x y => c ⟨a, x⟩ y (u.apply ⟨a, x⟩) (firstGridApply (p + 1) a D B u f ⟨a, x⟩ y))
    (E' := fun x y => c' ⟨a, x⟩ y (u.apply ⟨a, x⟩) (firstGridApply (p + 1) a D' B' u f ⟨a, x⟩ y))
    (f := fun x => g ⟨a, x⟩) (f' := fun x => g' ⟨a, x⟩)
    (funext (fun x : a.ShapeEl => hD ⟨a, x⟩ rfl))
  · intro x y hy; exact hd ⟨a, x⟩ rfl y hy
  · intro x y hy
    rw [hc ⟨a, x⟩ rfl y hy, firstGridApply_congr rfl hD hB]
  · intro x y hy z hz; exact hg ⟨a, x⟩ rfl y hy z hz

end Submission.Helpers
