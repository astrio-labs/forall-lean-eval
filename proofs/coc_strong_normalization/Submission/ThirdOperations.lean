import Submission.ThirdInference

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def ThirdValue.overApply (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : a.ShapeEl → MiddleValue → ThirdCode) (f : ThirdValue)
    (x : a.ShapeEl) (y : MiddleValue) (z : ThirdValue) : ThirdValue :=
  ThirdValue.piApply a D (fun x y => C x ⟨D x, y⟩) (fun x y => E x ⟨D x, y⟩)
    f x (y.cast (D x)) z

noncomputable def ThirdValue.overLambda (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : a.ShapeEl → MiddleValue → ThirdCode)
    (f : a.ShapeEl → MiddleValue → ThirdValue → ThirdValue) : ThirdValue :=
  ThirdValue.piLambda a D (fun x y => C x ⟨D x, y⟩) (fun x y => E x ⟨D x, y⟩)
    (fun x y => f x ⟨D x, y⟩)

theorem ThirdValue.overApply_congr {a : Arity} {D D' : a.ShapeEl → MiddleCode}
    {f z : ThirdValue} {x : a.ShapeEl} {y : MiddleValue}
    {C C' E E' : a.ShapeEl → MiddleValue → ThirdCode} (hD : D = D')
    (hC : ∀ x (y : MiddleValue), y.code = D x → C x y = C' x y)
    (hE : ∀ x (y : MiddleValue), y.code = D x → E x y = E' x y) :
    ThirdValue.overApply a D C E f x y z = ThirdValue.overApply a D' C' E' f x y z := by
  subst D'
  have hc : (fun x w => C x (MiddleValue.mk (D x) w)) =
      fun x w => C' x (MiddleValue.mk (D x) w) :=
    funext (fun x => funext (fun w => hC x ⟨D x, w⟩ rfl))
  have he : (fun x w => E x (MiddleValue.mk (D x) w)) =
      fun x w => E' x (MiddleValue.mk (D x) w) :=
    funext (fun x => funext (fun w => hE x ⟨D x, w⟩ rfl))
  unfold ThirdValue.overApply
  rw [hc, he]

theorem ThirdValue.overLambda_congr {a : Arity} {D D' : a.ShapeEl → MiddleCode}
    {f f' : a.ShapeEl → MiddleValue → ThirdValue → ThirdValue}
    {C C' E E' : a.ShapeEl → MiddleValue → ThirdCode} (hD : D = D')
    (hC : ∀ x (y : MiddleValue), y.code = D x → C x y = C' x y)
    (hE : ∀ x (y : MiddleValue), y.code = D x → E x y = E' x y)
    (hf : ∀ x (y : MiddleValue), y.code = D x → ∀ (z : ThirdValue), z.code = C x y → f x y z = f' x y z) :
    ThirdValue.overLambda a D C E f = ThirdValue.overLambda a D' C' E' f' := by
  subst D'
  have hc : (fun x w => C x (MiddleValue.mk (D x) w)) =
      fun x w => C' x (MiddleValue.mk (D x) w) :=
    funext (fun x => funext (fun w => hC x ⟨D x, w⟩ rfl))
  have he : (fun x w => E x (MiddleValue.mk (D x) w)) =
      fun x w => E' x (MiddleValue.mk (D x) w) :=
    funext (fun x => funext (fun w => hE x ⟨D x, w⟩ rfl))
  unfold ThirdValue.overLambda
  rw [hc, he]
  apply ThirdValue.piLambda_congr
  intro x y z hz
  exact hf x ⟨D x, y⟩ rfl z (hz.trans (hC x ⟨D x, y⟩ rfl).symm)

theorem thirdApply_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w) :
    thirdApply a D B d c u f g x y z = thirdApply a' D' B' d' c' u f g x y z := by
  subst a'
  apply ThirdValue.overApply_congr
    (C := fun x => d ⟨a, x⟩) (C' := fun x => d' ⟨a, x⟩)
    (E := fun x y => c ⟨a, x⟩ y (u.apply ⟨a, x⟩) (middleApply a D B u f ⟨a, x⟩ y))
    (E' := fun x y => c' ⟨a, x⟩ y (u.apply ⟨a, x⟩) (middleApply a D' B' u f ⟨a, x⟩ y))
    (f := g) (x := x.cast a) (y := y) (z := z)
    (funext (fun x : a.ShapeEl => hD ⟨a, x⟩ rfl))
  · intro x y hy
    exact hd ⟨a, x⟩ rfl y hy
  · intro x y hy
    rw [hc ⟨a, x⟩ rfl y hy, middleApply_congr rfl hD hB]

theorem thirdLambda_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w)
    (hg : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y → g x y z = g' x y z) :
    thirdLambda a D B d c u f g = thirdLambda a' D' B' d' c' u f g' := by
  subst a'
  apply ThirdValue.overLambda_congr
    (C := fun x => d ⟨a, x⟩) (C' := fun x => d' ⟨a, x⟩)
    (E := fun x y => c ⟨a, x⟩ y (u.apply ⟨a, x⟩) (middleApply a D B u f ⟨a, x⟩ y))
    (E' := fun x y => c' ⟨a, x⟩ y (u.apply ⟨a, x⟩) (middleApply a D' B' u f ⟨a, x⟩ y))
    (f := fun x => g ⟨a, x⟩) (f' := fun x => g' ⟨a, x⟩)
    (funext (fun x : a.ShapeEl => hD ⟨a, x⟩ rfl))
  · intro x y hy
    exact hd ⟨a, x⟩ rfl y hy
  · intro x y hy
    rw [hc ⟨a, x⟩ rfl y hy, middleApply_congr rfl hD hB]
  · intro x y hy z hz
    exact hg ⟨a, x⟩ rfl y hy z hz

end Submission.Helpers
