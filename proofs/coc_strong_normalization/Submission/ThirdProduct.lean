import Submission.MiddleUniverse

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem thirdProduct_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w) :
    thirdProduct a D B d c u f = thirdProduct a' D' B' d' c' u f := by
  subst a'
  unfold thirdProduct
  congr 1
  funext x
  simp only [middleApply_congr rfl hD hB]
  rw [hD ⟨a, x⟩ rfl]
  congr 1
  funext y
  rw [hd ⟨a, x⟩ rfl _ (hD ⟨a, x⟩ rfl).symm,
    hc ⟨a, x⟩ rfl _ (hD ⟨a, x⟩ rfl).symm]

theorem thirdProduct_trivial (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w,
      c x y z w = .small (.small .unit)) :
    thirdProduct a D B d c u f = .small (.small .unit) := by
  apply ThirdCode.all_trivial
  intro x
  apply ThirdCode.all_trivial
  intro y
  rw [hc ⟨a, x⟩ rfl ⟨D ⟨a, x⟩, y⟩ rfl, ThirdCode.arrow_unit]

theorem thirdProduct_isFiber (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue) (k : Arity)
    (hD : D .unit = .small k)
    (hd : ∀ y, (d .unit y).IsFiber)
    (hc : ∀ y z w, (c .unit y z w).IsFiber) :
    (thirdProduct .unit D B d c u f).IsFiber := by
  unfold thirdProduct
  rw [ThirdCode.all_unit]
  change (ThirdCode.all (D .unit) _).IsFiber
  have hall (E : MiddleCode) (he : E = .small k) (g : E.El → ThirdCode)
      (hg : ∀ y, (g y).IsFiber) : (ThirdCode.all E g).IsFiber := by
    subst E
    exact ThirdCode.all_isFiber k g hg
  apply hall _ hD
  intro y
  exact ThirdCode.arrow_isFiber (hd _) (hc _ _ _)

theorem thirdProduct_isArity (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue)
    (hD : D .unit = .small .unit)
    (hd : ∀ y, (d .unit y).IsArity)
    (hc : ∀ y z w, (c .unit y z w).IsArity) :
    (thirdProduct .unit D B d c u f).IsArity := by
  unfold thirdProduct
  rw [ThirdCode.all_unit]
  change (ThirdCode.all (D .unit) _).IsArity
  have hall (E : MiddleCode) (he : E = .small .unit) (g : E.El → ThirdCode)
      (hg : ∀ y, (g y).IsArity) : (ThirdCode.all E g).IsArity := by
    subst E
    rw [ThirdCode.all_unit]
    exact hg ()
  apply hall _ hD
  intro y
  exact ThirdCode.arrow_isArity (hd _) (hc _ _ _)

end Submission.Helpers
