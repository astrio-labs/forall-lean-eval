import Submission.ThirdFunctions
import Submission.ThirdProduct

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def ThirdCode.pi (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode) : ThirdCode :=
  ThirdCode.all (.small a) (fun x => ThirdCode.all (D x) (fun y => (C x y).arrow (E x y)))

noncomputable def ThirdCode.piApply (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode)
    (f : (ThirdCode.pi a D C E).El) (x : a.ShapeEl) (y : (D x).El) (z : (C x y).El) :
    (E x y).El :=
  (C x y).arrowApply (E x y)
    (ThirdCode.allApply (D x) _ (ThirdCode.allApply (.small a) _ f x) y) z

noncomputable def ThirdCode.piLambda (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode)
    (f : (x : a.ShapeEl) → (y : (D x).El) → (C x y).El → (E x y).El) :
    (ThirdCode.pi a D C E).El :=
  ThirdCode.allLambda (.small a) _ (fun x => ThirdCode.allLambda (D x) _
    (fun y => (C x y).arrowLambda (E x y) (f x y)))

theorem ThirdCode.piBeta (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode)
    (f : (x : a.ShapeEl) → (y : (D x).El) → (C x y).El → (E x y).El)
    (x : a.ShapeEl) (y : (D x).El) (z : (C x y).El) :
    ThirdCode.piApply a D C E (ThirdCode.piLambda a D C E f) x y z = f x y z := by
  unfold ThirdCode.piApply ThirdCode.piLambda
  rw [ThirdCode.allBeta (.small a)
    (fun x => ThirdCode.all (D x) (fun y => (C x y).arrow (E x y)))
    (fun x => ThirdCode.allLambda (D x) _ (fun y => (C x y).arrowLambda (E x y) (f x y))) x,
    ThirdCode.allBeta, ThirdCode.arrowBeta]

structure ThirdValue where
  code : ThirdCode
  data : code.El

noncomputable def ThirdValue.cast (v : ThirdValue) (A : ThirdCode) : A.El := by
  classical
  exact if h : v.code = A then h ▸ v.data else A.point

@[simp] theorem ThirdValue.cast_mk (A : ThirdCode) (x : A.El) :
    (ThirdValue.mk A x).cast A = x := by simp only [ThirdValue.cast, ↓reduceDIte]

theorem ThirdValue.mk_cast (v : ThirdValue) (h : v.code = A) :
    ThirdValue.mk A (v.cast A) = v := by
  cases v with
  | mk B x => cases h; rw [ThirdValue.cast_mk]

def ThirdValue.unit : ThirdValue := ⟨.small (.small .unit), ()⟩

noncomputable def ThirdValue.force (A : ThirdCode) (v : ThirdValue) : ThirdValue := ⟨A, v.cast A⟩

@[simp] theorem ThirdValue.force_code (A : ThirdCode) (v : ThirdValue) : (v.force A).code = A := rfl

theorem ThirdValue.force_eq (v : ThirdValue) (h : v.code = A) : v.force A = v := v.mk_cast h

noncomputable def ThirdValue.piApply (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode)
    (f : ThirdValue) (x : a.ShapeEl) (y : (D x).El) (z : ThirdValue) : ThirdValue :=
  ⟨E x y, ThirdCode.piApply a D C E (f.cast (.pi a D C E)) x y (z.cast (C x y))⟩

noncomputable def ThirdValue.piLambda (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode)
    (f : (x : a.ShapeEl) → (y : (D x).El) → ThirdValue → ThirdValue) : ThirdValue :=
  ⟨.pi a D C E, ThirdCode.piLambda a D C E (fun x y z => (f x y ⟨C x y, z⟩).cast (E x y))⟩

theorem ThirdValue.piBeta (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode)
    (f : (x : a.ShapeEl) → (y : (D x).El) → ThirdValue → ThirdValue)
    (x : a.ShapeEl) (y : (D x).El) (z : ThirdValue)
    (hz : z.code = C x y) (hf : (f x y z).code = E x y) :
    ThirdValue.piApply a D C E (ThirdValue.piLambda a D C E f) x y z = f x y z := by
  unfold ThirdValue.piApply ThirdValue.piLambda
  rw [ThirdValue.cast_mk, ThirdCode.piBeta, z.mk_cast hz]
  exact (f x y z).mk_cast hf

theorem ThirdValue.piLambda_congr (a : Arity) (D : a.ShapeEl → MiddleCode)
    (C E : (x : a.ShapeEl) → (D x).El → ThirdCode)
    (f g : (x : a.ShapeEl) → (y : (D x).El) → ThirdValue → ThirdValue)
    (h : ∀ x y z, z.code = C x y → f x y z = g x y z) :
    ThirdValue.piLambda a D C E f = ThirdValue.piLambda a D C E g := by
  unfold ThirdValue.piLambda
  congr 2
  funext x y z
  rw [h x y ⟨C x y, z⟩ rfl]

noncomputable def thirdApply (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue)
    (x : ShapeValue) (y : MiddleValue) (z : ThirdValue) : ThirdValue :=
  ThirdValue.piApply a (fun x => D ⟨a, x⟩)
    (fun x y => d ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)
    (fun x y => c ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩ (u.apply ⟨a, x⟩)
      (middleApply a D B u f ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩))
    g (x.cast a) (y.cast (D ⟨a, x.cast a⟩)) z

noncomputable def thirdLambda (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue)
    (g : ShapeValue → MiddleValue → ThirdValue → ThirdValue) : ThirdValue :=
  ThirdValue.piLambda a (fun x => D ⟨a, x⟩)
    (fun x y => d ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)
    (fun x y => c ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩ (u.apply ⟨a, x⟩)
      (middleApply a D B u f ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩))
    (fun x y => g ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)

theorem thirdLambda_code (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue)
    (g : ShapeValue → MiddleValue → ThirdValue → ThirdValue) :
    (thirdLambda a D B d c u f g).code = thirdProduct a D B d c u f := rfl

theorem thirdApply_code (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue)
    (x : ShapeValue) (y : MiddleValue) (z : ThirdValue)
    (hx : x.code = a) (hy : y.code = D x) :
    (thirdApply a D B d c u f g x y z).code = c x y (u.apply x) (middleApply a D B u f x y) := by
  change c ⟨a, x.cast a⟩ ⟨D ⟨a, x.cast a⟩, y.cast (D ⟨a, x.cast a⟩)⟩ _ _ = _
  rw [x.mk_cast hx, y.mk_cast hy]

theorem thirdBeta (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (u : ShapeValue) (f : MiddleValue)
    (g : ShapeValue → MiddleValue → ThirdValue → ThirdValue)
    (x : ShapeValue) (y : MiddleValue) (z : ThirdValue)
    (hx : x.code = a) (hy : y.code = D x) (hz : z.code = d x y)
    (hg : (g x y z).code = c x y (u.apply x) (middleApply a D B u f x y)) :
    thirdApply a D B d c u f (thirdLambda a D B d c u f g) x y z = g x y z := by
  cases x with
  | mk ax vx =>
    cases hx
    cases y with
    | mk ay vy =>
      cases hy
      unfold thirdApply thirdLambda
      rw [ShapeValue.cast_mk ax vx, MiddleValue.cast_mk (D ⟨ax, vx⟩) vy]
      exact (ThirdValue.piBeta ax (fun x => D ⟨ax, x⟩)
          (fun x y => d ⟨ax, x⟩ ⟨D ⟨ax, x⟩, y⟩)
          (fun x y => c ⟨ax, x⟩ ⟨D ⟨ax, x⟩, y⟩ (u.apply ⟨ax, x⟩)
            (middleApply ax D B u f ⟨ax, x⟩ ⟨D ⟨ax, x⟩, y⟩))
          (fun x y => g ⟨ax, x⟩ ⟨D ⟨ax, x⟩, y⟩) vx vy z hz hg)

end Submission.Helpers
