import Submission.ThirdOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A product candidate checks every compatible triple of semantic arguments. -/
noncomputable def thirdCandidatePi (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (p : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (q : ShapeValue → MiddleValue → ThirdValue → ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue) : Candidate :=
  Candidate.inter (fun x : {x : ShapeValue // x.code = a} =>
    Candidate.inter (fun y : {y : MiddleValue // y.code = D x.1} =>
      Candidate.inter (fun z : {z : ThirdValue // z.code = d x.1 y.1} =>
        (p x.1 y.1 z.1).arrow (q x.1 y.1 z.1 (u.apply x.1)
          (middleApply a D B u f x.1 y.1) (thirdApply a D B d c u f g x.1 y.1 z.1)))))

theorem thirdCandidatePi_contains (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (p : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (q : ShapeValue → MiddleValue → ThirdValue → ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue) :
    (thirdCandidatePi a D B d c p q u f g).contains t ↔ SN t ∧
      ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y →
        ((p x y z).arrow (q x y z (u.apply x) (middleApply a D B u f x y)
          (thirdApply a D B d c u f g x y z))).contains t := by
  constructor
  · intro h
    exact ⟨h.1, fun x hx y hy z hz => ((h.2 ⟨x, hx⟩).2 ⟨y, hy⟩).2 ⟨z, hz⟩⟩
  · intro h
    exact ⟨h.1, fun x => ⟨h.1, fun y => ⟨h.1, fun z => h.2 x.1 x.2 y.1 y.2 z.1 z.2⟩⟩⟩

theorem thirdCandidatePi_apply (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (p : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (q : ShapeValue → MiddleValue → ThirdValue → ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue)
    (x : ShapeValue) (y : MiddleValue) (z : ThirdValue)
    (hx : x.code = a) (hy : y.code = D x) (hz : z.code = d x y)
    (hg : (thirdCandidatePi a D B d c p q u f g).contains t) (ha : (p x y z).contains arg) :
    (q x y z (u.apply x) (middleApply a D B u f x y)
      (thirdApply a D B d c u f g x y z)).contains (.app t arg) :=
  (((hg.2 ⟨x, hx⟩).2 ⟨y, hy⟩).2 ⟨z, hz⟩).2 arg ha

theorem thirdCandidatePi_lambda (a : Arity) (D : ShapeValue → MiddleCode)
    (B : ShapeValue → ShapeValue → MiddleCode)
    (d : ShapeValue → MiddleValue → ThirdCode)
    (c : ShapeValue → MiddleValue → ShapeValue → MiddleValue → ThirdCode)
    (p : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (q : ShapeValue → MiddleValue → ThirdValue → ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue)
    (g : ShapeValue → MiddleValue → ThirdValue → ThirdValue)
    (hg : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y →
      (g x y z).code = c x y (u.apply x) (middleApply a D B u f x y))
    (hC : SN C)
    (hb : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y →
      ∀ arg, (p x y z).contains arg →
        (q x y z (u.apply x) (middleApply a D B u f x y) (g x y z)).contains (subst 0 arg b)) :
    (thirdCandidatePi a D B d c p q u f (thirdLambda a D B d c u f g)).contains (.lam C b) := by
  have hh (x : ShapeValue) (hx : x.code = a) (y : MiddleValue) (hy : y.code = D x)
      (z : ThirdValue) (hz : z.code = d x y) :
      ((p x y z).arrow (q x y z (u.apply x) (middleApply a D B u f x y)
        (thirdApply a D B d c u f (thirdLambda a D B d c u f g) x y z))).contains (.lam C b) := by
    rw [thirdBeta a D B d c u f g x y z hx hy hz (hg x hx y hy z hz)]
    exact Candidate.lambda _ _ hC (hb x hx y hy z hz)
  rw [thirdCandidatePi_contains]
  refine ⟨?_, hh⟩
  let x : ShapeValue := ⟨a, a.shapePoint⟩
  let y : MiddleValue := ⟨D x, (D x).point⟩
  let z : ThirdValue := ⟨d x y, (d x y).point⟩
  exact (hh x rfl y rfl z rfl).1

theorem thirdCandidatePi_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w)
    (hp : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y → p x y z = p' x y z)
    (hq : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z, z.code = d x y →
      ∀ v w r, q x y z v w r = q' x y z v w r) :
    thirdCandidatePi a D B d c p q u f g = thirdCandidatePi a' D' B' d' c' p' q' u f g := by
  subst a'
  apply Candidate.ext
  intro t
  rw [thirdCandidatePi_contains, thirdCandidatePi_contains]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro x hx y hy z hz
    have hy' := hy.trans (hD x hx).symm
    have hz' := hz.trans (hd x hx y hy').symm
    have hh := h.2 x hx y hy' z hz'
    rw [hp x hx y hy' z hz', hq x hx y hy' z hz',
      middleApply_congr rfl hD hB, thirdApply_congr rfl hD hB hd hc] at hh
    exact hh
  · intro h
    refine ⟨h.1, ?_⟩
    intro x hx y hy z hz
    rw [hp x hx y hy z hz, hq x hx y hy z hz,
      middleApply_congr rfl hD hB, thirdApply_congr rfl hD hB hd hc]
    exact h.2 x hx y (hy.trans (hD x hx)) z (hz.trans (hd x hx y hy))

end Submission.Helpers
