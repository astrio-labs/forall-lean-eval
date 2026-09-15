import Submission.FiberOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A product candidate quantifies over each compatible pair of upper and lower values. -/
noncomputable def fiberCandidatePi (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (d : ShapeValue → FiberValue → Candidate)
    (c : ShapeValue → FiberValue → ShapeValue → FiberValue → Candidate)
    (u : ShapeValue) (f : FiberValue) : Candidate :=
  Candidate.inter (fun x : {x : ShapeValue // x.code = a} =>
    Candidate.inter (fun y : {y : FiberValue // y.code = D x.1} =>
      (d x.1 y.1).arrow
        (c x.1 y.1 (u.apply x.1) (fiberApply a D B u f x.1 y.1))))

theorem fiberCandidatePi_contains (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (d : ShapeValue → FiberValue → Candidate)
    (c : ShapeValue → FiberValue → ShapeValue → FiberValue → Candidate)
    (u : ShapeValue) (f : FiberValue) :
    (fiberCandidatePi a D B d c u f).contains t ↔ SN t ∧
      ∀ x, x.code = a → ∀ y, y.code = D x →
        ((d x y).arrow (c x y (u.apply x) (fiberApply a D B u f x y))).contains t := by
  constructor
  · intro h
    exact ⟨h.1, fun x hx y hy => (h.2 ⟨x, hx⟩).2 ⟨y, hy⟩⟩
  · intro h
    exact ⟨h.1, fun x => ⟨h.1, fun y => h.2 x.1 x.2 y.1 y.2⟩⟩

theorem fiberCandidatePi_apply (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (d : ShapeValue → FiberValue → Candidate)
    (c : ShapeValue → FiberValue → ShapeValue → FiberValue → Candidate)
    (u : ShapeValue) (f : FiberValue) (x : ShapeValue) (y : FiberValue)
    (hx : x.code = a) (hy : y.code = D x)
    (hf : (fiberCandidatePi a D B d c u f).contains t) (ha : (d x y).contains arg) :
    (c x y (u.apply x) (fiberApply a D B u f x y)).contains (.app t arg) :=
  ((hf.2 ⟨x, hx⟩).2 ⟨y, hy⟩).2 arg ha

theorem fiberCandidatePi_lambda (a : Arity) (D : ShapeValue → FiberCode)
    (B : ShapeValue → ShapeValue → FiberCode)
    (d : ShapeValue → FiberValue → Candidate)
    (c : ShapeValue → FiberValue → ShapeValue → FiberValue → Candidate)
    (u : ShapeValue) (f : ShapeValue → FiberValue → FiberValue)
    (hf : ∀ x, x.code = a → ∀ y, y.code = D x → (f x y).code = B x (u.apply x))
    (hC : SN C)
    (hb : ∀ x, x.code = a → ∀ y, y.code = D x →
      ∀ arg, (d x y).contains arg → (c x y (u.apply x) (f x y)).contains (subst 0 arg b)) :
    (fiberCandidatePi a D B d c u (fiberLambda a D B u f)).contains (.lam C b) := by
  have hh (x : ShapeValue) (hx : x.code = a) (y : FiberValue) (hy : y.code = D x) :
      ((d x y).arrow
        (c x y (u.apply x) (fiberApply a D B u (fiberLambda a D B u f) x y))).contains
          (.lam C b) := by
    rw [fiberBeta a D B u f x y hx hy (hf x hx y hy)]
    exact Candidate.lambda _ _ hC (hb x hx y hy)
  rw [fiberCandidatePi_contains]
  refine ⟨?_, hh⟩
  exact (hh ⟨a, a.shapePoint⟩ rfl ⟨D ⟨a, a.shapePoint⟩, (D ⟨a, a.shapePoint⟩).point⟩ rfl).1

theorem fiberCandidatePi_congr (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hd : ∀ x, x.code = a → ∀ y, y.code = D x → d x y = d' x y)
    (hc : ∀ x, x.code = a → ∀ y, y.code = D x → ∀ z w, c x y z w = c' x y z w) :
    fiberCandidatePi a D B d c u f = fiberCandidatePi a' D' B' d' c' u f := by
  subst a'
  apply Candidate.ext
  intro t
  rw [fiberCandidatePi_contains, fiberCandidatePi_contains]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro x hx y hy
    have hy' := hy.trans (hD x hx).symm
    have hh := h.2 x hx y hy'
    rw [hd x hx y hy', hc x hx y hy', fiberApply_congr rfl hD hB] at hh
    exact hh
  · intro h
    refine ⟨h.1, ?_⟩
    intro x hx y hy
    rw [hd x hx y hy, hc x hx y hy, fiberApply_congr rfl hD hB]
    exact h.2 x hx y (hy.trans (hD x hx))

end Submission.Helpers
