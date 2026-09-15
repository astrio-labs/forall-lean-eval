import ChallengeDeps
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Sqrt

/-!
Quantifier elimination is reduced to finite polynomial sign conditions. A stationary-point
sampling argument realizes these conditions at polynomial roots. Signed root queries are
then eliminated through Cauchy-index reciprocity and even-power pseudo-remainders.

The helper development is kept in this module to avoid repeated compiler startup and
import loading during a fresh build.
-/

namespace Submission.Helpers

open LeanEval.ProgramVerification.RealClosedFieldQE

abbrev Env := Nat → ℝ

/-- A predicate on environments represented by the benchmark's quantifier-free syntax. -/
def QFDefinable (P : Env → Prop) : Prop :=
  ∃ φ : Formula, φ.IsQF ∧ ∀ env, φ.Holds env ↔ P env

namespace QFDefinable

theorem of_formula (φ : Formula) (hφ : φ.IsQF) : QFDefinable φ.Holds :=
  ⟨φ, hφ, fun _ => Iff.rfl⟩

theorem congr {P Q : Env → Prop} (hP : QFDefinable P)
    (h : ∀ env, P env ↔ Q env) : QFDefinable Q := by
  obtain ⟨φ, hφ, hφP⟩ := hP
  exact ⟨φ, hφ, fun env => (hφP env).trans (h env)⟩

theorem fals : QFDefinable (fun _ => False) :=
  ⟨.fals, trivial, fun _ => Iff.rfl⟩

theorem imp {P Q : Env → Prop} (hP : QFDefinable P) (hQ : QFDefinable Q) :
    QFDefinable (fun env => P env → Q env) := by
  obtain ⟨φ, hφ, hφP⟩ := hP
  obtain ⟨ψ, hψ, hψQ⟩ := hQ
  exact ⟨.imp φ ψ, ⟨hφ, hψ⟩, fun env => imp_congr (hφP env) (hψQ env)⟩

theorem not {P : Env → Prop} (hP : QFDefinable P) :
    QFDefinable (fun env => ¬ P env) := hP.imp fals

theorem tru : QFDefinable (fun _ => True) := by
  exact fals.not.congr fun _ => not_false_iff

theorem or {P Q : Env → Prop} (hP : QFDefinable P) (hQ : QFDefinable Q) :
    QFDefinable (fun env => P env ∨ Q env) := by
  classical
  exact (hP.not.imp hQ).congr fun _ => by tauto

theorem and {P Q : Env → Prop} (hP : QFDefinable P) (hQ : QFDefinable Q) :
    QFDefinable (fun env => P env ∧ Q env) := by
  classical
  exact (hP.imp hQ.not).not.congr fun _ => by tauto

theorem exists_finset {ι : Type*} (s : Finset ι) (P : ι → Env → Prop)
    (hP : ∀ i ∈ s, QFDefinable (P i)) :
    QFDefinable (fun env => ∃ i ∈ s, P i env) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fals.congr fun _ => by simp
  | @insert i s hi ih =>
    apply ((hP i (Finset.mem_insert_self _ _)).or
      (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))).congr
    intro env
    simp

theorem forall_finset {ι : Type*} (s : Finset ι) (P : ι → Env → Prop)
    (hP : ∀ i ∈ s, QFDefinable (P i)) :
    QFDefinable (fun env => ∀ i ∈ s, P i env) := by
  classical
  exact (exists_finset s (fun i env => ¬ P i env)
    (fun i hi => (hP i hi).not)).not.congr fun _ => by simp

theorem exists_finite {ι : Type*} [Fintype ι] (P : ι → Env → Prop)
    (hP : ∀ i, QFDefinable (P i)) : QFDefinable (fun env => ∃ i, P i env) := by
  exact (exists_finset Finset.univ P (fun i _ => hP i)).congr fun _ => by simp

theorem forall_finite {ι : Type*} [Fintype ι] (P : ι → Env → Prop)
    (hP : ∀ i, QFDefinable (P i)) : QFDefinable (fun env => ∀ i, P i env) := by
  exact (forall_finset Finset.univ P (fun i _ => hP i)).congr fun _ => by simp

end QFDefinable

/-- The one-variable projection property needed for the general construction. -/
def EliminatesOne : Prop :=
  ∀ φ : Formula, φ.IsQF → QFDefinable (fun env => ∃ x : ℝ, φ.Holds (cons x env))

/-- Eliminating a single existential quantifier suffices, including under nested binders. -/
theorem definable_of_eliminatesOne (h : EliminatesOne) (φ : Formula) :
    QFDefinable φ.Holds := by
  induction φ with
  | lt a b => exact QFDefinable.of_formula (.lt a b) trivial
  | eq a b => exact QFDefinable.of_formula (.eq a b) trivial
  | fals => exact QFDefinable.fals
  | imp φ ψ ihφ ihψ => exact ihφ.imp ihψ
  | all φ ih =>
    classical
    obtain ⟨ψ, hψ, hψφ⟩ := ih
    obtain ⟨χ, hχ, hχψ⟩ := h ψ.not ⟨hψ, trivial⟩
    refine ⟨χ.not, ⟨hχ, trivial⟩, ?_⟩
    intro env
    change (¬ χ.Holds env) ↔ ∀ x : ℝ, φ.Holds (cons x env)
    rw [hχψ]
    simp only [Formula.not, Formula.Holds, not_exists]
    exact forall_congr' fun x => not_not.trans (hψφ (cons x env))

/-- A quantifier eliminator constructed from a proof of one-variable projection. -/
noncomputable def qeFrom (h : EliminatesOne) (φ : Formula) : Formula :=
  Classical.choose (definable_of_eliminatesOne h φ)

theorem isQF_qeFrom (h : EliminatesOne) (φ : Formula) : (qeFrom h φ).IsQF :=
  (Classical.choose_spec (definable_of_eliminatesOne h φ)).1

theorem holds_qeFrom (h : EliminatesOne) (φ : Formula) (env : Env) :
    (qeFrom h φ).Holds env ↔ φ.Holds env :=
  (Classical.choose_spec (definable_of_eliminatesOne h φ)).2 env

end Submission.Helpers

namespace Submission.Helpers

open LeanEval.ProgramVerification.RealClosedFieldQE
open scoped Polynomial

/-- Integer polynomials in the free parameters. -/
abbrev Coeff := MvPolynomial Nat ℤ

/-- Univariate polynomials whose coefficients are integer polynomials in parameters. -/
abbrev ParamPoly := Polynomial Coeff

noncomputable def coeffEval (env : Env) : Coeff →+* ℝ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℝ) env

noncomputable def specialize (env : Env) (p : ParamPoly) : ℝ[X] :=
  p.map (coeffEval env)

/-- Interpret index zero as the univariate indeterminate, and shift the remaining indices. -/
noncomputable def termPoly : Term → ParamPoly
  | .var 0 => Polynomial.X
  | .var (i + 1) => Polynomial.C (MvPolynomial.X i)
  | .const k => Polynomial.C (MvPolynomial.C k)
  | .add a b => termPoly a + termPoly b
  | .mul a b => termPoly a * termPoly b
  | .neg a => -termPoly a

theorem eval_termPoly (t : Term) (env : Env) (x : ℝ) :
    (specialize env (termPoly t)).eval x = t.eval (cons x env) := by
  induction t with
  | var i => cases i <;> simp [termPoly, specialize, coeffEval, Term.eval, cons]
  | const k => simp [termPoly, specialize, coeffEval, Term.eval]
  | add a b ha hb => simpa [termPoly, specialize, Term.eval] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb => simpa [termPoly, specialize, Term.eval] using congrArg₂ (· * ·) ha hb
  | neg a ha => simpa [termPoly, specialize, Term.eval] using congrArg Neg.neg ha

/-- Every coefficient polynomial can be written using the fixed term constructors. -/
theorem exists_coeffTerm (p : Coeff) :
    ∃ t : Term, ∀ env, t.eval env = coeffEval env p := by
  induction p using MvPolynomial.induction_on with
  | C k => exact ⟨.const k, fun env => by simp [Term.eval, coeffEval]⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨.add a b, fun env => by simp [Term.eval, ha, hb]⟩
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := hp
    exact ⟨.mul a (.var i), fun env => by simp [Term.eval, ha, coeffEval]⟩

theorem qf_coeff_lt (p q : Coeff) :
    QFDefinable (fun env => coeffEval env p < coeffEval env q) := by
  obtain ⟨a, ha⟩ := exists_coeffTerm p
  obtain ⟨b, hb⟩ := exists_coeffTerm q
  exact ⟨.lt a b, trivial, fun env => by simp [Formula.Holds, ha, hb]⟩

theorem qf_coeff_eq (p q : Coeff) :
    QFDefinable (fun env => coeffEval env p = coeffEval env q) := by
  obtain ⟨a, ha⟩ := exists_coeffTerm p
  obtain ⟨b, hb⟩ := exists_coeffTerm q
  exact ⟨.eq a b, trivial, fun env => by simp [Formula.Holds, ha, hb]⟩

theorem qf_coeff_sign (p : Coeff) (s : SignType) :
    QFDefinable (fun env => SignType.sign (coeffEval env p) = s) := by
  cases s with
  | zero => exact (qf_coeff_eq p 0).congr fun env => by simp
  | neg => exact (qf_coeff_lt p 0).congr fun env => by simp [sign_eq_neg_one_iff]
  | pos => exact (qf_coeff_lt 0 p).congr fun env => by simp [sign_eq_one_iff]

noncomputable def atomPolys : Formula → Finset ParamPoly
  | .lt a b => {termPoly a - termPoly b}
  | .eq a b => {termPoly a - termPoly b}
  | .fals => ∅
  | .imp φ ψ => atomPolys φ ∪ atomPolys ψ
  | .all φ => atomPolys φ

/-- Evaluate the Boolean part of a quantifier-free formula from polynomial signs. -/
def signTruth (v : ParamPoly → SignType) : Formula → Prop
  | .lt a b => v (termPoly a - termPoly b) = -1
  | .eq a b => v (termPoly a - termPoly b) = 0
  | .fals => False
  | .imp φ ψ => signTruth v φ → signTruth v ψ
  | .all _ => False

theorem signTruth_congr (φ : Formula) (hφ : φ.IsQF) (v w : ParamPoly → SignType)
    (h : ∀ p ∈ atomPolys φ, v p = w p) : signTruth v φ ↔ signTruth w φ := by
  induction φ with
  | lt a b => simp only [signTruth, h (termPoly a - termPoly b) (by simp [atomPolys])]
  | eq a b => simp only [signTruth, h (termPoly a - termPoly b) (by simp [atomPolys])]
  | fals => rfl
  | imp φ ψ ihφ ihψ =>
    exact imp_congr (ihφ hφ.1 (fun p hp => h p (Finset.mem_union_left _ hp)))
      (ihψ hφ.2 (fun p hp => h p (Finset.mem_union_right _ hp)))
  | all φ ih => exact hφ.elim

theorem holds_iff_signTruth (φ : Formula) (hφ : φ.IsQF) (env : Env) (x : ℝ) :
    φ.Holds (cons x env) ↔
      signTruth (fun p => SignType.sign ((specialize env p).eval x)) φ := by
  induction φ with
  | lt a b =>
    simp only [Formula.Holds, signTruth, sign_eq_neg_one_iff]
    simp [specialize, ← eval_termPoly a env x, ← eval_termPoly b env x, sub_neg]
  | eq a b =>
    simp only [Formula.Holds, signTruth, sign_eq_zero_iff]
    simp [specialize, ← eval_termPoly a env x, ← eval_termPoly b env x, sub_eq_zero]
  | fals => rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ hφ.1) (ihψ hφ.2)
  | all φ ih => exact hφ.elim

/-- The algebraic projection statement, separated from the formula syntax. -/
def HasSignProjection : Prop :=
  ∀ (s : Finset ParamPoly) (v : s → SignType),
    QFDefinable (fun env => ∃ x : ℝ,
      ∀ p : s, SignType.sign ((specialize env p).eval x) = v p)

theorem QFDefinable.constant (P : Prop) : QFDefinable (fun _ => P) := by
  classical
  by_cases h : P
  · exact QFDefinable.tru.congr fun _ => iff_of_true trivial h
  · exact QFDefinable.fals.congr fun _ => iff_of_false id h

/-- Finite sign projection supplies the missing one-variable elimination step. -/
theorem eliminatesOne_of_signProjection (h : HasSignProjection) : EliminatesOne := by
  classical
  intro φ hφ
  let s := atomPolys φ
  let extend : (s → SignType) → ParamPoly → SignType :=
    fun v p => if hp : p ∈ s then v ⟨p, hp⟩ else 0
  have hd : QFDefinable (fun env => ∃ v : s → SignType,
      signTruth (extend v) φ ∧
        ∃ x : ℝ, ∀ p : s, SignType.sign ((specialize env p).eval x) = v p) :=
    QFDefinable.exists_finite _ fun v =>
      (QFDefinable.constant (signTruth (extend v) φ)).and (h s v)
  apply hd.congr
  intro env
  constructor
  · rintro ⟨v, hv, x, hx⟩
    refine ⟨x, (holds_iff_signTruth φ hφ env x).mpr ?_⟩
    apply (signTruth_congr φ hφ (extend v)
      (fun p => SignType.sign ((specialize env p).eval x)) ?_).mp hv
    intro p hp
    simpa [extend, show p ∈ s from hp] using (hx ⟨p, hp⟩).symm
  · rintro ⟨x, hx⟩
    let v : s → SignType := fun p => SignType.sign ((specialize env p).eval x)
    refine ⟨v, ?_, x, fun _ => rfl⟩
    apply (signTruth_congr φ hφ
      (fun p => SignType.sign ((specialize env p).eval x)) (extend v) ?_).mp
        ((holds_iff_signTruth φ hφ env x).mp hx)
    intro p hp
    simp [extend, v, show p ∈ s from hp]

end Submission.Helpers

namespace Submission.Helpers

/-- A function with finitely many values, each with a quantifier-free definable fiber. -/
def FiniteQFMap {α : Type*} (f : Env → α) : Prop :=
  ∃ s : Finset α, (∀ env, f env ∈ s) ∧ ∀ a, QFDefinable (fun env => f env = a)

namespace FiniteQFMap

theorem constant {α : Type*} (a : α) : FiniteQFMap (fun _ => a) := by
  classical
  exact ⟨{a}, fun _ => Finset.mem_singleton_self a,
    fun b => QFDefinable.constant (a = b)⟩

theorem pred {α : Type*} {f : Env → α} (hf : FiniteQFMap f) (P : α → Prop) :
    QFDefinable (fun env => P (f env)) := by
  obtain ⟨s, hs, h⟩ := hf
  apply (QFDefinable.exists_finset s (fun a env => f env = a ∧ P a)
    (fun a _ => (h a).and (QFDefinable.constant (P a)))).congr
  intro env
  exact ⟨fun ⟨_, _, he, hp⟩ => he.symm ▸ hp, fun hp => ⟨f env, hs env, rfl, hp⟩⟩

theorem map {α β : Type*} {f : Env → α} (hf : FiniteQFMap f) (g : α → β) :
    FiniteQFMap (fun env => g (f env)) := by
  classical
  have hpred := hf.pred
  obtain ⟨s, hs, _⟩ := hf
  exact ⟨s.image g, fun env => Finset.mem_image_of_mem g (hs env),
    fun b => hpred (fun a => g a = b)⟩

theorem pair {α β : Type*} {f : Env → α} {g : Env → β}
    (hf : FiniteQFMap f) (hg : FiniteQFMap g) :
    FiniteQFMap (fun env => (f env, g env)) := by
  obtain ⟨s, hs, h⟩ := hf
  obtain ⟨t, ht, k⟩ := hg
  refine ⟨s ×ˢ t, fun env => Finset.mem_product.mpr ⟨hs env, ht env⟩, ?_⟩
  rintro ⟨a, b⟩
  exact ((h a).and (k b)).congr fun _ => by simp

theorem map₂ {α β γ : Type*} {f : Env → α} {g : Env → β}
    (hf : FiniteQFMap f) (hg : FiniteQFMap g) (k : α → β → γ) :
    FiniteQFMap (fun env => k (f env) (g env)) :=
  (hf.pair hg).map (fun a => k a.1 a.2)

theorem congr {α : Type*} {f g : Env → α} (hf : FiniteQFMap f)
    (h : ∀ env, f env = g env) : FiniteQFMap g := by
  simpa only [show f = g from funext h] using hf

theorem ite {α : Type*} (P : Env → Prop) [DecidablePred P] (hP : QFDefinable P)
    {f g : Env → α} (hf : FiniteQFMap f) (hg : FiniteQFMap g) :
    FiniteQFMap (fun env => if P env then f env else g env) := by
  classical
  obtain ⟨s, hs, h⟩ := hf
  obtain ⟨t, ht, k⟩ := hg
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro env
    dsimp only
    split_ifs
    · exact Finset.mem_union_left _ (hs env)
    · exact Finset.mem_union_right _ (ht env)
  · intro a
    exact ((hP.and (h a)).or (hP.not.and (k a))).congr
      (fun env => by by_cases he : P env <;> simp [he])

end FiniteQFMap

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial

/-- A signed sum over the distinct real roots of the first polynomial. -/
noncomputable def rootQuery (p q : ParamPoly) (env : Env) : ℚ :=
  ∑ x ∈ (specialize env p).roots.toFinset,
    (SignType.sign ((specialize env q).eval x) : ℚ)

/-- A finite list of sign requirements. -/
abbrev SignConditions := List (ParamPoly × SignType)

def meets (cs : SignConditions) (env : Env) (x : ℝ) : Prop :=
  ∀ c ∈ cs, SignType.sign ((specialize env c.1).eval x) = c.2

/-- A signed sum with additional sign requirements imposed at the roots. -/
noncomputable def constrainedQuery (p : ParamPoly) (cs : SignConditions) (q : ParamPoly)
    (env : Env) : ℚ := by
  classical
  exact ∑ x ∈ (specialize env p).roots.toFinset,
    if meets cs env x then (SignType.sign ((specialize env q).eval x) : ℚ) else 0

def weight₀ (s : SignType) : ℚ := if s = 0 then 1 else 0

def weight₁ (s : SignType) : ℚ := (s : ℚ) / 2

def weight₂ (s : SignType) : ℚ := if s = 0 then -1 else 1 / 2

/-- Interpolation of a sign indicator on the three-point set `{-1, 0, 1}`. -/
theorem sign_indicator (s t : SignType) :
    (if t = s then (1 : ℚ) else 0) =
      weight₀ s + weight₁ s * (t : ℚ) + weight₂ s * (t : ℚ) ^ 2 := by
  cases s <;> cases t <;> norm_num [weight₀, weight₁, weight₂]
  decide

theorem weighted_sign_indicator (s t : SignType) (z : ℚ) :
    (if t = s then z else 0) =
      weight₀ s * z + weight₁ s * (z * (t : ℚ)) + weight₂ s * (z * (t : ℚ) ^ 2) := by
  calc
    _ = (if t = s then (1 : ℚ) else 0) * z := by split_ifs <;> simp
    _ = _ := by rw [sign_indicator]; ring

theorem constrainedQuery_nil (p q : ParamPoly) :
    constrainedQuery p [] q = rootQuery p q := by
  funext env
  simp [constrainedQuery, rootQuery, meets]

/-- A new sign constraint is reduced to three queries with one fewer constraint. -/
theorem constrainedQuery_cons (p a q : ParamPoly) (s : SignType) (cs : SignConditions)
    (env : Env) :
    constrainedQuery p ((a, s) :: cs) q env =
      weight₀ s * constrainedQuery p cs q env +
      weight₁ s * constrainedQuery p cs (q * a) env +
      weight₂ s * constrainedQuery p cs (q * a ^ 2) env := by
  classical
  simp only [constrainedQuery, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hm : meets ((a, s) :: cs) env x ↔
      SignType.sign ((specialize env a).eval x) = s ∧ meets cs env x := by
    simp [meets]
  by_cases hc : meets cs env x
  · simp only [hm, hc, and_true, if_true]
    simp only [specialize, Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval_mul,
      Polynomial.eval_pow, sign_mul, sign_pow, SignType.coe_mul, SignType.coe_pow]
    exact weighted_sign_indicator s _ _
  · simp [hm, hc]

/-- The outstanding algebraic input: each Tarski query has finitely many definable values. -/
def HasRootQueries : Prop :=
  ∀ p q : ParamPoly, FiniteQFMap (rootQuery p q)

theorem finiteQF_constrainedQuery (h : HasRootQueries) (p : ParamPoly)
    (cs : SignConditions) (q : ParamPoly) : FiniteQFMap (constrainedQuery p cs q) := by
  induction cs generalizing q with
  | nil => simpa only [constrainedQuery_nil] using h p q
  | cons c cs ih =>
    obtain ⟨a, s⟩ := c
    have hf := ((ih q).pair ((ih (q * a)).pair (ih (q * a ^ 2)))).map
      (fun v => weight₀ s * v.1 + weight₁ s * v.2.1 + weight₂ s * v.2.2)
    exact hf.congr fun env => (constrainedQuery_cons p a q s cs env).symm

theorem constrainedQuery_one_pos_iff (p : ParamPoly) (cs : SignConditions) (env : Env) :
    0 < constrainedQuery p cs 1 env ↔
      ∃ x ∈ (specialize env p).roots.toFinset, meets cs env x := by
  classical
  simp only [constrainedQuery, specialize, Polynomial.map_one, Polynomial.eval_one,
    sign_one, SignType.coe_one]
  rw [Finset.sum_pos_iff_of_nonneg (fun x _ => by split_ifs <;> norm_num)]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  split_ifs <;> simp_all

/-- All simultaneous sign requirements at real roots follow from signed root queries. -/
theorem qf_exists_root_meets (h : HasRootQueries) (p : ParamPoly) (cs : SignConditions) :
    QFDefinable (fun env =>
      ∃ x ∈ (specialize env p).roots.toFinset, meets cs env x) :=
  ((finiteQF_constrainedQuery h p cs 1).pred (0 < ·)).congr
    (constrainedQuery_one_pos_iff p cs)

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial

/-- An explicit finite range for a query, independent of the parameter values. -/
noncomputable def queryValues (p : ParamPoly) : Finset ℚ :=
  (Finset.Icc (-(p.natDegree : ℤ)) (p.natDegree : ℤ)).image (fun z : ℤ => (z : ℚ))

theorem rootQuery_mem_queryValues (p q : ParamPoly) (env : Env) :
    rootQuery p q env ∈ queryValues p := by
  classical
  let s := (specialize env p).roots.toFinset
  let v : ℝ → ℤ := fun x => (SignType.sign ((specialize env q).eval x) : ℤ)
  have hcard : s.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)
  have hlo : ∀ x, -1 ≤ v x := by
    intro x
    dsimp [v]
    cases SignType.sign ((specialize env q).eval x) <;> norm_num
  have hhi : ∀ x, v x ≤ 1 := by
    intro x
    dsimp [v]
    cases SignType.sign ((specialize env q).eval x) <;> norm_num
  have hsumlo : -(p.natDegree : ℤ) ≤ ∑ x ∈ s, v x := by
    have h₁ := Finset.sum_le_sum (s := s) (fun x _ => hlo x)
    have h₂ : (s.card : ℤ) ≤ p.natDegree := by exact_mod_cast hcard
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one] at h₁
    omega
  have hsumhi : ∑ x ∈ s, v x ≤ (p.natDegree : ℤ) := by
    have h₁ := Finset.sum_le_sum (s := s) (fun x _ => hhi x)
    have h₂ : (s.card : ℤ) ≤ p.natDegree := by exact_mod_cast hcard
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h₁
    omega
  refine Finset.mem_image.mpr ⟨∑ x ∈ s, v x, Finset.mem_Icc.mpr ⟨hsumlo, hsumhi⟩, ?_⟩
  simp [rootQuery, s, v]

/-- Only definability of the individual query fibers remains; boundedness is automatic. -/
theorem hasRootQueries_of_definable_fibers
    (h : ∀ (p q : ParamPoly) (r : ℚ),
      QFDefinable (fun env => rootQuery p q env = r)) : HasRootQueries := by
  intro p q
  exact ⟨queryValues p, rootQuery_mem_queryValues p q, h p q⟩

/-- Specialization to the zero polynomial is a finite conjunction of coefficient tests. -/
theorem qf_specialize_zero (p : ParamPoly) :
    QFDefinable (fun env => specialize env p = 0) := by
  apply (QFDefinable.forall_finset p.support
    (fun i env => coeffEval env (p.coeff i) = 0)
    (fun i _ => (qf_coeff_eq (p.coeff i) 0).congr (fun _ => by simp))).congr
  intro env
  constructor
  · intro h
    ext i
    simp only [specialize, Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hi : i ∈ p.support
    · exact h i hi
    · rw [Polynomial.mem_support_iff, not_not] at hi
      simp [hi]
  · intro hp i _
    have hi := congrArg (fun q : ℝ[X] => q.coeff i) hp
    simpa [specialize] using hi

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial
open Polynomial

/-- The first nonzero Taylor coefficient at a point. It is zero for the zero polynomial. -/
noncomputable def localCoeff (p : ℝ[X]) (a : ℝ) : ℝ :=
  (p.comp (X + C a)).trailingCoeff

theorem localCoeff_eq_coeff (p : ℝ[X]) (a : ℝ) :
    localCoeff p a = (p.comp (X + C a)).coeff (p.rootMultiplicity a) := by
  rw [rootMultiplicity_eq_natTrailingDegree]
  rfl

theorem localCoeff_eq_div (p : ℝ[X]) (a : ℝ) :
    localCoeff p a = (p /ₘ (X - C a) ^ p.rootMultiplicity a).eval a :=
  eval_divByMonic_eq_trailingCoeff_comp.symm

@[simp] theorem localCoeff_zero (a : ℝ) : localCoeff 0 a = 0 := by
  simp [localCoeff]

theorem localCoeff_ne_zero {p : ℝ[X]} (hp : p ≠ 0) (a : ℝ) : localCoeff p a ≠ 0 := by
  rw [localCoeff_eq_div]
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero a hp

theorem localCoeff_mul (p q : ℝ[X]) (a : ℝ) :
    localCoeff (p * q) a = localCoeff p a * localCoeff q a := by
  simp only [localCoeff, mul_comp, trailingCoeff_mul]

@[simp] theorem localCoeff_C (c a : ℝ) : localCoeff (C c) a = c := by
  simp [localCoeff, trailingCoeff]

noncomputable def localCoeffHom (a : ℝ) : ℝ[X] →*₀ ℝ where
  toFun p := localCoeff p a
  map_zero' := localCoeff_zero a
  map_one' := by simp [localCoeff, trailingCoeff]
  map_mul' p q := localCoeff_mul p q a

theorem localCoeff_pow (p : ℝ[X]) (n : ℕ) (a : ℝ) :
    localCoeff (p ^ n) a = localCoeff p a ^ n := (localCoeffHom a).map_pow p n

theorem localCoeff_prod {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) (a : ℝ) :
    localCoeff (∏ i ∈ s, p i) a = ∏ i ∈ s, localCoeff (p i) a :=
  map_prod (localCoeffHom a) p s

theorem localCoeff_of_eval_ne_zero {p : ℝ[X]} {a : ℝ} (ha : p.eval a ≠ 0) :
    localCoeff p a = p.eval a := by
  rw [localCoeff_eq_div, rootMultiplicity_eq_zero ha, pow_zero, divByMonic_one]

theorem localCoeff_derivative {p : ℝ[X]} (hp : p ≠ 0) {a : ℝ} (ha : p.IsRoot a) :
    localCoeff p.derivative a = (p.rootMultiplicity a : ℝ) * localCoeff p a := by
  have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
  have hc : p.derivative.comp (X + C a) = (p.comp (X + C a)).derivative := by
    simp [derivative_comp]
  rw [localCoeff_eq_coeff, derivative_rootMultiplicity_of_root ha, hc, coeff_derivative,
    Nat.sub_add_cancel hm, ← localCoeff_eq_coeff]
  have hcast : ((p.rootMultiplicity a - 1 : ℕ) : ℝ) + 1 = (p.rootMultiplicity a : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hm
  rw [hcast]
  ring

/-- A local Cauchy index. A pole contributes its sign when its order is odd. -/
noncomputable def localIndex (p q : ℝ[X]) (a : ℝ) : ℚ :=
  if q.rootMultiplicity a < p.rootMultiplicity a ∧
      Odd (p.rootMultiplicity a + q.rootMultiplicity a) then
    (SignType.sign (localCoeff p a * localCoeff q a) : ℚ)
  else 0

@[simp] theorem localIndex_zero_left (q : ℝ[X]) (a : ℝ) : localIndex 0 q a = 0 := by
  simp [localIndex]

@[simp] theorem localIndex_zero_right (p : ℝ[X]) (a : ℝ) : localIndex p 0 a = 0 := by
  simp [localIndex]

/-- The logarithmic derivative has one signed contribution at every distinct root. -/
theorem localIndex_derivative_mul {p : ℝ[X]} (hp : p ≠ 0) (q : ℝ[X])
    {a : ℝ} (ha : p.IsRoot a) :
    localIndex p (p.derivative * q) a = (SignType.sign (q.eval a) : ℚ) := by
  have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
  have hlc : localCoeff p a ≠ 0 := localCoeff_ne_zero hp a
  have hd : p.derivative ≠ 0 := by
    intro hz
    have hh := localCoeff_derivative hp ha
    rw [hz, localCoeff_zero] at hh
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') hlc hh.symm
  by_cases hq : q = 0
  · simp [hq]
  have hmprod : (p.derivative * q).rootMultiplicity a =
      p.rootMultiplicity a - 1 + q.rootMultiplicity a := by
    rw [rootMultiplicity_mul (mul_ne_zero hd hq), derivative_rootMultiplicity_of_root ha]
  by_cases hqa : q.eval a = 0
  · have hmq : 0 < q.rootMultiplicity a := (rootMultiplicity_pos hq).mpr hqa
    simp [localIndex, hmprod, show ¬ (p.rootMultiplicity a - 1 + q.rootMultiplicity a <
      p.rootMultiplicity a) by omega, hqa]
  · have hmq : q.rootMultiplicity a = 0 := rootMultiplicity_eq_zero hqa
    have hlt : p.rootMultiplicity a - 1 < p.rootMultiplicity a := by omega
    have hodd : Odd (p.rootMultiplicity a + (p.rootMultiplicity a - 1)) := by
      refine ⟨p.rootMultiplicity a - 1, ?_⟩
      omega
    rw [localIndex, hmprod, hmq, add_zero, if_pos ⟨hlt, hodd⟩,
      localCoeff_mul, localCoeff_derivative hp ha, localCoeff_of_eval_ne_zero hqa]
    have hpos : 0 < (p.rootMultiplicity a : ℝ) * localCoeff p a ^ 2 :=
      mul_pos (Nat.cast_pos.mpr hm) (sq_pos_of_ne_zero hlc)
    rw [show localCoeff p a * ((p.rootMultiplicity a : ℝ) * localCoeff p a * q.eval a) =
        ((p.rootMultiplicity a : ℝ) * localCoeff p a ^ 2) * q.eval a by ring,
      sign_mul, sign_pos hpos, one_mul]

/-- Sum of local pole contributions over the real roots of the denominator. -/
noncomputable def cauchyIndex (p q : ℝ[X]) : ℚ :=
  ∑ a ∈ p.roots.toFinset, localIndex p q a

theorem localData_add_of_order_lt {p q : ℝ[X]} (hp : p ≠ 0) (a : ℝ)
    (h : p.rootMultiplicity a < q.rootMultiplicity a) :
    (p + q).rootMultiplicity a = p.rootMultiplicity a ∧
      localCoeff (p + q) a = localCoeff p a := by
  have hqcoeff : (q.comp (X + C a)).coeff (p.rootMultiplicity a) = 0 := by
    apply coeff_eq_zero_of_lt_natTrailingDegree
    rwa [← rootMultiplicity_eq_natTrailingDegree]
  have hcoeff : ((p + q).comp (X + C a)).coeff (p.rootMultiplicity a) = localCoeff p a := by
    simp only [add_comp, coeff_add, hqcoeff, add_zero, ← localCoeff_eq_coeff]
  have hn : ((p + q).comp (X + C a)).coeff (p.rootMultiplicity a) ≠ 0 := by
    rw [hcoeff]
    exact localCoeff_ne_zero hp a
  have hpq : p + q ≠ 0 := by
    intro hz
    simp [hz] at hn
  have hupper : (p + q).rootMultiplicity a ≤ p.rootMultiplicity a := by
    rw [rootMultiplicity_eq_natTrailingDegree]
    exact natTrailingDegree_le_of_ne_zero hn
  have hlower : p.rootMultiplicity a ≤ (p + q).rootMultiplicity a := by
    simpa only [min_eq_left h.le] using rootMultiplicity_add a hpq
  have hm := le_antisymm hupper hlower
  exact ⟨hm, by rw [localCoeff_eq_coeff, hm, hcoeff]⟩

theorem localIndex_mul_right (p r : ℝ[X]) (a : ℝ) : localIndex p (p * r) a = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hr : r = 0
  · simp [hr]
  have hm := rootMultiplicity_mul (mul_ne_zero hp hr) (x := a)
  simp [localIndex, hm, show ¬ (p.rootMultiplicity a + r.rootMultiplicity a <
    p.rootMultiplicity a) by omega]

/-- Adding a polynomial to a rational function does not change its local pole contribution. -/
theorem localIndex_add_mul (p q r : ℝ[X]) (a : ℝ) :
    localIndex p (q + p * r) a = localIndex p q a := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hq : q = 0
  · simp [hq, localIndex_mul_right]
  have hm := rootMultiplicity_mul (mul_ne_zero hp hr) (x := a)
  by_cases hlt : q.rootMultiplicity a < p.rootMultiplicity a
  · have hlt' : q.rootMultiplicity a < (p * r).rootMultiplicity a := by
      rw [hm]
      omega
    obtain ⟨ho, hc⟩ := localData_add_of_order_lt hq a hlt'
    simp only [localIndex, ho, hc]
  · have hge : p.rootMultiplicity a ≤ q.rootMultiplicity a := Nat.le_of_not_gt hlt
    by_cases hsum : q + p * r = 0
    · simp [hsum, localIndex, show ¬ (q.rootMultiplicity a < p.rootMultiplicity a) from hlt]
    · have hnew : p.rootMultiplicity a ≤ (q + p * r).rootMultiplicity a := by
        apply le_trans (le_min hge ?_) (rootMultiplicity_add a hsum)
        rw [hm]
        omega
      simp [localIndex, hlt, not_lt.mpr hnew]

/-- Euclidean remainders preserve the Cauchy index with a fixed denominator. -/
theorem cauchyIndex_mod (p q : ℝ[X]) : cauchyIndex p (q % p) = cauchyIndex p q := by
  classical
  apply Finset.sum_congr rfl
  intro a _
  have h := localIndex_add_mul p (q % p) (q / p) a
  simpa only [EuclideanDomain.mod_add_div] using h.symm

theorem localIndex_C_mul_pos (p q : ℝ[X]) {c : ℝ} (hc : 0 < c) (a : ℝ) :
    localIndex p (C c * q) a = localIndex p q a := by
  by_cases hq : q = 0
  · simp [hq]
  have hm : (C c * q).rootMultiplicity a = q.rootMultiplicity a := by
    rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc.ne') hq), rootMultiplicity_C,
      zero_add]
  simp only [localIndex, hm]
  split_ifs
  · rw [localCoeff_mul, localCoeff_C,
      mul_left_comm (localCoeff p a) c (localCoeff q a), sign_mul, sign_pos hc, one_mul]
  · rfl

theorem cauchyIndex_C_mul_pos (p q : ℝ[X]) {c : ℝ} (hc : 0 < c) :
    cauchyIndex p (C c * q) = cauchyIndex p q :=
  Finset.sum_congr rfl (fun a _ => localIndex_C_mul_pos p q hc a)

theorem cauchyIndex_add_mul (p q r : ℝ[X]) :
    cauchyIndex p (q + p * r) = cauchyIndex p q :=
  Finset.sum_congr rfl (fun a _ => localIndex_add_mul p q r a)

theorem cauchyIndex_of_natDegree_zero {p : ℝ[X]} (hp : p.natDegree = 0) (q : ℝ[X]) :
    cauchyIndex p q = 0 := by
  rw [eq_C_of_natDegree_eq_zero hp]
  simp [cauchyIndex]

/-- Half the change of sign of a polynomial across a real root. -/
noncomputable def polyJump (p : ℝ[X]) (a : ℝ) : ℚ :=
  if Odd (p.rootMultiplicity a) then (SignType.sign (localCoeff p a) : ℚ) else 0

theorem localIndex_reciprocal (p q : ℝ[X]) (a : ℝ) :
    localIndex p q a + localIndex q p a = polyJump (p * q) a := by
  by_cases hp : p = 0
  · simp [hp, polyJump]
  by_cases hq : q = 0
  · simp [hq, polyJump]
  rw [polyJump, rootMultiplicity_mul (mul_ne_zero hp hq), localCoeff_mul]
  rcases lt_trichotomy (p.rootMultiplicity a) (q.rootMultiplicity a) with hlt | heq | hgt
  · simp [localIndex, hlt, hlt.not_gt, Nat.add_comm, mul_comm]
  · have he : ¬ Odd (q.rootMultiplicity a + q.rootMultiplicity a) :=
      Nat.not_odd_iff_even.mpr ⟨_, rfl⟩
    simp [localIndex, heq, he]
  · simp [localIndex, hgt, hgt.not_gt]

noncomputable def polyJumpSum (p : ℝ[X]) : ℚ := ∑ a ∈ p.roots.toFinset, polyJump p a

/-- Reciprocity reduces the two Cauchy indices to the total sign change of a polynomial. -/
theorem cauchyIndex_reciprocal (p q : ℝ[X]) :
    cauchyIndex p q + cauchyIndex q p = polyJumpSum (p * q) := by
  classical
  by_cases hp : p = 0
  · simp [hp, cauchyIndex, polyJumpSum]
  by_cases hq : q = 0
  · simp [hq, cauchyIndex, polyJumpSum]
  have hpq := mul_ne_zero hp hq
  have hs₁ : p.roots.toFinset ⊆ (p * q).roots.toFinset := by
    rw [roots_mul hpq, Multiset.toFinset_add]
    exact Finset.subset_union_left
  have hs₂ : q.roots.toFinset ⊆ (p * q).roots.toFinset := by
    rw [roots_mul hpq, Multiset.toFinset_add]
    exact Finset.subset_union_right
  have hsum₁ : cauchyIndex p q = ∑ a ∈ (p * q).roots.toFinset, localIndex p q a := by
    apply Finset.sum_subset hs₁
    intro a _ ha
    have hn : ¬ p.IsRoot a := fun h => ha (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr h))
    simp [localIndex, rootMultiplicity_eq_zero hn]
  have hsum₂ : cauchyIndex q p = ∑ a ∈ (p * q).roots.toFinset, localIndex q p a := by
    apply Finset.sum_subset hs₂
    intro a _ ha
    have hn : ¬ q.IsRoot a := fun h => ha (Multiset.mem_toFinset.mpr ((mem_roots hq).mpr h))
    simp [localIndex, rootMultiplicity_eq_zero hn]
  rw [hsum₁, hsum₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => localIndex_reciprocal p q a)

/-- The Tarski query is the Cauchy index of `p' * q / p`. -/
theorem rootQuery_eq_cauchyIndex (p q : ParamPoly) (env : Env) :
    rootQuery p q env = cauchyIndex (specialize env p)
      ((specialize env p).derivative * specialize env q) := by
  classical
  by_cases hp : specialize env p = 0
  · simp [rootQuery, cauchyIndex, hp]
  apply Finset.sum_congr rfl
  intro a ha
  exact (localIndex_derivative_mul hp (specialize env q)
    ((mem_roots hp).mp (Multiset.mem_toFinset.mp ha))).symm

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial
open Polynomial

noncomputable def orderSign (a b : ℝ) : ℚ := if a < b then -1 else 1

noncomputable def orderSignSum (s : Finset ℝ) : ℚ :=
  ∑ a ∈ s, ∏ b ∈ s, orderSign a b

/-- Alternating signs of a finite ordered set telescope to its parity. -/
theorem orderSignSum_eq (s : Finset ℝ) :
    orderSignSum s = if Odd s.card then 1 else 0 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp [orderSignSum]
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => (hlt a h).false
    have htop : (∏ b ∈ s, orderSign a b) = 1 := by
      apply Finset.prod_eq_one
      intro b hb
      exact if_neg (hlt b hb).not_gt
    have hrest : (∑ b ∈ s, orderSign b a * ∏ c ∈ s, orderSign b c) =
        -orderSignSum s := by
      rw [orderSignSum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [orderSign, if_pos (hlt b hb), neg_one_mul]
    have hrec : orderSignSum (insert a s) = 1 - orderSignSum s := by
      simp only [orderSignSum, Finset.sum_insert ha, Finset.prod_insert ha]
      rw [show orderSign a a = 1 by simp [orderSign], one_mul, htop, hrest]
      simp only [sub_eq_add_neg, orderSignSum]
    rw [hrec, ih, Finset.card_insert_of_notMem ha]
    have hpar : Odd (s.card + 1) ↔ ¬ Odd s.card := by
      simp only [Nat.odd_iff]
      omega
    simp only [hpar]
    by_cases h : Odd s.card <;> simp [h]

theorem sign_eval_of_roots_empty {p : ℝ[X]} (hp : p ≠ 0) (hr : p.roots = 0) (x : ℝ) :
    SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  have hn : ∀ y, ¬ p.IsRoot y := by
    intro y hy
    have hm := (mem_roots hp).mpr hy
    simp only [hr, Multiset.notMem_zero] at hm
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hneg | hpos
  · have he : p.eval x < 0 := eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos
      (fun y hy => (hn y hy).elim) hneg.le
    rw [sign_neg he, sign_neg hneg]
  · have he : 0 < p.eval x := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
      (fun y hy => (hn y hy).elim) hpos.le
    rw [sign_pos he, sign_pos hpos]

theorem even_natDegree_of_roots_empty {p : ℝ[X]} (hp : p ≠ 0) (hr : p.roots = 0) :
    Even p.natDegree := by
  have hn : ∀ y, ¬ p.IsRoot y := by
    intro y hy
    have hm := (mem_roots hp).mpr hy
    simp only [hr, Multiset.notMem_zero] at hm
  by_contra he
  have ho : Odd p.natDegree := Nat.not_even_iff_odd.mp he
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hneg | hpos
  · have h₁ : p.eval 0 < 0 := eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos
      (fun y hy => (hn y hy).elim) hneg.le
    have h₂ : Int.negOnePow p.natDegree * p.eval 0 < 0 :=
      negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos
        (fun y hy => (hn y hy).elim) hneg.le
    rw [Int.negOnePow_odd _ (by exact_mod_cast ho)] at h₂
    norm_num at h₂
    linarith
  · have h₁ : 0 < p.eval 0 := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
      (fun y hy => (hn y hy).elim) hpos.le
    have h₂ : 0 < Int.negOnePow p.natDegree * p.eval 0 :=
      zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
        (fun y hy => (hn y hy).elim) hpos.le
    rw [Int.negOnePow_odd _ (by exact_mod_cast ho)] at h₂
    norm_num at h₂
    linarith

noncomputable def activeRoots (p : ℝ[X]) : Finset ℝ :=
  p.roots.toFinset.filter (fun a => Odd (p.rootMultiplicity a))

theorem sign_localCoeff_linear (a b : ℝ) :
    SignType.sign (localCoeff (X - C b) a) = if a < b then -1 else 1 := by
  by_cases he : a = b
  · subst b
    simp [localCoeff, sub_comp, trailingCoeff, natTrailingDegree_X]
  have hn : (X - C b : ℝ[X]).eval a ≠ 0 := by simpa using sub_ne_zero.mpr he
  rw [localCoeff_of_eval_ne_zero hn]
  simp only [eval_sub, eval_X, eval_C]
  rcases lt_or_gt_of_ne he with hlt | hgt
  · rw [if_pos hlt, sign_neg (sub_neg.mpr hlt)]
  · rw [if_neg hgt.not_gt, sign_pos (sub_pos.mpr hgt)]

theorem sign_localCoeff_roots {p : ℝ[X]} (hp : p ≠ 0) (a : ℝ) :
    SignType.sign (localCoeff p a) = SignType.sign p.leadingCoeff *
      ∏ b ∈ activeRoots p, (if a < b then (-1 : SignType) else 1) := by
  classical
  obtain ⟨r, hfac, _, hr⟩ := exists_prod_multiset_X_sub_C_mul p
  have hrne : r ≠ 0 := by
    intro hz
    exact hp (by simpa [hz] using hfac.symm)
  have hrlead : r.leadingCoeff = p.leadingCoeff := by
    have hh := congrArg leadingCoeff hfac
    simpa only [leadingCoeff_mul, (monic_multisetProd_X_sub_C p.roots).leadingCoeff, one_mul]
      using hh
  have hran : r.eval a ≠ 0 := by
    intro hz
    have hm := (mem_roots hrne).mpr hz
    simp only [hr, Multiset.notMem_zero] at hm
  have hrlocal : SignType.sign (localCoeff r a) = SignType.sign p.leadingCoeff := by
    rw [localCoeff_of_eval_ne_zero hran, sign_eval_of_roots_empty hrne hr, hrlead]
  rw [prod_multiset_root_eq_finset_root] at hfac
  conv_lhs => rw [← hfac, localCoeff_mul, sign_mul, hrlocal]
  rw [mul_comm]
  congr 1
  rw [localCoeff_prod]
  change signHom (∏ b ∈ p.roots.toFinset, localCoeff ((X - C b) ^ p.rootMultiplicity b) a) = _
  rw [map_prod]
  simp only [signHom_apply, localCoeff_pow, sign_pow]
  rw [activeRoots, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro b _
  by_cases ho : Odd (p.rootMultiplicity b)
  · rw [if_pos ho, SignType.pow_odd _ ho, sign_localCoeff_linear]
  · rw [if_neg ho, SignType.pow_even _ (Nat.not_odd_iff_even.mp ho)
      (sign_ne_zero.mpr (localCoeff_ne_zero (X_sub_C_ne_zero b) a))]

theorem odd_activeRoots_iff {p : ℝ[X]} (hp : p ≠ 0) :
    Odd (activeRoots p).card ↔ Odd p.natDegree := by
  classical
  obtain ⟨r, hfac, hdeg, hr⟩ := exists_prod_multiset_X_sub_C_mul p
  have hrne : r ≠ 0 := by
    intro hz
    exact hp (by simpa [hz] using hfac.symm)
  have hre := even_natDegree_of_roots_empty hrne hr
  have hc : (∑ a ∈ p.roots.toFinset, p.rootMultiplicity a) = p.roots.card := by
    simpa only [← count_roots] using Multiset.toFinset_sum_count_eq p.roots
  have hs : Odd p.roots.card ↔ Odd (activeRoots p).card := by
    rw [← hc]
    exact Finset.odd_sum_iff_odd_card_odd _
  apply hs.symm.trans
  rw [← hdeg, Nat.odd_add]
  simp [hre]

/-- Total sign change of a polynomial, expressed only using its degree and leading coefficient. -/
theorem polyJumpSum_eq (p : ℝ[X]) :
    polyJumpSum p = if Odd p.natDegree then (SignType.sign p.leadingCoeff : ℚ) else 0 := by
  classical
  by_cases hp : p = 0
  · simp [hp, polyJumpSum]
  have hlocal (a : ℝ) : (SignType.sign (localCoeff p a) : ℚ) =
      (SignType.sign p.leadingCoeff : ℚ) * ∏ b ∈ activeRoots p, orderSign a b := by
    rw [sign_localCoeff_roots hp a, SignType.coe_mul]
    congr 1
    change SignType.castHom (∏ b ∈ activeRoots p, if a < b then (-1 : SignType) else 1) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro b _
    by_cases hab : a < b <;> simp [orderSign, hab]
  simp only [polyJumpSum, polyJump, hlocal]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  change (SignType.sign p.leadingCoeff : ℚ) * orderSignSum (activeRoots p) = _
  rw [orderSignSum_eq]
  simp only [odd_activeRoots_iff hp]
  split_ifs <;> simp

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial
open Polynomial

theorem qf_specialize_natDegree_le (p : ParamPoly) (n : ℕ) :
    QFDefinable (fun env => (specialize env p).natDegree ≤ n) := by
  apply (QFDefinable.forall_finset (p.support.filter (n < ·))
    (fun i env => coeffEval env (p.coeff i) = 0)
    (fun i _ => (qf_coeff_eq (p.coeff i) 0).congr (fun _ => by simp))).congr
  intro env
  rw [natDegree_le_iff_coeff_eq_zero]
  constructor
  · intro h i hi
    simp only [specialize, coeff_map]
    by_cases his : i ∈ p.support
    · exact h i (Finset.mem_filter.mpr ⟨his, hi⟩)
    · rw [mem_support_iff, not_not] at his
      simp [his]
  · intro h i hi
    simpa [specialize] using h i (Finset.mem_filter.mp hi).2

theorem qf_specialize_natDegree_eq (p : ParamPoly) (n : ℕ) :
    QFDefinable (fun env => (specialize env p).natDegree = n) := by
  cases n with
  | zero => exact (qf_specialize_natDegree_le p 0).congr (fun _ => by omega)
  | succ n =>
    exact ((qf_specialize_natDegree_le p (n + 1)).and
      (qf_specialize_natDegree_le p n).not).congr (fun _ => by omega)

theorem finiteQF_coeffSign (p : Coeff) :
    FiniteQFMap (fun env => SignType.sign (coeffEval env p)) := by
  exact ⟨Finset.univ, fun _ => Finset.mem_univ _, qf_coeff_sign p⟩

noncomputable def jumpValue (p : ParamPoly) (env : Env) : ℚ :=
  if Odd (specialize env p).natDegree then (SignType.sign (specialize env p).leadingCoeff : ℚ)
  else 0

theorem qf_jumpValue (p : ParamPoly) (r : ℚ) :
    QFDefinable (fun env => jumpValue p env = r) := by
  have hval (n : ℕ) : QFDefinable (fun env =>
      (if Odd n then (SignType.sign (coeffEval env (p.coeff n)) : ℚ) else 0) = r) := by
    by_cases hn : Odd n
    · exact ((finiteQF_coeffSign (p.coeff n)).pred (fun s => (s : ℚ) = r)).congr
        (fun _ => by simp [hn])
    · exact (QFDefinable.constant ((0 : ℚ) = r)).congr (fun _ => by simp [hn])
  apply (QFDefinable.exists_finset (Finset.range (p.natDegree + 1))
    (fun n env => (specialize env p).natDegree = n ∧
      (if Odd n then (SignType.sign (coeffEval env (p.coeff n)) : ℚ) else 0) = r)
    (fun n _ => (qf_specialize_natDegree_eq p n).and (hval n))).congr
  intro env
  have hlc : (specialize env p).leadingCoeff =
      coeffEval env (p.coeff (specialize env p).natDegree) := by
    simp only [leadingCoeff, specialize, coeff_map]
  constructor
  · rintro ⟨n, _, hn, hv⟩
    subst n
    simpa only [jumpValue, hlc] using hv
  · intro hv
    refine ⟨(specialize env p).natDegree,
      Finset.mem_range.mpr (Nat.lt_succ_of_le natDegree_map_le), rfl, ?_⟩
    simpa only [jumpValue, hlc] using hv

theorem finiteQF_jumpValue (p : ParamPoly) : FiniteQFMap (jumpValue p) := by
  classical
  refine ⟨Finset.univ.image (fun s : SignType => (s : ℚ)), ?_, qf_jumpValue p⟩
  intro env
  unfold jumpValue
  split_ifs
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem finiteQF_polyJumpSum (p : ParamPoly) :
    FiniteQFMap (fun env => polyJumpSum (specialize env p)) :=
  (finiteQF_jumpValue p).congr (fun env => (polyJumpSum_eq (specialize env p)).symm)

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial
open Polynomial

/-- Pseudo-division with an even power of the leading coefficient. After specialization
at a nonzero leading coefficient, the multiplier is strictly positive. -/
theorem exists_even_pseudo_remainder (p q : ParamPoly) (hpd : 0 < p.natDegree) :
    ∃ (k : ℕ) (s r : ParamPoly),
      C (p.leadingCoeff ^ (2 * k)) * q = p * s + r ∧ r.natDegree < p.natDegree := by
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hpd
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  induction q using Polynomial.degree_lt_wf.induction with
  | h q ih =>
    by_cases hq : q = 0
    · exact ⟨0, 0, 0, by simp [hq], by simpa using hpd⟩
    by_cases hlow : q.natDegree < p.natDegree
    · exact ⟨0, 0, q, by simp, hlow⟩
    have hqc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
    let a : ParamPoly := C q.leadingCoeff * X ^ (q.natDegree - p.natDegree)
    let u : ParamPoly := C p.leadingCoeff * q
    let v : ParamPoly := a * p
    let t : ParamPoly := u - v
    have ha : a ≠ 0 := mul_ne_zero (C_ne_zero.mpr hqc) (pow_ne_zero _ X_ne_zero)
    have hu : u ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hq
    have hv : v ≠ 0 := mul_ne_zero ha hp
    have hnu : u.natDegree = q.natDegree := by
      dsimp [u]
      rw [natDegree_mul (C_ne_zero.mpr hc) hq, natDegree_C, zero_add]
    have hnv : v.natDegree = q.natDegree := by
      dsimp [v]
      rw [natDegree_mul ha hp]
      dsimp [a]
      rw [natDegree_C_mul_X_pow _ _ hqc]
      omega
    have hdu : u.degree = q.degree := by
      rw [degree_eq_natDegree hu, degree_eq_natDegree hq, hnu]
    have hdv : v.degree = q.degree := by
      rw [degree_eq_natDegree hv, degree_eq_natDegree hq, hnv]
    have hlc : u.leadingCoeff = v.leadingCoeff := by
      change (C p.leadingCoeff * q).leadingCoeff =
        ((C q.leadingCoeff * X ^ (q.natDegree - p.natDegree)) * p).leadingCoeff
      rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_C_mul_X_pow]
      exact mul_comm _ _
    have ht : t.degree < q.degree :=
      (degree_sub_lt_left (hdu.trans hdv.symm) hu hlc).trans_eq hdu
    obtain ⟨k, s, r, hid, hr⟩ := ih t ht
    refine ⟨k + 1, C (p.leadingCoeff ^ (2 * k + 1)) * a + C p.leadingCoeff * s,
      C p.leadingCoeff * r, ?_, ?_⟩
    · dsimp [t, u, v] at hid
      simp only [Nat.mul_add, Nat.mul_one, map_pow, map_mul, pow_add, pow_one, pow_two] at hid ⊢
      linear_combination C p.leadingCoeff * hid
    · have hle : (C p.leadingCoeff * r).natDegree ≤ (C p.leadingCoeff).natDegree + r.natDegree :=
        natDegree_mul_le
      simp only [natDegree_C, zero_add] at hle
      exact hle.trans_lt hr

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial
open Polynomial

/-- A symbolic signed-remainder argument: every Cauchy index has definable fibers. -/
theorem finiteQF_cauchyIndex (p q : ParamPoly) :
    FiniteQFMap (fun env => cauchyIndex (specialize env p) (specialize env q)) := by
  classical
  by_cases hd : p.natDegree = 0
  · apply (FiniteQFMap.constant (0 : ℚ)).congr
    intro env
    have hreal : (specialize env p).natDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact natDegree_map_le.trans hd.le
    exact (cauchyIndex_of_natDegree_zero hreal (specialize env q)).symm
  have hpd : 0 < p.natDegree := Nat.pos_of_ne_zero hd
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hpd
  have hedeg : p.eraseLead.natDegree < p.natDegree := by
    by_cases he : p.eraseLead = 0
    · simpa [he] using hpd
    · exact (natDegree_lt_natDegree_iff he).mpr (p.degree_eraseLead_lt hp)
  obtain ⟨k, s, r, hdiv, hrdeg⟩ := exists_even_pseudo_remainder p q hpd
  have hz := finiteQF_cauchyIndex p.eraseLead q
  have hn := (finiteQF_polyJumpSum (p * r)).map₂ (finiteQF_cauchyIndex r p) (· - ·)
  have htest : QFDefinable (fun env => coeffEval env p.leadingCoeff = 0) :=
    (qf_coeff_eq p.leadingCoeff 0).congr (fun _ => by simp)
  apply (FiniteQFMap.ite (fun env => coeffEval env p.leadingCoeff = 0) htest hz hn).congr
  intro env
  split_ifs with hc
  · have he : specialize env p.eraseLead = specialize env p := by
      have hh := congrArg (specialize env) p.eraseLead_add_C_mul_X_pow
      simpa only [specialize, Polynomial.map_add, Polynomial.map_mul, map_C, hc,
        C_0, zero_mul, add_zero] using hh
    rw [he]
  · have hpos : 0 < coeffEval env p.leadingCoeff ^ (2 * k) := by
      rw [pow_mul]
      exact pow_pos (sq_pos_of_ne_zero hc) k
    have hdiv' : C (coeffEval env p.leadingCoeff ^ (2 * k)) * specialize env q =
        specialize env p * specialize env s + specialize env r := by
      have hh := congrArg (specialize env) hdiv
      simpa [specialize] using hh
    have hrem : cauchyIndex (specialize env p) (specialize env q) =
        cauchyIndex (specialize env p) (specialize env r) := by
      calc
        _ = cauchyIndex (specialize env p)
            (C (coeffEval env p.leadingCoeff ^ (2 * k)) * specialize env q) :=
          (cauchyIndex_C_mul_pos _ _ hpos).symm
        _ = cauchyIndex (specialize env p)
            (specialize env p * specialize env s + specialize env r) := by rw [hdiv']
        _ = cauchyIndex (specialize env p) (specialize env r) := by
          rw [add_comm, cauchyIndex_add_mul]
    have hrec := cauchyIndex_reciprocal (specialize env p) (specialize env r)
    have hmul : specialize env (p * r) = specialize env p * specialize env r := by
      simp [specialize]
    rw [hmul]
    linarith
termination_by p.natDegree
decreasing_by all_goals assumption

/-- Signed root queries are finite functions whose fibers have quantifier-free formulas. -/
theorem hasRootQueries : HasRootQueries := by
  intro p q
  apply (finiteQF_cauchyIndex p (p.derivative * q)).congr
  intro env
  rw [rootQuery_eq_cauchyIndex]
  congr 1
  simp [specialize, derivative_map]

end Submission.Helpers

namespace Submission.Helpers

open Filter Set
open scoped Topology Polynomial

/-- A positive objective vanishing on the walls of a sign region has a stationary sample
inside that region, provided the objective tends to zero at infinity. -/
theorem exists_same_sign_isLocalMax {ι : Type*} [Fintype ι]
    (g : ι → ℝ → ℝ) (hg : ∀ i, Continuous (g i))
    (f : ℝ → ℝ) (hf : Continuous f) (hlim : Tendsto f (cocompact ℝ) (𝓝 0))
    (hzero : ∀ y, (∃ i, g i y = 0) → f y = 0)
    (x : ℝ) (hx : ∀ i, g i x ≠ 0) (hfx : 0 < f x) :
    ∃ y, (∀ i, SignType.sign (g i y) = SignType.sign (g i x)) ∧ IsLocalMax f y := by
  let S : Set ℝ := {y | ∀ i, 0 < g i x * g i y}
  let T : Set ℝ := {y | ∀ i, 0 ≤ g i x * g i y}
  have hopen : IsOpen S := by
    simp only [S, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ((hg i).const_mul _)
  have hclosed : IsClosed T := by
    simp only [T, ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const ((hg i).const_mul _)
  have hxT : x ∈ T := fun i => mul_self_nonneg _
  have hevent : ∀ᶠ y in cocompact ℝ ⊓ 𝓟 T, f y ≤ f x :=
    ((hlim.eventually (gt_mem_nhds hfx)).mono (fun _ hy => hy.le)).filter_mono inf_le_left
  obtain ⟨y, hyT, hmax⟩ := hf.continuousOn.exists_isMaxOn' hclosed hxT hevent
  have hfy : 0 < f y := hfx.trans_le (hmax hxT)
  have hyS : y ∈ S := by
    intro i
    apply lt_of_le_of_ne (hyT i)
    intro heq
    have hiy : g i y = 0 := (mul_eq_zero.mp heq.symm).resolve_left (hx i)
    exact hfy.ne' (hzero y ⟨i, hiy⟩)
  refine ⟨y, ?_, hmax.isLocalMax ?_⟩
  · intro i
    rcases mul_pos_iff.mp (hyS i) with hpos | hneg
    · rw [sign_pos hpos.1, sign_pos hpos.2]
    · rw [sign_neg hneg.1, sign_neg hneg.2]
  · exact mem_of_superset (hopen.mem_nhds hyS) (fun z hz i => (hz i).le)

open Polynomial

/-- A decaying, nonnegative objective with precisely the same zeros as `p`. -/
noncomputable def normalizedSquare (p : ℝ[X]) (N : ℕ) : ℝ → ℝ :=
  fun x => p.eval x ^ 2 / (x ^ 2 + 1) ^ N

theorem continuous_normalizedSquare (p : ℝ[X]) (N : ℕ) :
    Continuous (normalizedSquare p N) := by
  exact (p.differentiable.continuous.pow 2).div
    (((continuous_id.pow 2).add continuous_const).pow N)
    (fun x => pow_ne_zero N (by positivity))

theorem normalizedSquare_pos {p : ℝ[X]} {N : ℕ} {x : ℝ} (hx : p.eval x ≠ 0) :
    0 < normalizedSquare p N x := by
  exact div_pos (sq_pos_of_ne_zero hx) (pow_pos (by positivity) _)

theorem tendsto_normalizedSquare {p : ℝ[X]} (hp : p ≠ 0) {N : ℕ}
    (hN : p.natDegree < N) : Tendsto (normalizedSquare p N) (cocompact ℝ) (𝓝 0) := by
  have hdeg : (p ^ 2).degree < ((X ^ 2 + C 1 : ℝ[X]) ^ N).degree := by
    rw [← natDegree_lt_natDegree_iff (pow_ne_zero 2 hp), natDegree_pow,
      natDegree_pow, natDegree_X_pow_add_C]
    omega
  have he : (fun x : ℝ => (p ^ 2).eval x / (((X ^ 2 + C 1 : ℝ[X]) ^ N).eval x)) =
      normalizedSquare p N := by
    funext x
    simp [normalizedSquare]
  rw [← he, cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · exact (p ^ 2).div_tendsto_atBot_zero_of_degree_lt ((X ^ 2 + C 1) ^ N) hdeg
  · exact (p ^ 2).div_tendsto_atTop_zero_of_degree_lt ((X ^ 2 + C 1) ^ N) hdeg

/-- The numerator of the derivative, after removing factors that are everywhere positive. -/
noncomputable def criticalPoly (p : ℝ[X]) (N : ℕ) : ℝ[X] :=
  (X ^ 2 + 1) * p.derivative - C (N : ℝ) * (X * p)

theorem coeff_criticalPoly (p : ℝ[X]) (N : ℕ) :
    (criticalPoly p N).coeff (p.natDegree + 1) =
      ((p.natDegree : ℝ) - N) * p.leadingCoeff := by
  have hz : p.derivative.coeff (p.natDegree + 1) = 0 := by
    rw [coeff_derivative, coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  simp only [criticalPoly, add_mul, one_mul, coeff_sub, coeff_add, coeff_C_mul,
    coeff_X_mul, hz, add_zero]
  cases hn : p.natDegree with
  | zero =>
    simp [coeff_X_pow_mul', ← coeff_natDegree, hn]
  | succ n =>
    rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul, coeff_derivative]
    rw [← coeff_natDegree, hn]
    push_cast
    ring

theorem criticalPoly_ne_zero {p : ℝ[X]} (hp : p ≠ 0) {N : ℕ}
    (hN : p.natDegree < N) : criticalPoly p N ≠ 0 := by
  intro hz
  have hcoef := coeff_criticalPoly p N
  rw [hz, coeff_zero] at hcoef
  have hn : (p.natDegree : ℝ) - N ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hN.ne)
  exact mul_ne_zero hn (leadingCoeff_ne_zero.mpr hp) hcoef.symm

theorem eval_mul_criticalPoly_eq_zero {p : ℝ[X]} {N : ℕ} {x : ℝ}
    (hx : IsLocalMax (normalizedSquare p (N + 1)) x) :
    (p * criticalPoly p (N + 1)).eval x = 0 := by
  have hb : x ^ 2 + 1 ≠ 0 := by positivity
  have hb' := ((hasDerivAt_id x).pow 2).add_const (1 : ℝ)
  have hd := ((p.hasDerivAt x).pow 2).div (hb'.pow (N + 1)) (pow_ne_zero _ hb)
  have he : ((fun y : ℝ => p.eval y) ^ 2 /
      (fun y : ℝ => ((id : ℝ → ℝ) ^ 2) y + 1) ^ (N + 1)) =
        normalizedSquare p (N + 1) := by
    funext y
    simp [normalizedSquare]
  rw [he] at hd
  have hz := hx.deriv_eq_zero
  rw [hd.deriv] at hz
  have hz' := (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 (pow_ne_zero _ hb))
  have hf : (2 * (x ^ 2 + 1) ^ N) * (p * criticalPoly p (N + 1)).eval x = 0 := by
    simp only [criticalPoly, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_one, eval_C]
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.reduceSub, pow_one, mul_one] at hz'
    rw [pow_succ (x ^ 2 + 1) N] at hz'
    convert hz' using 1
    ring
  exact (mul_eq_zero.mp hf).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero N hb))

/-- Roots of this polynomial sample every sign region of a finite nonzero family. -/
noncomputable def samplePoly (p : ℝ[X]) (N : ℕ) : ℝ[X] :=
  p * criticalPoly p (N + 1)

theorem samplePoly_ne_zero {p : ℝ[X]} (hp : p ≠ 0) {N : ℕ}
    (hN : p.natDegree ≤ N) : samplePoly p N ≠ 0 :=
  mul_ne_zero hp (criticalPoly_ne_zero hp (by omega))

theorem exists_root_same_sign {ι : Type*} [Fintype ι] (p : ι → ℝ[X])
    (hp : ∀ i, p i ≠ 0) (N : ℕ) (hN : (∏ i, p i).natDegree ≤ N) (x : ℝ) :
    ∃ y ∈ (samplePoly (∏ i, p i) N).roots.toFinset,
      ∀ i, SignType.sign ((p i).eval y) = SignType.sign ((p i).eval x) := by
  classical
  let P := ∏ i, p i
  change P.natDegree ≤ N at hN
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hsample : samplePoly P N ≠ 0 := samplePoly_ne_zero hP hN
  have hzero : ∀ y, (∃ i, (p i).eval y = 0) → normalizedSquare P (N + 1) y = 0 := by
    rintro y ⟨i, hi⟩
    have hy : P.eval y = 0 := by
      simp only [P, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    simp [normalizedSquare, hy]
  by_cases hx : ∃ i, (p i).eval x = 0
  · obtain ⟨i, hi⟩ := hx
    refine ⟨x, ?_, fun _ => rfl⟩
    rw [Multiset.mem_toFinset, mem_roots hsample]
    rw [IsRoot, samplePoly, eval_mul]
    apply mul_eq_zero.mpr ∘ Or.inl
    simp only [P, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  · have hx' : ∀ i, (p i).eval x ≠ 0 := by simpa using hx
    have hPx : P.eval x ≠ 0 := by
      simp only [P, eval_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hx' i)
    obtain ⟨y, hy, hmax⟩ := exists_same_sign_isLocalMax (fun i => (p i).eval)
      (fun i => (p i).differentiable.continuous) (normalizedSquare P (N + 1))
      (continuous_normalizedSquare P (N + 1))
      (tendsto_normalizedSquare hP (by omega)) hzero x hx' (normalizedSquare_pos hPx)
    refine ⟨y, ?_, hy⟩
    rw [Multiset.mem_toFinset, mem_roots hsample]
    exact eval_mul_criticalPoly_eq_zero hmax

end Submission.Helpers

namespace Submission.Helpers

open scoped Polynomial
open Polynomial

noncomputable def conditionsOf (s : Finset ParamPoly) (v : s → SignType) : SignConditions :=
  s.attach.toList.map (fun p => (p.1, v p))

theorem meets_conditionsOf (s : Finset ParamPoly) (v : s → SignType) (env : Env) (x : ℝ) :
    meets (conditionsOf s v) env x ↔
      ∀ p : s, SignType.sign ((specialize env p).eval x) = v p := by
  constructor
  · intro h p
    apply h (p.1, v p)
    exact List.mem_map.mpr ⟨p, Finset.mem_toList.mpr (Finset.mem_attach _ p), rfl⟩
  · intro h c hc
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    exact h p

noncomputable def familyProduct (s : Finset ParamPoly) : ParamPoly := ∏ p ∈ s, p

/-- A uniform sampling polynomial, using the symbolic degree as an upper bound. -/
noncomputable def parameterSample (s : Finset ParamPoly) : ParamPoly :=
  let p := familyProduct s
  p * ((X ^ 2 + 1) * p.derivative - C (p.natDegree + 1 : Coeff) * (X * p))

theorem specialize_familyProduct (s : Finset ParamPoly) (env : Env) :
    specialize env (familyProduct s) = ∏ p : s, specialize env p := by
  rw [Finset.prod_coe_sort]
  exact Polynomial.map_prod (coeffEval env) (fun p => p) s

theorem specialize_parameterSample (s : Finset ParamPoly) (env : Env) :
    specialize env (parameterSample s) =
      samplePoly (specialize env (familyProduct s)) (familyProduct s).natDegree := by
  simp [parameterSample, samplePoly, criticalPoly, specialize, derivative_map]

/-- A finite union over subsets handles coefficients that specialize to zero. -/
theorem signProjection_of_rootQueries (h : HasRootQueries) : HasSignProjection := by
  classical
  intro s v
  have hd : QFDefinable (fun env => ∃ t ∈ s.powerset,
      ∃ x ∈ (specialize env (parameterSample t)).roots.toFinset,
        ∀ p : s, SignType.sign ((specialize env p).eval x) = v p) := by
    apply QFDefinable.exists_finset
    intro t _
    exact (qf_exists_root_meets h (parameterSample t) (conditionsOf s v)).congr
      (fun env => by simp only [meets_conditionsOf])
  apply hd.congr
  intro env
  constructor
  · rintro ⟨t, _, x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    let t := s.filter (fun p => specialize env p ≠ 0)
    have hts : t ⊆ s := Finset.filter_subset _ _
    have ht : ∀ p : t, specialize env p ≠ 0 := fun p =>
      (Finset.mem_filter.mp p.2).2
    have hdegree : (∏ p : t, specialize env p).natDegree ≤ (familyProduct t).natDegree := by
      rw [← specialize_familyProduct]
      exact natDegree_map_le
    obtain ⟨y, hy, hsign⟩ := exists_root_same_sign (fun p : t => specialize env p)
      ht (familyProduct t).natDegree hdegree x
    refine ⟨t, Finset.mem_powerset.mpr hts, y, ?_, ?_⟩
    · simpa only [specialize_parameterSample, specialize_familyProduct] using hy
    · intro p
      by_cases hp : p.1 ∈ t
      · exact (hsign ⟨p, hp⟩).trans (hx p)
      · have hz : specialize env p = 0 := by
          by_contra hn
          exact hp (Finset.mem_filter.mpr ⟨p.2, hn⟩)
        simpa only [hz, eval_zero, sign_zero] using hx p

/-- The remaining algebraic query theorem suffices for all four benchmark declarations. -/
noncomputable def qeFromQueries (h : HasRootQueries)
    (φ : LeanEval.ProgramVerification.RealClosedFieldQE.Formula) :
    LeanEval.ProgramVerification.RealClosedFieldQE.Formula :=
  qeFrom (eliminatesOne_of_signProjection (signProjection_of_rootQueries h)) φ

theorem isQF_qeFromQueries (h : HasRootQueries)
    (φ : LeanEval.ProgramVerification.RealClosedFieldQE.Formula) : (qeFromQueries h φ).IsQF :=
  isQF_qeFrom (eliminatesOne_of_signProjection (signProjection_of_rootQueries h)) φ

theorem holds_qeFromQueries (h : HasRootQueries)
    (φ : LeanEval.ProgramVerification.RealClosedFieldQE.Formula) (env : Env) :
    (qeFromQueries h φ).Holds env ↔ φ.Holds env :=
  holds_qeFrom (eliminatesOne_of_signProjection (signProjection_of_rootQueries h)) φ env

end Submission.Helpers

namespace Submission.LeanEval.ProgramVerification.RealClosedFieldQE

open _root_.LeanEval.ProgramVerification.RealClosedFieldQE

namespace Formula

def tru : Formula := .not .fals

def or (φ ψ : Formula) : Formula := .imp φ.not ψ

def and (φ ψ : Formula) : Formula := (φ.imp ψ.not).not

end Formula

noncomputable def qe (φ : Formula) : Formula :=
  Submission.Helpers.qeFromQueries Submission.Helpers.hasRootQueries φ

theorem isQF_qe (φ : Formula) : (qe φ).IsQF :=
  Submission.Helpers.isQF_qeFromQueries Submission.Helpers.hasRootQueries φ

theorem holds_qe (φ : Formula) (env : Nat → ℝ) :
    (qe φ).Holds env ↔ φ.Holds env :=
  Submission.Helpers.holds_qeFromQueries Submission.Helpers.hasRootQueries φ env

theorem holds_ex_sq (env : Nat → ℝ) :
    (Formula.ex (.eq (.mul (.var 0) (.var 0)) (.var 1))).Holds env ↔
      (Formula.not (.lt (.var 0) (.const 0))).Holds env := by
  simp only [Formula.ex, Formula.not, Formula.Holds, Term.eval, cons, Int.cast_zero]
  constructor
  · intro h hneg
    apply h
    intro x hx
    have hnonneg : 0 ≤ env 0 := by
      rw [← hx]
      exact mul_self_nonneg x
    exact (not_lt_of_ge hnonneg) hneg
  · intro h hall
    exact hall (Real.sqrt (env 0)) (Real.mul_self_sqrt (le_of_not_gt h))

end Submission.LeanEval.ProgramVerification.RealClosedFieldQE
