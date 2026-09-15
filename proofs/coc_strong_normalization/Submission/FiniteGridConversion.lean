import Submission.FiniteGridUniverses

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- Equality of semantic types is tested on coherent prefixes and values.
No equation on ill-formed arguments is included in these premises. -/
structure FiniteGridTypeEq (A B : FiniteGridType R) : Prop where
  code : ∀ j hj v, A.carrier.Coherent j (by omega) v → A.carrier.code j hj v = B.carrier.code j hj v
  candidate : ∀ v, A.Valid v → A.candidate v = B.candidate v

variable {R : Nat} {A B C : FiniteGridType R}

theorem FiniteGridTypeEq.coherent_forward (h : FiniteGridTypeEq A B) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) (hv : A.carrier.Coherent d hd v) : B.carrier.Coherent d hd v := by
  intro j hj
  exact (hv j hj).trans (h.code j (by omega) v (hv.mono (by omega)))

theorem FiniteGridTypeEq.coherent_backward (h : FiniteGridTypeEq A B) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) (hv : B.carrier.Coherent d hd v) : A.carrier.Coherent d hd v := by
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    have hp := ih (by omega) (hv.mono (Nat.le_succ _))
    intro i hi
    by_cases hid : i < d
    · exact hp i hid
    · have he : i = d := by omega
      subst i
      exact (hv d (Nat.lt_succ_self _)).trans (h.code d (by omega) v hp).symm

theorem FiniteGridTypeEq.valid_iff (h : FiniteGridTypeEq A B) (v : FiniteGridValue R) :
    A.Valid v ↔ B.Valid v :=
  ⟨h.coherent_forward (R + 1) (Nat.le_refl _) _, h.coherent_backward (R + 1) (Nat.le_refl _) _⟩

theorem FiniteGridTypeEq.normalize_eq (h : FiniteGridTypeEq A B) (d : Nat) (hd : d ≤ R + 1)
    (v : TowerFamily (carrierGrid R)) : A.carrier.normalize d hd v = B.carrier.normalize d hd v := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [CausalGridType.normalize, CausalGridType.normalize, ← ih (by omega)]
    rw [h.code d (by omega) _ (A.carrier.normalize_coherent d (by omega) v)]

noncomputable def FiniteGridType.normalizeValue (A : FiniteGridType R) (v : FiniteGridValue R) :
    FiniteGridValue R := FiniteGridValue.ofTower R
  (A.carrier.normalize (R + 1) (Nat.le_refl _) (FiniteGridValue.toTower R v))

theorem FiniteGridType.normalizeValue_valid (A : FiniteGridType R) (v : FiniteGridValue R) :
    A.Valid (A.normalizeValue v) := A.carrier.valid_ofTower _ (A.carrier.normalize_coherent _ _ _)

theorem FiniteGridType.normalizeValue_eq (A : FiniteGridType R) (v : FiniteGridValue R) (hv : A.Valid v) :
    A.normalizeValue v = v :=
  (FiniteGridValue.ofTower_congr R _ _ (A.carrier.normalize_recover (R + 1) (Nat.le_refl _) _ hv)).trans
    (FiniteGridValue.ofTower_toTower R v)

noncomputable def FiniteGridType.canonicalCandidate (A : FiniteGridType R) (v : FiniteGridValue R) : Candidate :=
  A.candidate (A.normalizeValue v)

theorem FiniteGridType.canonicalCandidate_eq (A : FiniteGridType R) (v : FiniteGridValue R) (hv : A.Valid v) :
    A.canonicalCandidate v = A.candidate v := congrArg A.candidate (A.normalizeValue_eq v hv)

/-- Equality proved only on coherent data yields candidate conversion on
every finite input after canonicalization, as required by `BoundedModel`. -/
theorem FiniteGridTypeEq.canonicalCandidate_eq (h : FiniteGridTypeEq A B) :
    A.canonicalCandidate = B.canonicalCandidate := by
  funext v
  have he : A.normalizeValue v = B.normalizeValue v :=
    congrArg (FiniteGridValue.ofTower R) (h.normalize_eq (R + 1) (Nat.le_refl _) (FiniteGridValue.toTower R v))
  exact (h.candidate _ (A.normalizeValue_valid v)).trans (congrArg B.candidate he)

theorem FiniteGridTypeEq.refl (A : FiniteGridType R) : FiniteGridTypeEq A A :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem FiniteGridTypeEq.symm (h : FiniteGridTypeEq A B) : FiniteGridTypeEq B A :=
  ⟨fun j hj v hv => (h.code j hj v (h.coherent_backward j (by omega) v hv)).symm,
    fun v hv => (h.candidate v ((h.valid_iff v).mpr hv)).symm⟩

theorem FiniteGridTypeEq.trans (h : FiniteGridTypeEq A B) (h' : FiniteGridTypeEq B C) : FiniteGridTypeEq A C :=
  ⟨fun j hj v hv => (h.code j hj v hv).trans
      (h'.code j hj v (h.coherent_forward j (by omega) v hv)),
    fun v hv => (h.candidate v hv).trans (h'.candidate v ((h.valid_iff v).mp hv))⟩

end Submission.Helpers
