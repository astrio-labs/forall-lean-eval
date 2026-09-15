import Submission.CarrierGridFormation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem CarrierRepresentation.ofEq_layer_small
    {S T I J : CarrierSystem} {U U' V V' : CarrierAtoms}
    (hU : U = U') (hV : V = V')
    (R : CarrierRepresentation S T) (Q : CarrierRepresentation I J)
    (P : CarrierAtomsRepresentation U' V') (A : S.Code) :
    (CarrierRepresentation.ofEq (congrArg (layerCarrierSystem S I) hU)
      (congrArg (layerCarrierSystem T J) hV) (LayerCode.representation R Q P)).code
        (.small A) = .small (R.code A) := by
  cases hU
  cases hV
  rfl

theorem carrierGridHorizontal_small (r d : Nat) (hd : d + 2 < r + 2)
    (A : (carrierGrid (r + 1) d).Code) :
    (carrierGridHorizontal (r + 2) (d + 1) hd).code (.small A) =
      .small ((carrierGridHorizontal (r + 1) d (by omega)).code A) := by
  rw [carrierGridHorizontal]
  let R := carrierGridHorizontal (r + 1) d (by omega)
  let Q := carrierGridHorizontal (r + 2) d (by omega)
  let L : CarrierRetraction (carrierGrid (r + 1) (d + 1)).Code
      (carrierGrid (r + 1) (d + 2)).Code := LayerCode.codeRetraction
  exact CarrierRepresentation.ofEq_layer_small
    (if_pos (α := CarrierAtoms) (e := noCarrierAtoms) (show d < r + 1 by omega))
    (if_pos (α := CarrierAtoms) (e := noCarrierAtoms) (show d + 1 < r + 1 by omega)) R Q
    (universeCarrierRepresentation Q L) A

theorem carrierGridHorizontal_default_aux (r d : Nat) (hd : d + 1 < r + 2) :
    (carrierGridHorizontal (r + 2) d hd).code (carrierGrid (r + 2) d).defaultCode =
      (carrierGrid (r + 2) (d + 1)).defaultCode := by
  induction d generalizing r with
  | zero => rw [carrierGridHorizontal]; rfl
  | succ d ih =>
    cases r with
    | zero => omega
    | succ r =>
      change (carrierGridHorizontal (r + 3) (d + 1) hd).code
        (.small (carrierGrid (r + 2) d).defaultCode) =
        .small (carrierGrid (r + 2) (d + 1)).defaultCode
      rw [carrierGridHorizontal_small, ih]

theorem carrierGridHorizontal_default (r d : Nat) (hd : d + 1 < r) :
    (carrierGridHorizontal r d hd).code (carrierGrid r d).defaultCode =
      (carrierGrid r (d + 1)).defaultCode := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ r => exact carrierGridHorizontal_default_aux r d hd

theorem GridCodeImage.horizontal (h : GridCodeImage r d k A) (hd : d + 1 < r) :
    GridCodeImage r (d + 1) k ((carrierGridHorizontal r d hd).code A) := by
  induction h with
  | base A => exact .base _
  | @small r d k A h ih =>
    cases r with
    | zero => omega
    | succ r =>
      rw [carrierGridHorizontal_small]
      exact .small (ih (by omega))

/-- Horizontal representation preserves source formation without changing
the source universe bound. -/
theorem GridFormation.horizontal (h : GridFormation r d s A) (hd : d + 1 < r) :
    GridFormation r (d + 1) s ((carrierGridHorizontal r d hd).code A) := by
  by_cases hl : sortRank s + d < r + 1
  · rw [h.lower hl, carrierGridHorizontal_default]
    exact gridFormation_default (by omega) s
  · exact ⟨fun hs => (hl (by omega)).elim, (h.image.horizontal hd).mono (by omega)⟩

theorem GridFormation.advance (h : GridFormation r d s A) (k : Nat) (hk : d + k < r) :
    GridFormation r (d + k) s ((carrierGridAdvance r d k hk).code A) := by
  induction k with
  | zero => exact h
  | succ k ih => exact (ih (by omega)).horizontal (by omega)

theorem CarrierRepresentation.ofEq_gridFormation {r a d e : Nat}
    {A : (carrierGrid r a).Code} (he : e = d)
    (R : CarrierRepresentation (carrierGrid r a) (carrierGrid r d))
    (h : GridFormation r d s (R.code A)) :
    GridFormation r e s ((CarrierRepresentation.ofEq rfl (congrArg (carrierGrid r) he) R).code A) := by
  cases he
  exact h

theorem GridFormation.prefix (h : GridFormation r d s A) (hde : d ≤ e) (he : e < r) :
    GridFormation r e s ((carrierGridPrefixRepresentation r d e hde he).code A) :=
  CarrierRepresentation.ofEq_gridFormation (Nat.add_sub_of_le hde).symm _
    (h.advance (e - d) (by omega))

end Submission.Helpers
