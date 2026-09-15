import Submission.FiniteTruncation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

def finiteValueCast (h : R = S) (v : FiniteGridValue R) : FiniteGridValue S := h ▸ v
def finiteTypeCast (h : R = S) (A : FiniteGridType R) : FiniteGridType S := h ▸ A

def FiniteGridType.trivial (R : Nat) : FiniteGridType R where
  carrier := ⟨fun j _ _ => (carrierGrid R j).defaultCode, fun _ _ _ _ _ => rfl⟩
  candidate _ := Candidate.sn

/-- Universe introduction at any finite row. The unrepresented top sort has
terminal values; no decoding law for that top sort is asserted. -/
noncomputable def uniformUniverseEncode (R : Nat) (s : Option Srt) (A : FiniteGridType R) :
    FiniteGridValue R := by
  classical
  exact match s with
  | some .prop => A.reifyProp
  | some (.type i) =>
    if hi : i + 1 ≤ R then
      let k := R - (i + 1)
      let he : i + 1 + k = R := Nat.add_sub_of_le hi
      finiteValueCast he ((finiteTypeCast he.symm A).reify i k)
    else FiniteGridValue.ofTower R (TowerFamily.point (carrierGrid R))
  | none => FiniteGridValue.ofTower R (TowerFamily.point (carrierGrid R))

noncomputable def uniformUniverseDecode (R : Nat) (s : Option Srt) (v : FiniteGridValue R) :
    FiniteGridType R := by
  classical
  exact match s with
  | some .prop => decodePropType R v
  | some (.type i) =>
    if hi : i + 1 ≤ R then
      let k := R - (i + 1)
      let he : i + 1 + k = R := Nat.add_sub_of_le hi
      finiteTypeCast he (decodeUniverseType i k (finiteValueCast he.symm v))
    else FiniteGridType.trivial R
  | none => FiniteGridType.trivial R

theorem finiteUniverseEncode_cast (hk : k' = k) (he : r + 1 + k' = r + 1 + k)
    (A : FiniteGridType (r + 1 + k)) :
    finiteValueCast he ((finiteTypeCast he.symm A).reify r k') = A.reify r k := by
  cases hk
  rfl

theorem finiteUniverseDecode_cast (hk : k' = k) (he : r + 1 + k' = r + 1 + k)
    (v : FiniteGridValue (r + 1 + k)) :
    finiteTypeCast he (decodeUniverseType r k' (finiteValueCast he.symm v)) = decodeUniverseType r k v := by
  cases hk
  rfl

theorem uniformUniverseEncode_at (r k : Nat) (A : FiniteGridType (r + 1 + k)) :
    uniformUniverseEncode (r + 1 + k) (some (.type r)) A = A.reify r k := by
  unfold uniformUniverseEncode
  dsimp only
  rw [dif_pos (show r + 1 ≤ r + 1 + k by omega)]
  exact finiteUniverseEncode_cast (by omega) _ A

theorem uniformUniverseDecode_at (r k : Nat) (v : FiniteGridValue (r + 1 + k)) :
    uniformUniverseDecode (r + 1 + k) (some (.type r)) v = decodeUniverseType r k v := by
  unfold uniformUniverseDecode
  dsimp only
  rw [dif_pos (show r + 1 ≤ r + 1 + k by omega)]
  exact finiteUniverseDecode_cast (by omega) _ v

end Submission.Helpers
