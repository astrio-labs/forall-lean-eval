import Submission.CarrierGridAlgebra

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

namespace LayerCode

variable {S I J K T : CarrierSystem} {U V : CarrierAtoms}

/-- An intermediate universe stores exactly a family of codes in its lower
row, indexed by the already available preceding value. -/
def universeEncode (a : I.Code) (C : I.El a → LayerCode S J U) :
    (LayerCode.atom a : LayerCode T I (universeCarrierAtoms I S)).El T I (universeCarrierAtoms I S) :=
  fun x => (C x).asSmall

def universeDecode (a : I.Code)
    (v : (LayerCode.atom a : LayerCode T I (universeCarrierAtoms I S)).El T I (universeCarrierAtoms I S)) :
    I.El a → LayerCode S J U := fun x => .small (v x)

/-- The factorization premise is both necessary and sufficient. No claim
about source universes is hidden in this roundtrip. -/
theorem universe_decode_encode_iff (a : I.Code) (C : I.El a → LayerCode S J U) :
    universeDecode (T := T) a (universeEncode a C) = C ↔ ∀ x, (C x).IsSmall := by
  constructor
  · intro h x
    exact ⟨_, (congrFun h x).symm⟩
  · intro h
    funext x
    exact ((isSmall_iff (C x)).mp (h x)).symm

theorem universe_decode_encode (a : I.Code) (C : I.El a → LayerCode S J U)
    (h : ∀ x, (C x).IsSmall) : universeDecode (T := T) a (universeEncode a C) = C :=
  (universe_decode_encode_iff a C).mpr h

theorem universe_encode_decode (a : I.Code)
    (v : (LayerCode.atom a : LayerCode T I (universeCarrierAtoms I S)).El T I (universeCarrierAtoms I S)) :
    universeEncode a (universeDecode (J := J) (U := U) a v) = v := rfl

theorem compactArrow_isSmall (P : CarrierArrows S) {A B : LayerCode S I U}
    (hA : A.IsSmall) (hB : B.IsSmall) : (compactArrow P A B).IsSmall := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  exact ⟨_, compactArrow_small P a b⟩

theorem compactAll_isSmall (Q : CarrierQuantifiers J S)
    (hJ : CarrierTerminal J) (hS : CarrierTerminal S)
    (a : J.Code) (B : J.El a → LayerCode S (layerCarrierSystem J K V) U)
    (h : ∀ x, (B x).IsSmall) : (compactAll Q hJ hS (.small a) B).IsSmall := by
  let C := fun x => (B x).asSmall
  have he : B = fun x => .small (C x) := funext (fun x => (isSmall_iff (B x)).mp (h x))
  exact ⟨Q.code a C, (congrArg (compactAll Q hJ hS (.small a)) he).trans
    (compactAll_small Q hJ hS a C)⟩

/-- Product closure supplies the exact premise required by universe decoding. -/
theorem universe_decode_product (Q : CarrierQuantifiers J S)
    (hJ : CarrierTerminal J) (P : CarrierArrows S) (a : I.Code)
    (D : I.El a → J.Code)
    (A B : (x : I.El a) → J.El (D x) → LayerCode S (layerCarrierSystem J K V) U)
    (hA : ∀ x y, (A x y).IsSmall) (hB : ∀ x y, (B x y).IsSmall) :
    universeDecode (T := T) a (universeEncode a
      (fun x => (quantifiers Q hJ P.terminal).pi (arrows P) (.small (D x)) (A x) (B x))) =
      fun x => (quantifiers Q hJ P.terminal).pi (arrows P) (.small (D x)) (A x) (B x) := by
  apply universe_decode_encode
  intro x
  exact compactAll_isSmall Q hJ P.terminal (D x) _
    (fun y => compactArrow_isSmall P (hA x y) (hB x y))

end LayerCode

/-- At every square, encoding a compact product returns the preceding row's
product code, rather than merely an isomorphic carrier. -/
theorem carrierGrid_encode_pi (r d : Nat) (A : (carrierGrid (r + 1) d).Code)
    (D B : (carrierGrid (r + 1) d).El A → (carrierGrid (r + 1) (d + 1)).Code) :
    LayerCode.asSmall ((carrierGridQuantifiers (r + 1) (d + 1)).pi
      (carrierGridArrows (r + 2) (d + 2)) (.small A)
      (fun x => .small (D x)) (fun x => .small (B x))) =
    (carrierGridQuantifiers r d).pi (carrierGridArrows (r + 1) (d + 1)) A D B :=
  congrArg LayerCode.asSmall (carrierGrid_pi_small r d A D B)

end Submission.Helpers
