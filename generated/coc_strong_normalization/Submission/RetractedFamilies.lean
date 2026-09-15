import Submission.TelescopeProjection

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- A represented family uses only the retained arguments and returns only
values in the represented output image. -/
structure FamilyAdmissible (R : CarrierRetraction X A) (E : CarrierRetraction Y B) (C : A → B) : Prop where
  image : ∀ a, E.encode (E.decode (C a)) = C a
  canonical : ∀ a, C (R.encode (R.decode a)) = C a

def familyEncode (R : CarrierRetraction X A) (E : CarrierRetraction Y B) (C : A → B) : X → Y :=
  fun x => E.decode (C (R.encode x))

def familyDecode (R : CarrierRetraction X A) (E : CarrierRetraction Y B) (C : X → Y) : A → B :=
  fun a => E.encode (C (R.decode a))

theorem family_encode_decode (R : CarrierRetraction X A) (E : CarrierRetraction Y B) (C : X → Y) :
    familyEncode R E (familyDecode R E C) = C := by
  funext x
  simp only [familyEncode, familyDecode, R.roundtrip, E.roundtrip]

theorem family_decode_admissible (R : CarrierRetraction X A) (E : CarrierRetraction Y B) (C : X → Y) :
    FamilyAdmissible R E (familyDecode R E C) := by
  refine ⟨?_, ?_⟩
  · intro a; simp only [familyDecode, E.roundtrip]
  · intro a; simp only [familyDecode, R.roundtrip]

/-- These two explicit conditions are necessary and sufficient for faithful
family decoding. No source or normalization premise is hidden in the law. -/
theorem family_decode_encode_iff (R : CarrierRetraction X A) (E : CarrierRetraction Y B) (C : A → B) :
    familyDecode R E (familyEncode R E C) = C ↔ FamilyAdmissible R E C := by
  constructor
  · intro h
    rw [← h]
    exact family_decode_admissible R E _
  · intro h
    funext a
    exact (h.image (R.encode (R.decode a))).trans (h.canonical a)

def CarrierRetraction.families (R : CarrierRetraction X A) (E : CarrierRetraction Y B) :
    CarrierRetraction {C : A → B // FamilyAdmissible R E C} (X → Y) where
  encode C := familyEncode R E C.1
  decode C := ⟨familyDecode R E C, family_decode_admissible R E C⟩
  roundtrip C := Subtype.ext ((family_decode_encode_iff R E C.1).mpr C.2)

end Submission.Helpers
