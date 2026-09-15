import Submission.UniversePrefixBoundary

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

/-- Proper universe coordinates store lower codes, while the final coordinate
stores candidates. Both payloads are defined before their representations. -/
def UniversePayload (r d : Nat) : Type :=
  if d ≤ r then (carrierGrid r d).Code else Candidate

def CarrierObject.ofDataEq (h : X = Y) (O : CarrierObject S Y) : CarrierObject S X := by
  cases h
  exact O

theorem CarrierObject.ofDataEq_code (h : X = Y) (O : CarrierObject S Y) :
    (CarrierObject.ofDataEq h O).code = O.code := by cases h; rfl

noncomputable def UniversePrefix.codeObject (P : UniversePrefix r d) (hd : d ≤ r) :
    CarrierObject (carrierGrid (r + 1) d) (P.El → (carrierGrid r d).Code) := by
  cases d with
  | zero =>
    obtain ⟨T, hT⟩ := P
    have he : T = .nil := hT.empty (Nat.le_refl _)
    subst T
    cases r <;> exact CarrierObject.pullback
      ((CarrierFunction.singletonDomain () (inferInstanceAs (Subsingleton Unit))
        (fun _ => Arity)).toRetraction)
      (CarrierObject.direct shapeCarrierSystem .prop)
  | succ d =>
    exact carrierGridUniverseTelescope r d (by omega) (fun _ => false) id P.telescope
      (P.telescope.all_mono P.ordered.all (fun _ hi => Nat.le_of_lt_succ hi))

/-- One universe representation for every finite depth, including its
candidate boundary. Its recursion is entirely in the already constructed grid. -/
noncomputable def UniversePrefix.object (P : UniversePrefix r d) (hd : d ≤ r + 1) :
    CarrierObject (carrierGrid (r + 1) d) (P.El → UniversePayload r d) := by
  classical
  by_cases hl : d ≤ r
  · exact CarrierObject.ofDataEq (by simp only [UniversePayload, if_pos hl]) (P.codeObject hl)
  · have he : d = r + 1 := by omega
    subst d
    exact CarrierObject.ofDataEq (by simp only [UniversePayload, if_neg (Nat.not_succ_le_self r)]) P.candidateObject

/-- Higher source universes add only a diagonal code inclusion; the payload
and its preceding dependent arguments are unchanged. -/
noncomputable def UniversePrefix.shiftObject (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat) :
    CarrierObject (carrierGrid (r + 1 + k) (d + k)) (P.El → UniversePayload r d) :=
  CarrierObject.map (carrierGridImageEmbedding (r + 1) d k).representation (P.object hd)

noncomputable def UniversePrefix.encode (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat)
    (C : P.El → UniversePayload r d) : TowerValue (carrierGrid (r + 1 + k) (d + k)) :=
  ⟨(P.shiftObject hd k).code, (P.shiftObject hd k).values.encode C⟩

noncomputable def UniversePrefix.decode (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat)
    (v : TowerValue (carrierGrid (r + 1 + k) (d + k))) : P.El → UniversePayload r d :=
  (P.shiftObject hd k).values.decode (v.cast (P.shiftObject hd k).code)

/-- Faithful universe decoding is uniform in its height, current depth and
diagonal offset. The final depth returns actual reducibility candidates. -/
theorem UniversePrefix.decode_encode (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat)
    (C : P.El → UniversePayload r d) : P.decode hd k (P.encode hd k C) = C := by
  unfold decode encode
  rw [TowerValue.cast_mk]
  exact (P.shiftObject hd k).roundtrip C

theorem UniversePrefix.encode_code (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat)
    (C : P.El → UniversePayload r d) : (P.encode hd k C).code = (P.shiftObject hd k).code := rfl

theorem UniversePrefix.shiftObject_image (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat) :
    GridCodeImage (r + 1 + k) (d + k) k (P.shiftObject hd k).code :=
  carrierGridImageCodes_image (r + 1) d k (P.object hd).code

/-- This is the exact source-universe formation rank of the represented sort:
the universe has rank `r + 1`, and its own type has rank `r + 2`. -/
theorem UniversePrefix.shiftObject_formation (P : UniversePrefix r d) (hd : d ≤ r + 1) (k : Nat) :
    GridFormation (r + 1 + k) (d + k) (.type (r + 1)) (P.shiftObject hd k).code := by
  refine ⟨fun h => by simp only [sortRank] at h; omega, ?_⟩
  have he : min (d + k) ((r + 1 + k) + 1 - sortRank (.type (r + 1))) = k := by
    simp only [sortRank]
    omega
  rw [he]
  exact P.shiftObject_image hd k

end Submission.Helpers
