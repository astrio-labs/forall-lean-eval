import Submission.CompletePrefixes
import Submission.UniverseProducts

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

def TowerFamily.AgreeBelow {S : Nat → CarrierSystem} (d : Nat) (v w : TowerFamily S) : Prop :=
  ∀ i, i < d → v i = w i

def TowerFamily.DependsBelow {S : Nat → CarrierSystem} (d : Nat) (f : TowerFamily S → X) : Prop :=
  ∀ v w, AgreeBelow d v w → f v = f w

/-- A local reverse decoding law: formation and compatibility of the actual
argument suffice. No global projection-invariance premise is assumed. -/
theorem UniversePrefix.read_store_coherent (P : UniversePrefix r d) (hP : P.Full)
    (hd : d ≤ r) (k : Nat)
    (C : TowerFamily (universeArgumentSystems r k) → (carrierGrid (r + 1 + k) (d + 1 + k)).Code)
    (hdep : TowerFamily.DependsBelow d C)
    (v : TowerFamily (universeArgumentSystems r k))
    (hv : P.telescope.Compatible (universeArgumentRepresentation r k) v)
    (hform : GridFormation (r + 1 + k) (d + 1 + k) (.type r) (C v)) :
    P.readCodeFamily hd k (P.storeCodeFamily hd k C) v = C v := by
  unfold readCodeFamily storeCodeFamily
  rw [decodeCode_encodeCode]
  dsimp only [familyDecode, familyEncode]
  rw [hdep _ v (fun i hi => P.arguments_recover hP k v hv i hi)]
  exact universeOutputCodes_formed r d k (C v) hform

theorem UniversePrefix.read_store_candidate_coherent (P : UniversePrefix r (r + 1))
    (hP : P.Full) (k : Nat)
    (C : TowerFamily (universeArgumentSystems r k) → Candidate)
    (hdep : TowerFamily.DependsBelow (r + 1) C)
    (v : TowerFamily (universeArgumentSystems r k))
    (hv : P.telescope.Compatible (universeArgumentRepresentation r k) v) :
    P.readCandidateFamily k (P.storeCandidateFamily k C) v = C v := by
  unfold readCandidateFamily storeCandidateFamily
  rw [decodeCandidate_encodeCandidate]
  exact hdep _ v (fun i hi => P.arguments_recover hP k v hv i hi)

theorem universeProductCode_congr (r d k : Nat) (hd : d ≤ r)
    (T : CarrierTelescope (carrierGrid (r + k + 1))) (hw : T.Within (d + k))
    (D B B' : T.El → (carrierGrid (r + k + 1) (d + k + 1)).Code)
    (hB : ∀ x, B x = B' x) :
    universeProductCode r d k hd T hw D B = universeProductCode r d k hd T hw D B' := by
  rw [funext hB]

/-- Product families may be evaluated directly on coherent arguments.
Only the preceding application data are required to be causal; product
formation supplies the output-image condition. -/
theorem UniversePrefix.read_store_product_coherent (P : UniversePrefix r d) (hP : P.Full)
    (hd : d ≤ r) (k : Nat)
    (T : CarrierTelescope (carrierGrid (r + k + 1))) (hw : T.Within (d + k))
    (D : T.El → (carrierGrid (r + k + 1) (d + k + 1)).Code)
    (app : TowerFamily (universeArgumentSystems r k) → T.El → X)
    (happ : TowerFamily.DependsBelow d app)
    (B : T.El → X → (carrierGrid (r + k + 1) (d + k + 1)).Code)
    (hr : Rl sA sB (.type r)) (hT : T.GridForm (r + k + 1) sA)
    (hD : ∀ x, GridFormation (r + k + 1) (d + k + 1) sA (D x))
    (v : TowerFamily (universeArgumentSystems r k))
    (hv : P.telescope.Compatible (universeArgumentRepresentation r k) v)
    (hB : ∀ x, GridFormation (r + k + 1) (d + k + 1) sB (B x (app v x))) :
    let C := fun w => universeProductCode r d k hd T hw D (fun x => B x (app w x))
    P.readCodeFamily hd k (P.storeCodeFamily hd k C) v = C v := by
  apply P.read_store_coherent hP hd k _ ?_ v hv
    (universeProductCode_formation r d k hd T hw D _ hr hT hD hB)
  intro u w huw
  dsimp only
  rw [happ u w huw]

end Submission.Helpers
