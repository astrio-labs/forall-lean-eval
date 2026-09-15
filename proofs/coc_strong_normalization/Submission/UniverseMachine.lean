import Submission.UniformSorts

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true
set_option maxHeartbeats 1000000

theorem CarrierTelescope.project_snoc {S V : Nat → CarrierSystem}
    (R : ∀ i, CarrierRepresentation (S i) (V i)) (T : CarrierTelescope S)
    (i : Nat) (A : T.El → (S i).Code) (v : TowerFamily V) :
    (T.snoc i A).project R v = T.snocEncode i A
      ⟨T.project R v, ((R i).values (A (T.project R v))).decode ((v i).cast ((R i).code (A (T.project R v))))⟩ := by
  induction T with
  | nil => rfl
  | cons j B C ih =>
    simp only [snoc, project, snocEncode]
    exact congrArg (fun y => (⟨_, y⟩ : (x : (S j).El B) × ((C x).snoc i (fun y => A ⟨x, y⟩)).El))
      (ih _ (fun y => A ⟨_, y⟩))

/-- The input prefix consists of values encoding successive lower-row code
families. Its state is the lower type prefix decoded from those values. -/
structure UniverseMachine (r d : Nat) where
  inputs : UniversePrefix (r + 1) d
  state : inputs.El → UniversePrefix r d

noncomputable def UniverseMachine.project (M : UniverseMachine r d)
    (v : TowerFamily (carrierGrid (r + 1))) : M.inputs.El :=
  M.inputs.telescope.project (fun i => CarrierRepresentation.identity (carrierGrid (r + 1) i)) v

noncomputable def UniverseMachine.inputCode (M : UniverseMachine r d) (hd : d ≤ r) :
    M.inputs.El → (carrierGrid (r + 1) d).Code :=
  fun x => ((M.state x).shiftCodeObject hd 0).code

noncomputable def UniverseMachine.step (M : UniverseMachine r d) (hd : d ≤ r) : UniverseMachine r (d + 1) where
  inputs := M.inputs.next (M.inputCode hd)
  state z :=
    let x := (M.inputs.nextValues (M.inputCode hd)).decode z
    (M.state x.1).next (((M.state x.1).shiftCodeObject hd 0).values.decode x.2)

theorem UniverseMachine.step_project (M : UniverseMachine r d) (hd : d ≤ r)
    (v : TowerFamily (carrierGrid (r + 1))) :
    (M.step hd).state ((M.step hd).project v) =
      (M.state (M.project v)).next ((M.state (M.project v)).decodeCode hd 0 (v d)) := by
  unfold step project
  dsimp only
  erw [CarrierTelescope.project_snoc]
  simp only [UniversePrefix.nextValues]
  erw [CarrierTelescope.snoc_roundtrip]
  rfl

/-- The universe machine is constructed by induction on the coordinate,
independently of source syntax and independently of normalization. -/
noncomputable def universeMachine (r : Nat) : (d : Nat) → d ≤ r + 1 → UniverseMachine r d
  | 0, _ => ⟨UniversePrefix.empty (r + 1), fun _ => UniversePrefix.empty r⟩
  | d + 1, hd => (universeMachine r d (by omega)).step (by omega)

/-- The machine's intrinsic dependent input telescope captures exactly the
data read by the uniform universe reconstruction. -/
theorem universeMachine_trace (r d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1))) :
    (universeMachine r d hd).state ((universeMachine r d hd).project v) =
      UniversePrefix.fromValues r 0 d hd v := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [universeMachine, UniverseMachine.step_project, ih, UniversePrefix.fromValues]

noncomputable def UniverseMachine.arguments (M : UniverseMachine r d) :
    CarrierRetraction M.inputs.El (TowerFamily (carrierGrid (r + 1))) :=
  M.inputs.telescope.valuesRetraction (fun i => CarrierRepresentation.identity (carrierGrid (r + 1) i))
    M.inputs.ordered

/-- Uniform sort carriers are already canonical on the dependent input
telescope constructed by the universe machine, even at its bottom boundary. -/
theorem universeSortAt_canonical (r d : Nat) (hd : d ≤ r + 1)
    (v : TowerFamily (carrierGrid (r + 1))) :
    universeSortAt r 0 d hd
      ((universeMachine r d hd).arguments.encode ((universeMachine r d hd).arguments.decode v)) =
      universeSortAt r 0 d hd v := by
  unfold universeSortAt
  rw [← universeMachine_trace r d hd, ← universeMachine_trace r d hd]
  change (((universeMachine r d hd).state
    ((universeMachine r d hd).arguments.decode
      ((universeMachine r d hd).arguments.encode ((universeMachine r d hd).arguments.decode v)))).shiftObject hd 0).code = _
  rw [(universeMachine r d hd).arguments.roundtrip]
  rfl

end Submission.Helpers
