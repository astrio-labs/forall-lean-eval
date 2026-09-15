import Submission.SourceGridFormation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- All value carriers in a source domain's semantic telescope have that
domain's universe formation, at their own coordinates. -/
def CarrierTelescope.GridForm (r : Nat) (s : Srt) : CarrierTelescope (carrierGrid r) → Prop
  | .nil => True
  | .cons i A B => GridFormation r i s A ∧ ∀ x, (B x).GridForm r s

/-- Quantification over any finite semantic telescope preserves formation.
The telescope's length is independent of the row and source bound. -/
theorem carrierGridTelescopeCode_formation (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (hw : T.Within e)
    (C : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (hdom : sC = .prop ∨ sortRank sA ≤ sortRank sC)
    (hT : T.GridForm (r + 1) sA)
    (hC : ∀ x, GridFormation (r + 1) (e + 1) sC (C x)) :
    GridFormation (r + 1) (e + 1) sC (carrierGridTelescopeCode r e he T hw C) := by
  induction T with
  | nil => exact hC ()
  | cons i A B ih =>
    change GridFormation (r + 1) (e + 1) sC
      ((carrierGridQuantifiers r e).code _ _)
    apply gridFormation_all (by omega) hdom (Nat.le_refl _) _ _
      (hT.1.prefix hw.1 he)
    intro x
    exact ih _ (hw.2 _) _ (hT.2 _) (fun y => hC ⟨_, y⟩)

/-- A complete binder, with every preceding coordinate and the current
value, obeys the original product rule at every finite grid bound. -/
theorem carrierGridBinderCode_formation (r e : Nat) (he : e < r + 1)
    (T : CarrierTelescope (carrierGrid (r + 1))) (hw : T.Within e)
    (D B : T.El → (carrierGrid (r + 1) (e + 1)).Code)
    (hr : Rl sA sB sC) (hT : T.GridForm (r + 1) sA)
    (hD : ∀ x, GridFormation (r + 1) (e + 1) sA (D x))
    (hB : ∀ x, GridFormation (r + 1) (e + 1) sB (B x)) :
    GridFormation (r + 1) (e + 1) sC (carrierGridBinderCode r e he T hw D B) :=
  carrierGridTelescopeCode_formation r e he T hw _ (gridRule_domain hr) hT
    (fun x => gridFormation_arrow (by omega) hr (hD x) (hB x))

end Submission.Helpers
