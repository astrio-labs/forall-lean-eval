import Submission.CarrierGridRepresentation

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

theorem CarrierRetraction.injective (R : CarrierRetraction A B) : Function.Injective R.encode := by
  intro x y h
  have he := congrArg R.decode h
  rw [R.roundtrip, R.roundtrip] at he
  exact he

noncomputable def CarrierRetraction.ofInjection (f : A → B) (hf : Function.Injective f) (p : A) :
    CarrierRetraction A B where
  encode := f
  decode y := by
    classical
    exact if h : ∃ x, f x = y then Classical.choose h else p
  roundtrip x := by
    classical
    have h : ∃ y, f y = f x := ⟨x, rfl⟩
    simp only [dif_pos h]
    exact hf (Classical.choose_spec h)

/-- A representation whose map on codes also has an exact decoder. -/
structure CarrierEmbedding (S T : CarrierSystem) where
  codes : CarrierRetraction S.Code T.Code
  values : (A : S.Code) → CarrierRetraction (S.El A) (T.El (codes.encode A))

def CarrierEmbedding.representation (E : CarrierEmbedding S T) : CarrierRepresentation S T :=
  ⟨E.codes.encode, E.values⟩

namespace LayerCode

variable {S I T J : CarrierSystem} {U V : CarrierAtoms}

def mapCode (s : S.Code → T.Code) (Q : CarrierRepresentation I J) (u : U.Code → V.Code) :
    LayerCode S I U → LayerCode T J V
  | .small A => .small (s A)
  | .atom A => .atom (u A)
  | .fn A B => .fn (mapCode s Q u A) (mapCode s Q u B)
  | .all A B => .all (Q.code A) (fun x => mapCode s Q u (B ((Q.values A).decode x)))

theorem mapCode_injective (s : S.Code → T.Code) (Q : CarrierRepresentation I J) (u : U.Code → V.Code)
    (hs : Function.Injective s) (hQ : Function.Injective Q.code) (hu : Function.Injective u) :
    Function.Injective (mapCode s Q u) := by
  intro A
  induction A with
  | small a =>
    intro B h
    cases B <;> simp only [mapCode, LayerCode.small.injEq, reduceCtorEq] at h
    exact congrArg LayerCode.small (hs h)
  | atom a =>
    intro B h
    cases B <;> simp only [mapCode, LayerCode.atom.injEq, reduceCtorEq] at h
    exact congrArg LayerCode.atom (hu h)
  | fn A B ihA ihB =>
    intro C h
    cases C <;> simp only [mapCode, LayerCode.fn.injEq, reduceCtorEq] at h
    exact (congrArg (fun a => LayerCode.fn a _) (ihA h.1)).trans
      (congrArg (LayerCode.fn _) (ihB h.2))
  | all a B ih =>
    intro C h
    cases C with
    | small => cases h
    | atom => cases h
    | fn => cases h
    | all a' B' =>
      have he : Q.code a = Q.code a' := congrArg LayerCode.indexCode h
      have ha := hQ he
      subst a'
      have hh := LayerCode.all.inj h
      have hb := eq_of_heq hh.2
      apply congrArg (LayerCode.all a)
      funext x
      apply ih x
      have hx := congrFun hb ((Q.values a).encode x)
      rw [(Q.values a).roundtrip] at hx
      exact hx

noncomputable def mapRetraction (R : CarrierRetraction S.Code T.Code) (Q : CarrierEmbedding I J)
    (u : U.Code → V.Code) (hu : Function.Injective u) :
    CarrierRetraction (layerCarrierSystem S I U).Code (layerCarrierSystem T J V).Code :=
  CarrierRetraction.ofInjection (mapCode R.encode Q.representation u)
    (mapCode_injective R.encode Q.representation u R.injective Q.codes.injective hu)
    (.small S.defaultCode)

def mapValues (s : S.Code → T.Code) (Q : CarrierRepresentation I J) (u : U.Code → V.Code)
    (R : (A : S.Code) → CarrierRetraction (S.El A) (T.El (s A)))
    (P : (A : U.Code) → CarrierRetraction (U.El A) (V.El (u A))) :
    (A : LayerCode S I U) → CarrierRetraction (A.El S I U) ((mapCode s Q u A).El T J V)
  | .small A => R A
  | .atom A => P A
  | .fn A B => (mapValues s Q u R P A).arrow (mapValues s Q u R P B)
  | .all A B => CarrierRetraction.pi (Q.values A)
      (fun x => (B x).El S I U) (fun x => (mapCode s Q u (B x)).El T J V)
      (fun x => mapValues s Q u R P (B x))

end LayerCode
end Submission.Helpers
