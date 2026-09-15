import Submission.ThirdSemantics

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def thirdSortCode (s : Srt) (k : Arity) (m : MiddleValue) : ThirdCode :=
  match s with
  | .prop => .small (.small .prop)
  | .type 0 => .small (.small (.fn (m.cast (.small .prop)) .prop))
  | .type 1 => .small (FiberCode.pi k (m.cast (.universe k)) (fun _ => .small .prop))
  | _ => .small (.small .unit)

theorem inferredThird_sort (h : BoundedTyping 3 Γ t (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    inferredThird Γ ρ δ t = thirdSortCode s (nextArity 3 1 Γ ρ t) (middleSemantics Γ ρ δ t).1 := by
  rw [inferredThird_eq h hρ hδ]
  cases s with
  | prop => rfl
  | type i => cases i with
    | zero => rfl
    | succ j => cases j <;> rfl

theorem thirdEncode_code (s : Srt) (k : Arity) (m : MiddleValue)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate) :
    (thirdEncode (some s) k m C).code = thirdSortCode s k m := by
  cases s with
  | prop => rfl
  | type i => cases i with
    | zero => rfl
    | succ j => cases j <;> rfl

theorem thirdEncode_typed_code (h : BoundedTyping 3 Γ t (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate) :
    (thirdEncode (some s) (nextArity 3 1 Γ ρ t) (middleSemantics Γ ρ δ t).1 C).code =
      inferredThird Γ ρ δ t := by
  rw [thirdEncode_code, inferredThird_sort h hρ hδ]

theorem thirdSemantics_pi_value (h : BoundedTyping 3 Γ (.pi A B) (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.pi A B)).1 =
      thirdEncode (some s) (nextArity 3 1 Γ ρ (.pi A B)) (middleSemantics Γ ρ δ (.pi A B)).1
        (thirdSemantics Γ ρ δ ε (.pi A B)).2 := by
  change ThirdValue.force _ (thirdEncode _ _ _ _) = _
  rw [typeSort_eq h]
  exact ThirdValue.force_eq _ (thirdEncode_typed_code h hρ hδ _)

theorem thirdSemantics_sort_value (h : BoundedTyping 3 Γ (.srt r) (.srt s))
    (hρ : ShapeContext (.type 1) Γ ρ) (hδ : MiddleContext 3 1 Γ ρ δ) :
    (thirdSemantics Γ ρ δ ε (.srt r)).1 =
      thirdEncode (some s) (nextArity 3 1 Γ ρ (.srt r)) (middleSemantics Γ ρ δ (.srt r)).1
        (fun _ _ _ => Candidate.sn) := by
  change ThirdValue.force _ (thirdEncode _ _ _ _) = _
  rw [typeSort_eq h]
  exact ThirdValue.force_eq _ (thirdEncode_typed_code h hρ hδ _)

theorem thirdDecode_encode_prop (k : Arity) (m : MiddleValue)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue) :
    thirdDecode (some .prop) k m (thirdEncode (some .prop) k m C) u f g = C .unit .unit .unit :=
  ThirdValue.cast_mk (.small (.small .prop)) _

theorem thirdDecode_encode_type_zero (k : Arity) (m : MiddleValue)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue) :
    thirdDecode (some (.type 0)) k m (thirdEncode (some (.type 0)) k m C) u f g =
      C .unit .unit (g.force (.small (.small (m.cast (.small .prop))))) :=
  congrFun (ThirdValue.cast_mk (.small (.small (.fn (m.cast (.small .prop)) .prop)))
    (fun z => C .unit .unit ⟨.small (.small (m.cast (.small .prop))), z⟩))
    (g.cast (.small (.small (m.cast (.small .prop)))))

theorem thirdDecode_encode_type_one (k : Arity) (m : MiddleValue)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue) :
    thirdDecode (some (.type 1)) k m (thirdEncode (some (.type 1)) k m C) u f g =
      C .unit (f.force (.small k))
        (g.force (.small (m.cast (.universe k) (f.cast (.small k))))) := by
  let F : k.ShapeEl → FiberCode := m.cast (.universe k)
  change FiberCode.piApply k F (fun _ => .small .prop)
    ((ThirdValue.mk (.small (FiberCode.pi k F (fun _ => .small .prop)))
      (FiberCode.piLambda k F (fun _ => .small .prop)
        (fun y z => C .unit ⟨.small k, y⟩ ⟨.small (F y), z⟩))).cast (.small (FiberCode.pi k F (fun _ => .small .prop))))
    (f.cast (.small k)) (g.cast (.small (F (f.cast (.small k))))) = _
  rw [ThirdValue.cast_mk (.small (FiberCode.pi k F (fun _ => .small .prop)))
    (FiberCode.piLambda k F (fun _ => .small .prop)
      (fun y z => C .unit ⟨.small k, y⟩ ⟨.small (F y), z⟩))]
  exact FiberCode.piBeta k F (fun _ => .small .prop)
    (fun y z => C .unit ⟨.small k, y⟩ ⟨.small (F y), z⟩)
    (f.cast (.small k)) (g.cast (.small (F (f.cast (.small k)))))

theorem ThirdValue.force_unit (g : ThirdValue) : g.force (.small (.small .unit)) = .unit := by
  have he : g.cast (.small (.small .unit)) = (Unit.unit : Unit) :=
    @Subsingleton.elim Unit inferInstance _ _
  change ThirdValue.mk _ (g.cast _) = _
  rw [he]
  rfl

@[simp] theorem ThirdValue.force_force (g : ThirdValue) (D : ThirdCode) :
    (g.force D).force D = g.force D := ThirdValue.force_eq _ rfl

@[simp] theorem MiddleValue.cast_force (f : MiddleValue) (D : MiddleCode) :
    (f.force D).cast D = f.cast D := MiddleValue.cast_mk D (f.cast D)

theorem thirdCanonical_unit (D : MiddleCode) (d : ShapeValue → MiddleValue → ThirdCode)
    (C : ShapeValue → MiddleValue → ThirdValue → Candidate)
    (u : ShapeValue) (f : MiddleValue) (g : ThirdValue) :
    thirdCanonical .unit (fun _ => D) d C u f g =
      C .unit (f.force D) (g.force (d .unit (f.force D))) := by
  unfold thirdCanonical
  dsimp only
  rw [ShapeValue.eq_unit (u.force .unit) rfl]

end Submission.Helpers
