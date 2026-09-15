import Submission.CarrierGrid

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

/-- The distinguished carrier is a singleton; this is a semantic property,
with no assertion about the universe bound of a source derivation. -/
structure CarrierTerminal (S : CarrierSystem) : Prop where
  subsingleton : Subsingleton (S.El S.defaultCode)

/-- Compact arrows retain their application and abstraction operations. -/
structure CarrierArrows (S : CarrierSystem) where
  terminal : CarrierTerminal S
  code : S.Code → S.Code → S.Code
  functions : (A B : S.Code) → CarrierFunction (S.El A) (fun _ => S.El B) (S.El (code A B))
  trivial : ∀ A, code A S.defaultCode = S.defaultCode

/-- A quantifier's index is in the preceding coordinate. -/
structure CarrierQuantifiers (I S : CarrierSystem) where
  code : (a : I.Code) → (I.El a → S.Code) → S.Code
  functions : (a : I.Code) → (B : I.El a → S.Code) →
    CarrierFunction (I.El a) (fun x => S.El (B x)) (S.El (code a B))
  trivial : ∀ a B, (∀ x, B x = S.defaultCode) → code a B = S.defaultCode
  single : ∀ B, code I.defaultCode B = B (I.point I.defaultCode)

def CarrierFunction.singletonDomain (x : X) (h : Subsingleton X) (Y : X → Type) :
    CarrierFunction X Y (Y x) where
  lambda f := f x
  apply y z := cast (congrArg Y (h.elim x z)) y
  beta f z := dependent_cast_apply f (h.elim x z)

def CarrierFunction.singletonRange (p : Z) (Y : X → Type)
    (q : ∀ x, Y x) (h : ∀ x, Subsingleton (Y x)) : CarrierFunction X Y Z where
  lambda _ := p
  apply _ x := q x
  beta _f x := (h x).elim _ _

namespace LayerCode

variable {S I : CarrierSystem} {U : CarrierAtoms}

def asSmall : LayerCode S I U → S.Code
  | .small a => a
  | _ => S.defaultCode

def IsSmall (A : LayerCode S I U) : Prop := ∃ a, A = .small a

theorem isSmall_iff (A : LayerCode S I U) : A.IsSmall ↔ A = .small A.asSmall := by
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro h; exact ⟨_, h⟩

theorem terminal (h : CarrierTerminal S) : CarrierTerminal (layerCarrierSystem S I U) := ⟨h.subsingleton⟩

noncomputable def compactArrow (P : CarrierArrows S) (A B : LayerCode S I U) : LayerCode S I U := by
  classical
  exact if B = .small S.defaultCode then .small S.defaultCode else
    match A, B with
    | .small a, .small b => .small (P.code a b)
    | _, _ => .fn A B

theorem compactArrow_trivial (P : CarrierArrows S) (A : LayerCode S I U) :
    compactArrow P A (.small S.defaultCode) = .small S.defaultCode := by
  classical
  simp only [compactArrow, ↓reduceIte]

theorem compactArrow_small (P : CarrierArrows S) (a b : S.Code) :
    compactArrow (I := I) (U := U) P (.small a) (.small b) = .small (P.code a b) := by
  classical
  by_cases h : b = S.defaultCode
  · subst b
    rw [compactArrow_trivial, P.trivial]
  · have he : (LayerCode.small b : LayerCode S I U) ≠ .small S.defaultCode := by
      intro he; exact h (LayerCode.small.inj he)
    simp only [compactArrow, if_neg he]

noncomputable def compactArrowFunctions (P : CarrierArrows S) (A B : LayerCode S I U) :
    CarrierFunction (A.El S I U) (fun _ => B.El S I U)
      ((compactArrow P A B).El S I U) := by
  classical
  unfold compactArrow
  split
  · rename_i h
    exact CarrierFunction.singletonRange (S.point S.defaultCode) _
      (fun _ => B.point S I U) (fun _ => by rw [h]; exact P.terminal.subsingleton)
  · cases A <;> cases B
    · exact P.functions _ _
    all_goals exact CarrierFunction.direct _ _

noncomputable def arrows (P : CarrierArrows S) : CarrierArrows (layerCarrierSystem S I U) where
  terminal := terminal P.terminal
  code := compactArrow P
  functions := compactArrowFunctions P
  trivial := compactArrow_trivial P

/-- Free quantifiers still collapse constant singleton families and the
distinguished singleton index. -/
noncomputable def freeAll (_hI : CarrierTerminal I) (_hS : CarrierTerminal S)
    (a : I.Code) (B : I.El a → LayerCode S I U) : LayerCode S I U := by
  classical
  exact if ∀ x, B x = .small S.defaultCode then .small S.defaultCode else
    if a = I.defaultCode then B (I.point a) else .all a B

theorem freeAll_trivial (hI : CarrierTerminal I) (hS : CarrierTerminal S)
    (a : I.Code) (B : I.El a → LayerCode S I U)
    (h : ∀ x, B x = .small S.defaultCode) : freeAll hI hS a B = .small S.defaultCode := by
  classical
  simp only [freeAll, if_pos h]

theorem freeAll_single (hI : CarrierTerminal I) (hS : CarrierTerminal S)
    (B : I.El I.defaultCode → LayerCode S I U) :
    freeAll hI hS I.defaultCode B = B (I.point I.defaultCode) := by
  classical
  by_cases h : ∀ x, B x = .small S.defaultCode
  · rw [freeAll_trivial hI hS _ B h, h (I.point I.defaultCode)]
  · simp only [freeAll, if_neg h, ↓reduceIte]

noncomputable def freeAllFunctions (hI : CarrierTerminal I) (hS : CarrierTerminal S)
    (a : I.Code) (B : I.El a → LayerCode S I U) :
    CarrierFunction (I.El a) (fun x => (B x).El S I U) ((freeAll hI hS a B).El S I U) := by
  classical
  unfold freeAll
  split
  · rename_i h
    exact CarrierFunction.singletonRange (S.point S.defaultCode) _
      (fun x => (B x).point S I U) (fun x => by rw [h x]; exact hS.subsingleton)
  · split
    · rename_i h
      exact CarrierFunction.singletonDomain (I.point a) (by rw [h]; exact hI.subsingleton) _
    · exact CarrierFunction.direct _ _

noncomputable def freeQuantifiers (hI : CarrierTerminal I) (hS : CarrierTerminal S) :
    CarrierQuantifiers I (layerCarrierSystem S I U) where
  code := freeAll hI hS
  functions := freeAllFunctions hI hS
  trivial := freeAll_trivial hI hS
  single := freeAll_single hI hS

variable {J K : CarrierSystem} {V : CarrierAtoms}

/-- Folding a dependent product transports its values through the pointwise
proof that the result codes are small. -/
noncomputable def smallAllFunctions (Q : CarrierQuantifiers J S) (a : J.Code)
    (B : J.El a → LayerCode S I U) (h : ∀ x, B x = .small (B x).asSmall) :
    CarrierFunction (J.El a) (fun x => (B x).El S I U)
      (S.El (Q.code a (fun x => (B x).asSmall))) where
  lambda f := (Q.functions a _).lambda (fun x => cast (congrArg (El S I U) (h x)) (f x))
  apply f x := cast (congrArg (El S I U) (h x).symm) ((Q.functions a _).apply f x)
  beta f x := by
    rw [(Q.functions a _).beta]
    exact fiber_cast_cancel _ _ (f x)

/-- The square between adjacent rows folds products of old codes to the
already constructed lower product. The index decoder never recurses here. -/
noncomputable def compactAll (Q : CarrierQuantifiers J S)
    (_hJ : CarrierTerminal J) (_hS : CarrierTerminal S)
    (A : LayerCode J K V)
    (B : (A.El J K V) → LayerCode S (layerCarrierSystem J K V) U) :
    LayerCode S (layerCarrierSystem J K V) U := by
  classical
  exact if ∀ x, B x = .small S.defaultCode then .small S.defaultCode else
    if A = .small J.defaultCode then B (A.point J K V) else
      match A with
      | .small a =>
        if ∀ x, B x = .small (B x).asSmall then
          .small (Q.code a (fun x => (B x).asSmall)) else .all (.small a) B
      | A' => .all A' B

theorem compactAll_trivial (Q : CarrierQuantifiers J S)
    (hJ : CarrierTerminal J) (hS : CarrierTerminal S)
    (A : LayerCode J K V) (B : A.El J K V → LayerCode S (layerCarrierSystem J K V) U)
    (h : ∀ x, B x = .small S.defaultCode) : compactAll Q hJ hS A B = .small S.defaultCode := by
  classical
  simp only [compactAll, if_pos h]

theorem compactAll_single (Q : CarrierQuantifiers J S)
    (hJ : CarrierTerminal J) (hS : CarrierTerminal S)
    (B : (LayerCode.small J.defaultCode : LayerCode J K V).El J K V →
      LayerCode S (layerCarrierSystem J K V) U) :
    compactAll Q hJ hS (.small J.defaultCode) B = B (J.point J.defaultCode) := by
  classical
  by_cases h : ∀ x, B x = .small S.defaultCode
  · rw [compactAll_trivial Q hJ hS (.small J.defaultCode) B h, h (J.point J.defaultCode)]
  · simp only [compactAll, if_neg h, ↓reduceIte, point]

theorem compactAll_small (Q : CarrierQuantifiers J S)
    (hJ : CarrierTerminal J) (hS : CarrierTerminal S) (a : J.Code) (B : J.El a → S.Code) :
    compactAll (K := K) (V := V) (U := U) Q hJ hS (.small a) (fun x => .small (B x)) =
      .small (Q.code a B) := by
  classical
  unfold compactAll
  simp only [El, asSmall, small.injEq, implies_true, ↓reduceIte, point]
  by_cases h : ∀ x, B x = S.defaultCode
  · rw [if_pos h, Q.trivial a B h]
  · rw [if_neg h]
    by_cases ha : a = J.defaultCode
    · subst a
      rw [if_pos rfl, Q.single]
    · rw [if_neg ha]

noncomputable def compactAllFunctions (Q : CarrierQuantifiers J S)
    (hJ : CarrierTerminal J) (hS : CarrierTerminal S)
    (A : LayerCode J K V) (B : A.El J K V → LayerCode S (layerCarrierSystem J K V) U) :
    CarrierFunction (A.El J K V) (fun x => (B x).El S (layerCarrierSystem J K V) U)
      ((compactAll Q hJ hS A B).El S (layerCarrierSystem J K V) U) := by
  classical
  unfold compactAll
  split
  · rename_i h
    exact CarrierFunction.singletonRange (S.point S.defaultCode) _
      (fun x => (B x).point _ _ _) (fun x => by rw [h x]; exact hS.subsingleton)
  · split
    · rename_i h
      exact CarrierFunction.singletonDomain (A.point J K V) (by rw [h]; exact hJ.subsingleton) _
    · cases A with
      | small a =>
        dsimp only
        split
        · rename_i h
          exact smallAllFunctions Q a B h
        · exact CarrierFunction.direct _ _
      | atom => exact CarrierFunction.direct _ _
      | fn => exact CarrierFunction.direct _ _
      | all => exact CarrierFunction.direct _ _

noncomputable def quantifiers (Q : CarrierQuantifiers J S)
    (hJ : CarrierTerminal J) (hS : CarrierTerminal S) :
    CarrierQuantifiers (layerCarrierSystem J K V)
      (layerCarrierSystem S (layerCarrierSystem J K V) U) where
  code := compactAll Q hJ hS
  functions := compactAllFunctions Q hJ hS
  trivial := compactAll_trivial Q hJ hS
  single := compactAll_single Q hJ hS

end LayerCode
end Submission.Helpers
