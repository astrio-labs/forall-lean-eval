import Submission.FirstGridOperations

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def CarrierQuantifiers.valueApply (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code) (f : TowerValue S) (x : I.El a) (y : TowerValue S) : TowerValue S :=
  ⟨B x, Q.piApply P a D B (f.cast (Q.pi P a D B)) x (y.cast (D x))⟩

noncomputable def CarrierQuantifiers.valueLambda (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code) (b : I.El a → TowerValue S → TowerValue S) : TowerValue S :=
  ⟨Q.pi P a D B, Q.piLambda P a D B (fun x y => (b x ⟨D x, y⟩).cast (B x))⟩

theorem CarrierQuantifiers.valueLambda_congr (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D B : I.El a → S.Code) (b c : I.El a → TowerValue S → TowerValue S)
    (h : ∀ x y, y.code = D x → b x y = c x y) :
    Q.valueLambda P a D B b = Q.valueLambda P a D B c := by
  unfold valueLambda
  congr 2
  funext x y
  rw [h x ⟨D x, y⟩ rfl]

theorem firstGridApply_congr {r : Nat} {a a' : Arity}
    {D D' : ShapeValue → (carrierGrid (r + 2) 1).Code}
    {B B' : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code}
    {u x : ShapeValue} {f y : FirstGridValue r} (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z) :
    firstGridApply r a D B u f x y = firstGridApply r a' D' B' u f x y := by
  subst a'
  have hd : (fun z : a.ShapeEl => D ⟨a, z⟩) = fun z => D' ⟨a, z⟩ :=
    funext (fun z => hD ⟨a, z⟩ rfl)
  have hb : (fun z : a.ShapeEl => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) =
      fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩) := funext (fun z => hB ⟨a, z⟩ rfl _)
  change (carrierGridQuantifiers (r + 1) 0).valueApply (carrierGridArrows (r + 2) 1) a
    (fun z => D ⟨a, z⟩) (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) f (x.cast a) y =
      (carrierGridQuantifiers (r + 1) 0).valueApply (carrierGridArrows (r + 2) 1) a
        (fun z => D' ⟨a, z⟩) (fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩)) f (x.cast a) y
  erw [hd, hb]
  rfl

theorem firstGridLambda_congr {r : Nat} {a a' : Arity}
    {D D' : ShapeValue → (carrierGrid (r + 2) 1).Code}
    {B B' : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code} {u : ShapeValue}
    {b b' : ShapeValue → FirstGridValue r → FirstGridValue r} (ha : a = a')
    (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z)
    (hb : ∀ x, x.code = a → ∀ y, y.code = D x → b x y = b' x y) :
    firstGridLambda r a D B u b = firstGridLambda r a' D' B' u b' := by
  subst a'
  have hd : (fun z : a.ShapeEl => D ⟨a, z⟩) = fun z => D' ⟨a, z⟩ :=
    funext (fun z => hD ⟨a, z⟩ rfl)
  have hc : (fun z : a.ShapeEl => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) =
      fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩) := funext (fun z => hB ⟨a, z⟩ rfl _)
  change (carrierGridQuantifiers (r + 1) 0).valueLambda (carrierGridArrows (r + 2) 1) a
    (fun z => D ⟨a, z⟩) (fun z => B ⟨a, z⟩ (u.apply ⟨a, z⟩)) (fun z => b ⟨a, z⟩) =
      (carrierGridQuantifiers (r + 1) 0).valueLambda (carrierGridArrows (r + 2) 1) a
        (fun z => D' ⟨a, z⟩) (fun z => B' ⟨a, z⟩ (u.apply ⟨a, z⟩)) (fun z => b' ⟨a, z⟩)
  erw [hd, hc]
  apply CarrierQuantifiers.valueLambda_congr
  intro z y hy
  exact hb ⟨a, z⟩ rfl y (hy.trans (hD ⟨a, z⟩ rfl).symm)

theorem firstGridProduct_congr {r : Nat} {a a' : Arity}
    {D D' : ShapeValue → (carrierGrid (r + 2) 1).Code}
    {B B' : ShapeValue → ShapeValue → (carrierGrid (r + 2) 1).Code} {u : ShapeValue}
    (ha : a = a') (hD : ∀ x, x.code = a → D x = D' x)
    (hB : ∀ x, x.code = a → ∀ z, B x z = B' x z) :
    firstGridProduct r a D B u = firstGridProduct r a' D' B' u := by
  subst a'
  unfold firstGridProduct
  congr 1
  · funext x; exact hD ⟨a, x⟩ rfl
  · funext x; exact hB ⟨a, x⟩ rfl _

theorem firstGridProduct_types_conv
    (hPi : BoundedTyping (r + 3) Γ (.pi A B) (.srt s))
    (hPi' : BoundedTyping (r + 3) Γ (.pi A' B') (.srt s'))
    (hc : Conv (.pi A B) (.pi A' B')) (hρ : ShapeContext (.type (r + 1)) Γ ρ) :
    arityAt (.type (r + 1)) A = arityAt (.type (r + 1)) A' ∧
    (∀ x, firstGridShape r Γ ρ A x = firstGridShape r Γ ρ A' x) ∧
    (∀ x, x.code = arityAt (.type (r + 1)) A → ∀ y,
      firstGridShape r (A :: Γ) (push x ρ) B y = firstGridShape r (A' :: Γ) (push x ρ) B' y) := by
  obtain ⟨ha, hd, hb⟩ := middleProduct_types_conv hPi hPi' hc rfl hρ
  exact ⟨ha, fun x => congrArg (firstGridCode r) (hd x),
    fun x hx y => congrArg (firstGridCode r) (hb x hx y)⟩

theorem firstGridShape_env (h : BoundedTyping (r + 3) Γ A (.srt s))
    (he : ∀ j B, Γ[j]? = some B → ρ j = ρ' j) :
    firstGridShape r Γ ρ A u = firstGridShape r Γ ρ' A u :=
  congrArg (firstGridCode r) (middleShape_env h rfl he)

theorem firstGridShape_context_conversion (hB : BoundedTyping (r + 3) (A :: Γ) B (.srt sB))
    (hA : BoundedTyping (r + 3) Γ A (.srt sA)) (hA' : BoundedTyping (r + 3) Γ A' (.srt sA'))
    (hsA : sortRank sA ≤ r + 3) (hc : Conv A A') :
    firstGridShape r (A' :: Γ) ρ B u = firstGridShape r (A :: Γ) ρ B u :=
  congrArg (firstGridCode r) (middleShape_context_conversion hB hA hA' hsA hc rfl)

end Submission.Helpers
