import Submission.SecondGridInference

namespace Submission.Helpers
open LeanEval.ProgramVerification.CoCStrongNormalization
set_option autoImplicit true

noncomputable def CarrierQuantifiers.twoPi (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code) : S.Code :=
  Q.code a (fun x => Q.pi P (D x) (d x) (c x))

noncomputable def CarrierQuantifiers.twoLambda (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code)
    (f : (x : I.El a) → (y : I.El (D x)) → S.El (d x y) → S.El (c x y)) :
    S.El (Q.twoPi P a D d c) :=
  (Q.functions a _).lambda (fun x => Q.piLambda P (D x) (d x) (c x) (f x))

noncomputable def CarrierQuantifiers.twoApply (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code)
    (f : S.El (Q.twoPi P a D d c)) (x : I.El a) (y : I.El (D x)) (z : S.El (d x y)) : S.El (c x y) :=
  Q.piApply P (D x) (d x) (c x) ((Q.functions a _).apply f x) y z

theorem CarrierQuantifiers.twoBeta (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code)
    (f : (x : I.El a) → (y : I.El (D x)) → S.El (d x y) → S.El (c x y))
    (x : I.El a) (y : I.El (D x)) (z : S.El (d x y)) :
    Q.twoApply P a D d c (Q.twoLambda P a D d c f) x y z = f x y z := by
  unfold twoApply twoLambda
  rw [(Q.functions a _).beta, Q.piBeta]

noncomputable def CarrierQuantifiers.twoValueApply (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code)
    (f : TowerValue S) (x : I.El a) (y : I.El (D x)) (z : TowerValue S) : TowerValue S :=
  ⟨c x y, Q.twoApply P a D d c (f.cast (Q.twoPi P a D d c)) x y (z.cast (d x y))⟩

noncomputable def CarrierQuantifiers.twoValueLambda (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code)
    (f : (x : I.El a) → I.El (D x) → TowerValue S → TowerValue S) : TowerValue S :=
  ⟨Q.twoPi P a D d c, Q.twoLambda P a D d c (fun x y z => (f x y ⟨d x y, z⟩).cast (c x y))⟩

theorem CarrierQuantifiers.twoValueBeta (Q : CarrierQuantifiers I S) (P : CarrierArrows S)
    (a : I.Code) (D : I.El a → I.Code) (d c : (x : I.El a) → I.El (D x) → S.Code)
    (f : (x : I.El a) → I.El (D x) → TowerValue S → TowerValue S)
    (x : I.El a) (y : I.El (D x)) (z : TowerValue S)
    (hz : z.code = d x y) (hf : (f x y z).code = c x y) :
    Q.twoValueApply P a D d c (Q.twoValueLambda P a D d c f) x y z = f x y z := by
  unfold twoValueApply twoValueLambda
  rw [TowerValue.cast_mk, Q.twoBeta, z.mk_cast hz]
  exact (f x y z).mk_cast hf

noncomputable def secondGridApply (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r) (g : SecondGridValue r)
    (x : ShapeValue) (y : UpperGridValue r) (z : SecondGridValue r) : SecondGridValue r :=
  (carrierGridQuantifiers (r + 2) 1).twoValueApply (carrierGridArrows (r + 3) 2) (.small a)
    (fun x => D ⟨a, x⟩) (fun x y => d ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)
    (fun x y => c ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩ (u.apply ⟨a, x⟩)
      (firstGridApply (r + 1) a D B u f ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩))
    g (x.cast a) (y.cast (D ⟨a, x.cast a⟩)) z

noncomputable def secondGridLambda (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r)
    (g : ShapeValue → UpperGridValue r → SecondGridValue r → SecondGridValue r) : SecondGridValue r :=
  (carrierGridQuantifiers (r + 2) 1).twoValueLambda (carrierGridArrows (r + 3) 2) (.small a)
    (fun x => D ⟨a, x⟩) (fun x y => d ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)
    (fun x y => c ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩ (u.apply ⟨a, x⟩)
      (firstGridApply (r + 1) a D B u f ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩))
    (fun x y => g ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)

theorem secondGridLambda_code (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r)
    (g : ShapeValue → UpperGridValue r → SecondGridValue r → SecondGridValue r) :
    (secondGridLambda r a D B d c u f g).code = upperGridProduct r a D B d c u f := rfl

theorem secondGridApply_code (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r) (g : SecondGridValue r)
    (x : ShapeValue) (y : UpperGridValue r) (z : SecondGridValue r)
    (hx : x.code = a) (hy : y.code = D x) :
    (secondGridApply r a D B d c u f g x y z).code = c x y (u.apply x) (firstGridApply (r + 1) a D B u f x y) := by
  change c ⟨a, x.cast a⟩ ⟨D ⟨a, x.cast a⟩, y.cast (D ⟨a, x.cast a⟩)⟩ _ _ = _
  rw [x.mk_cast hx, y.mk_cast hy]

theorem secondGridBeta (r : Nat) (a : Arity)
    (D : ShapeValue → (carrierGrid (r + 3) 1).Code)
    (B : ShapeValue → ShapeValue → (carrierGrid (r + 3) 1).Code)
    (d : ShapeValue → UpperGridValue r → UpperGridCode r)
    (c : ShapeValue → UpperGridValue r → ShapeValue → UpperGridValue r → UpperGridCode r)
    (u : ShapeValue) (f : UpperGridValue r)
    (g : ShapeValue → UpperGridValue r → SecondGridValue r → SecondGridValue r)
    (x : ShapeValue) (y : UpperGridValue r) (z : SecondGridValue r)
    (hx : x.code = a) (hy : y.code = D x) (hz : z.code = d x y)
    (hg : (g x y z).code = c x y (u.apply x) (firstGridApply (r + 1) a D B u f x y)) :
    secondGridApply r a D B d c u f (secondGridLambda r a D B d c u f g) x y z = g x y z := by
  cases x with
  | mk ax vx =>
    change ax = a at hx
    subst ax
    cases y with
    | mk ay vy =>
      change ay = D ⟨a, vx⟩ at hy
      subst ay
      unfold secondGridApply secondGridLambda
      dsimp only
      rw [ShapeValue.cast_mk a vx]
      rw [TowerValue.cast_mk (S := carrierGrid (r + 3) 1) (D ⟨a, vx⟩) vy]
      exact (carrierGridQuantifiers (r + 2) 1).twoValueBeta (carrierGridArrows (r + 3) 2) (.small a)
        (fun x => D ⟨a, x⟩) (fun x y => d ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩)
        (fun x y => c ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩ (u.apply ⟨a, x⟩)
          (firstGridApply (r + 1) a D B u f ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩))
        (fun x y => g ⟨a, x⟩ ⟨D ⟨a, x⟩, y⟩) vx vy z hz hg

/-- The second-coordinate abstraction inhabits the carrier of its source
product whenever the two preceding coordinates have their prescribed codes. -/
theorem secondGridLambda_typed {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A B : Tm} {u : ShapeValue} {f : UpperGridValue r}
    (hu : u.code = arityAt (.type (r + 2)) (.pi A B))
    (hf : f.code = firstGridShape (r + 1) Γ ρ (.pi A B) u)
    (g : ShapeValue → UpperGridValue r → SecondGridValue r → SecondGridValue r) :
    (secondGridLambda r (arityAt (.type (r + 2)) A)
      (fun x => firstGridShape (r + 1) Γ ρ A x)
      (fun x y => firstGridShape (r + 1) (A :: Γ) (push x ρ) B y)
      (secondGridShape r Γ ρ δ A)
      (fun x y => secondGridShape r (A :: Γ) (push x ρ) (push y δ) B) u f g).code =
      secondGridShape r Γ ρ δ (.pi A B) u f := (secondGridShape_pi hu hf).symm

/-- Application's second-coordinate carrier agrees with source substitution,
at the original bound `r + 4`. -/
theorem secondGridApply_typed {r : Nat} {Γ : List Tm} {ρ : Nat → ShapeValue}
    {δ : Nat → UpperGridValue r} {A B t a : Tm}
    (ht : BoundedTyping (r + 4) Γ t (.pi A B)) (ha : BoundedTyping (r + 4) Γ a A)
    (hρ : ShapeContext (.type (r + 2)) Γ ρ) (hδ : FirstGridContext (r + 1) Γ ρ δ)
    (g z : SecondGridValue r) :
    (secondGridApply r (arityAt (.type (r + 2)) A)
      (fun x => firstGridShape (r + 1) Γ ρ A x)
      (fun x y => firstGridShape (r + 1) (A :: Γ) (push x ρ) B y)
      (secondGridShape r Γ ρ δ A)
      (fun x y => secondGridShape r (A :: Γ) (push x ρ) (push y δ) B)
      (shapeEval (r + 4) (r + 2) Γ ρ t) (upperGridSemantics r Γ ρ δ t).1 g
      (shapeEval (r + 4) (r + 2) Γ ρ a) (upperGridSemantics r Γ ρ δ a).1 z).code =
      secondGridShape r Γ ρ δ (subst 0 a B) (shapeEval (r + 4) (r + 2) Γ ρ (.app t a))
        (upperGridSemantics r Γ ρ δ (.app t a)).1 := by
  rw [secondGridApply_code _ _ _ _ _ _ _ _ _ _ _ _ (shapeEval_typed_code ha rfl hρ)
    (upperGridSemantics_typed_code ha hρ)]
  obtain ⟨s, hPi⟩ := ht.pi_type
  obtain ⟨sA, hA, _⟩ := hPi.pi_domain
  obtain ⟨sB, hB, _⟩ := hPi.pi_codomain
  rw [secondGridShape_subst hB ha hA hρ hδ, upperGridSemantics_app ht ha hρ]
  rfl

end Submission.Helpers
