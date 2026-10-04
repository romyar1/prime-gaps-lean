import TypeIIIArithmeticDualFromEvaluation

/-! The dual comparison is obtained from the SAME evaluation morphism,
not a chosen equivalence followed by an evaluation equation. Bijectivity
of this computed map on finite-lisse objects remains the individual
general internal-Hom/stalk theorem. No Frobenius or contragredient law
is a premise. This pure application does not supply an adic realization. -/
noncomputable section
open CategoryTheory Opposite
open scoped MonoidalCategory TensorProduct
namespace PrimeGap182.TypeIII.ArithmeticDualFromCanonicalEvaluation
open PublishedPhaseApplication
universe u v w
variable {Input : Type u} [Category.{v} Input] [MonoidalCategory Input]
  {G : Type w} [Group G] (T : Input ⥤ FDRep ℂ G) [T.Monoidal]
  (dual : Inputᵒᵖ ⥤ Input) (ev : ∀ A, dual.obj (op A) ⊗ A ⟶ 𝟙_ Input)

/-- The actual monoidal image of the source evaluation. -/
def evaluationHom (A : Input) : T.obj (dual.obj (op A)) ⊗ T.obj A ⟶ 𝟙_ (FDRep ℂ G) :=
  Functor.LaxMonoidal.μ T (dual.obj (op A)) A ≫ T.map (ev A) ≫ (Functor.Monoidal.εIso T).inv

/-- Currying this actual equivariant morphism determines the dual map. -/
def canonicalDualMap (A : Input) : (T.obj (dual.obj (op A))).V →ₗ[ℂ]
    Module.Dual ℂ (T.obj A).V :=
  TensorProduct.curry (evaluationHom T dual ev A).hom.hom.hom

/-- Inertia invariance follows from equivariance of the actual evaluation. -/
theorem evaluation_invariant (A : Input) (g : G)
    (x : (T.obj (dual.obj (op A))).V) (y : (T.obj A).V) :
    canonicalDualMap T dual ev A ((T.obj (dual.obj (op A))).ρ g x)
      ((T.obj A).ρ g y) = canonicalDualMap T dual ev A x y := by
  have h := congrArg (fun f => f.hom.hom (x ⊗ₜ[ℂ] y)) ((evaluationHom T dual ev A).comm g)
  change canonicalDualMap T dual ev A ((T.obj (dual.obj (op A))).ρ g x)
    ((T.obj A).ρ g y) = canonicalDualMap T dual ev A x y at h
  exact h

theorem canonicalDualMap_intertwines (A : Input) (g : G)
    (x : (T.obj (dual.obj (op A))).V) :
    canonicalDualMap T dual ev A ((T.obj (dual.obj (op A))).ρ g x) =
      (dualRepresentation (T.obj A)).ρ g (canonicalDualMap T dual ev A x) := by
  apply LinearMap.ext
  intro y
  change canonicalDualMap T dual ev A ((T.obj (dual.obj (op A))).ρ g x) y =
    canonicalDualMap T dual ev A x ((T.obj A).ρ g⁻¹ y)
  have h := evaluation_invariant T dual ev A g x ((T.obj A).ρ g⁻¹ y)
  have hi : (T.obj A).ρ g ((T.obj A).ρ g⁻¹ y) = y := by
    change ((T.obj A).ρ g * (T.obj A).ρ g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hi] at h
  exact h

variable (Good : Input → Prop)
  (bijective : ∀ A, Good A → Function.Bijective (canonicalDualMap T dual ev A))

/-- The computed map becomes the literal representation dual comparison. -/
def dualComparison (A : Input) (hA : Good A) : Representation.Equiv
    (T.obj (dual.obj (op A))).ρ (dualRepresentation (T.obj A)).ρ where
  toLinearEquiv := LinearEquiv.ofBijective (canonicalDualMap T dual ev A) (bijective A hA)
  isIntertwining' g := by
    apply LinearMap.ext
    exact canonicalDualMap_intertwines T dual ev A g

section Along
universe a b
variable {Local : Type a} [Category.{b} Local] [MonoidalCategory Local]
  (along : Input ⥤ Local) [along.Monoidal]
  (J : Local ⥤ FDRep ℂ G) [J.Monoidal]
  (localBijective : ∀ A, Good A → Function.Bijective (canonicalDualMap (along ⋙ J) dual ev A))

/-- The original arithmetic evaluation comparison is now definitional. -/
theorem arithmeticComparison : ArithmeticDualFromEvaluation.Comparison along dual ev Good
    (fun A hA => (dualComparison (along ⋙ J) dual ev Good localBijective A hA).toLinearEquiv) where
  evaluation _ _ _ _ := rfl
end Along
end PrimeGap182.TypeIII.ArithmeticDualFromCanonicalEvaluation
