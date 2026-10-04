import TypeIIIArithmeticSourceMaps
import TypeIIISourceCurveBaseChange

/-!
# The actual power-cover and scalar coordinate square

For every field extension and every natural exponent, the Laurent power
map t ↦ t^e satisfies scalar(r) ≫ [e] = [e] ≫ scalar(r^e).
These are actual algebra-homomorphism and Spec identities on the original
Gm scheme. There is no sheaf pushforward, inertia induction, cover-descent,
Frobenius or published local-model hypothesis in this coordinate leaf.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PrimeGap182.TypeIII.PowerCoverScalarCoordinates
open ArithmeticSourceMaps SourceCurveBaseChange

variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- The actual power endomorphism of the original Laurent coordinate ring. -/
def powerHom (e : ℕ) : FiberRing E →ₐ[K] FiberRing E where
  toRingHom := LaurentPolynomial.eval₂ LaurentPolynomial.C
    (PhysicalTorusLaurent.variableUnit E ^ e)
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _
      (LaurentPolynomial.C (algebraMap K E c)) = _
    rw [LaurentPolynomial.eval₂_C]
    rfl

/-- The corresponding actual power morphism of Gm, also at exponent zero. -/
def powerMorphism (e : ℕ) : fiberScheme E ⟶ fiberScheme E :=
  Spec.map (CommRingCat.ofHom (powerHom K E e).toRingHom)

theorem powerHom_C (e : ℕ) (a : E) :
    powerHom K E e (LaurentPolynomial.C a) = LaurentPolynomial.C a :=
  LaurentPolynomial.eval₂_C _ _ a

theorem scalarHom_C (r : Eˣ) (a : E) :
    scalarHom K E r (LaurentPolynomial.C a) = LaurentPolynomial.C a :=
  LaurentPolynomial.eval₂_C _ _ a

theorem powerHom_variable (e : ℕ) :
    powerHom K E e (PhysicalTorusLaurent.variableUnit E : FiberRing E) =
      ((PhysicalTorusLaurent.variableUnit E ^ e : (FiberRing E)ˣ) : FiberRing E) := by
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

theorem scalarHom_variable (r : Eˣ) :
    scalarHom K E r (PhysicalTorusLaurent.variableUnit E : FiberRing E) =
      LaurentPolynomial.C (r : E) * (PhysicalTorusLaurent.variableUnit E : FiberRing E) := by
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

/-- The coefficient is raised to the same exponent in the literal ring square. -/
theorem power_scalar_comp (e : ℕ) (r : Eˣ) :
    (scalarHom K E r).comp (powerHom K E e) =
      (powerHom K E e).comp (scalarHom K E (r ^ e)) := by
  apply AlgHom.coe_ringHom_injective
  apply laurent_ringHom_ext
  · apply RingHom.ext
    intro a
    change scalarHom K E r (powerHom K E e (LaurentPolynomial.C a)) =
      powerHom K E e (scalarHom K E (r ^ e) (LaurentPolynomial.C a))
    rw [powerHom_C, scalarHom_C, scalarHom_C, powerHom_C]
  · apply Units.ext
    change scalarHom K E r (powerHom K E e (PhysicalTorusLaurent.variableUnit E : FiberRing E)) =
      powerHom K E e (scalarHom K E (r ^ e) (PhysicalTorusLaurent.variableUnit E : FiberRing E))
    rw [powerHom_variable, scalarHom_variable]
    change scalarHom K E r ((PhysicalTorusLaurent.variableUnit E : FiberRing E) ^ e) =
      powerHom K E e (LaurentPolynomial.C ((r : E) ^ e) *
        (PhysicalTorusLaurent.variableUnit E : FiberRing E))
    rw [map_pow, scalarHom_variable, map_mul, powerHom_C, powerHom_variable]
    change (LaurentPolynomial.C (r : E) *
      (PhysicalTorusLaurent.variableUnit E : FiberRing E)) ^ e =
      LaurentPolynomial.C ((r : E) ^ e) *
        (PhysicalTorusLaurent.variableUnit E : FiberRing E) ^ e
    rw [mul_pow, map_pow]

/-- The exact source/target map square needed for scalar base change of a power cover. -/
theorem scalarMorphism_powerMorphism (e : ℕ) (r : Eˣ) :
    scalarMorphism K E r ≫ powerMorphism K E e =
      powerMorphism K E e ≫ scalarMorphism K E (r ^ e) := by
  dsimp only [scalarMorphism, powerMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (power_scalar_comp K E e r))

/-- The cubic case uses the same actual square, with no additional assumption. -/
theorem scalarMorphism_cubicCover (r : Eˣ) :
    scalarMorphism K E r ≫ powerMorphism K E 3 =
      powerMorphism K E 3 ≫ scalarMorphism K E (r ^ 3) :=
  scalarMorphism_powerMorphism K E 3 r

end PrimeGap182.TypeIII.PowerCoverScalarCoordinates
