import TypeIIIPowerCoverScalarCoordinates
import TypeIIIExactInverseImagesToDerived

/-!
# Scalar automorphisms and the actual Cartesian power-cover square

The original scalar Laurent homomorphism has inverse given by the inverse
unit. Its actual Spec map is consequently an isomorphism. The same literal
power/scalar square is Cartesian by the standard isomorphism-square lemma,
for every natural exponent. SAME-U composition then transports actual
ordinary inverse images around this square. No cover pushforward, induction,
local ramification or Frobenius comparison is assumed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.PowerScalarCartesianFromUnitAutomorphism
open ArithmeticSourceMaps SourceCurveBaseChange PowerCoverScalarCoordinates
open ExactInverseImagesToDerived

variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- The original scalar substitution multiplies coefficient units. -/
theorem scalarHom_comp (r s : Eˣ) :
    (scalarHom K E r).comp (scalarHom K E s) = scalarHom K E (r * s) := by
  apply AlgHom.coe_ringHom_injective
  apply laurent_ringHom_ext
  · apply RingHom.ext
    intro a
    change scalarHom K E r (scalarHom K E s (LaurentPolynomial.C a)) =
      scalarHom K E (r * s) (LaurentPolynomial.C a)
    rw [scalarHom_C, scalarHom_C, scalarHom_C]
  · apply Units.ext
    change scalarHom K E r (scalarHom K E s
      (PhysicalTorusLaurent.variableUnit E : FiberRing E)) =
      scalarHom K E (r * s) (PhysicalTorusLaurent.variableUnit E : FiberRing E)
    rw [scalarHom_variable, map_mul, scalarHom_C, scalarHom_variable, scalarHom_variable]
    change LaurentPolynomial.C (s : E) *
      (LaurentPolynomial.C (r : E) * (PhysicalTorusLaurent.variableUnit E : FiberRing E)) =
      LaurentPolynomial.C ((r : E) * (s : E)) *
        (PhysicalTorusLaurent.variableUnit E : FiberRing E)
    rw [map_mul, ← mul_assoc, mul_comm (LaurentPolynomial.C (s : E))]

/-- The coefficient-one native scalar map is literally the identity. -/
theorem scalarHom_one : scalarHom K E 1 = AlgHom.id K (FiberRing E) := by
  apply AlgHom.coe_ringHom_injective
  apply laurent_ringHom_ext
  · apply RingHom.ext
    intro a
    exact scalarHom_C K E 1 a
  · apply Units.ext
    change scalarHom K E 1 (PhysicalTorusLaurent.variableUnit E : FiberRing E) =
      (PhysicalTorusLaurent.variableUnit E : FiberRing E)
    rw [scalarHom_variable]
    simp only [Units.val_one, map_one, one_mul]

/-- The inverse scalar homomorphism is the original homomorphism at the inverse unit. -/
theorem scalarHom_inverse (r : Eˣ) :
    (scalarHom K E r).comp (scalarHom K E r⁻¹) = AlgHom.id K (FiberRing E) := by
  rw [scalarHom_comp, mul_inv_cancel, scalarHom_one]

/-- The original native scalar Spec map has its literal inverse map. -/
theorem scalarMorphism_inverse (r : Eˣ) :
    scalarMorphism K E r ≫ scalarMorphism K E r⁻¹ = 𝟙 (fiberScheme E) := by
  dsimp only [scalarMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom
    (((scalarHom K E r).comp (scalarHom K E r⁻¹)).toRingHom)) = _
  rw [scalarHom_inverse]
  exact Spec.map_id _

/-- The scalar isomorphism is constructed from the actual original maps. -/
def nativeScalarIso (r : Eˣ) : fiberScheme E ≅ fiberScheme E where
  hom := scalarMorphism K E r
  inv := scalarMorphism K E r⁻¹
  hom_inv_id := scalarMorphism_inverse K E r
  inv_hom_id := by simpa only [inv_inv] using scalarMorphism_inverse K E r⁻¹

instance nativeScalarMorphism_isIso (r : Eˣ) : IsIso (scalarMorphism K E r) :=
  (nativeScalarIso K E r).isIso_hom

/-- The same actual scalar/power square is Cartesian, including exponent zero. -/
theorem powerScalar_isPullback (e : ℕ) (r : Eˣ) :
    IsPullback (scalarMorphism K E r) (powerMorphism K E e)
      (powerMorphism K E e) (scalarMorphism K E (r ^ e)) :=
  IsPullback.of_horiz_isIso ⟨scalarMorphism_powerMorphism K E e r⟩

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)

/-- Ordinary inverse images around the actual square agree by SAME-U composition. -/
def ordinaryPowerScalarIso (e : ℕ) (r : Eˣ) :
    U.pull (powerMorphism K E e) ⋙ U.pull (scalarMorphism K E r) ≅
      U.pull (scalarMorphism K E (r ^ e)) ⋙ U.pull (powerMorphism K E e) :=
  U.composition (scalarMorphism K E r) (powerMorphism K E e) ≪≫
    eqToIso (congrArg (fun f => U.pull f) (scalarMorphism_powerMorphism K E e r)) ≪≫
      (U.composition (powerMorphism K E e) (scalarMorphism K E (r ^ e))).symm

end PrimeGap182.TypeIII.PowerScalarCartesianFromUnitAutomorphism
