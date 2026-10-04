import TypeIIIFourierSourceMaps

/-!
# Linear covering characters from the same primitive AS source

Construct all coefficient maps x ↦ a*x to the original affine line,
including coefficient zero. Pull back the same AS source used by the
finite-sum and Fourier-kernel construction and restrict it to covering
inertia. LinearASData is thus derived rather than independently supplied.
Its published character, rank and deck laws remain general inputs.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial

namespace PrimeGap182.TypeIII.PrimitiveLinearAS

open StartingSourceMaps PublishedPhaseApplication PublishedMackey FourierSourceMaps

universe u v w a b c d
variable (K : Type u) [Field K]

/-- The affine-line target permits zero coefficients without a zero
scalar endomorphism of Gm. -/
def linearHom (a : PhaseField K) : MvPolynomial (Fin 1) K →ₐ[K] LocalRing K :=
  aeval (fun _ => LaurentPolynomial.C a * LaurentPolynomial.T 1)

theorem linearHom_one : linearHom K 1 = localInputHom K := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [linearHom, localInputHom, aeval_X, map_one, one_mul]
  rfl

theorem linearHom_scalar (a : (PhaseField K)ˣ) :
    linearHom K a = (scalarHom K a).comp (localInputHom K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [linearHom, localInputHom, AlgHom.comp_apply, aeval_X]
  change LaurentPolynomial.C (a : PhaseField K) * LaurentPolynomial.T 1 =
    LaurentPolynomial.eval₂ LaurentPolynomial.C _ (LaurentPolynomial.T 1)
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

/-- Deck or scalar substitution multiplies the original coefficient. -/
theorem linearHom_scalar_comp (a : PhaseField K) (r : (PhaseField K)ˣ) :
    (scalarHom K r).comp (linearHom K a) = linearHom K (a * (r : PhaseField K)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, linearHom, aeval_X]
  change LaurentPolynomial.eval₂ LaurentPolynomial.C _
    (LaurentPolynomial.C a * LaurentPolynomial.T 1) = _
  rw [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_one]
  change LaurentPolynomial.C a * (LaurentPolynomial.C (r : PhaseField K) * LaurentPolynomial.T 1) =
    LaurentPolynomial.C (a * (r : PhaseField K)) * LaurentPolynomial.T 1
  rw [map_mul, mul_assoc]

def linearMorphism (a : PhaseField K) : localScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (linearHom K a).toRingHom)

/-- For units this is the exact scalar morphism already used elsewhere. -/
theorem linearMorphism_scalar (a : (PhaseField K)ˣ) :
    linearMorphism K a = scalarMorphism K a ≫ localInputMorphism K := by
  dsimp only [linearMorphism, scalarMorphism, localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (linearHom_scalar K a))

variable {Line : Type v} [Category.{a} Line]
  {Local : Type w} [Category.{b} Local]
  {E : Type c} [Field E] {Cover : Type d} [Group Cover]

/-- One source object and the actual inverse-image/inertia functors
determine every linear Artin–Schreier covering representation. -/
def data (restriction : (localScheme K ⟶ affineLine K) → Line ⥤ Local)
    (inertia : Local ⥤ FDRep E Cover) (as : Line) :
    LinearASData (PhaseField K) E Cover where
  phase a := inertia.obj ((restriction (linearMorphism K a)).obj as)

end PrimeGap182.TypeIII.PrimitiveLinearAS

#print axioms PrimeGap182.TypeIII.PrimitiveLinearAS.linearHom_one
#print axioms PrimeGap182.TypeIII.PrimitiveLinearAS.linearHom_scalar
#print axioms PrimeGap182.TypeIII.PrimitiveLinearAS.linearHom_scalar_comp
#print axioms PrimeGap182.TypeIII.PrimitiveLinearAS.linearMorphism_scalar
#print axioms PrimeGap182.TypeIII.PrimitiveLinearAS.data
