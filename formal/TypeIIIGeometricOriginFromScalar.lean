import TypeIIIFourierSourcePullbacks
import TypeIIIGenericCurvePullback
import TypeIIIRegularUnipotentRepresentation

/-!
# Geometric origin models from general tame scalar restriction

The scalar coefficients below lie in the parameter ring, before adjoining
the curve coordinate. General geometric tame restriction supplies the
same primitive origin representation after these scalar pullbacks.
The one Kloosterman model and AS lissity at zero remain published inputs.
No equality of full arithmetic Frobenius representations is asserted.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial

namespace PrimeGap182.TypeIII.GeometricOriginFromScalar

open StartingSourceMaps PublishedPhaseApplication FourierSourceMaps FourierSourcePullbacks
open GenericSourceSpecialization GenericCurvePullback CanonicalCurveInput
open RegularUnipotentRepresentation

universe u v w z a b c d e f
variable (K : Type u) [Field K]

def coefficientUnit (c : (ParameterRing K)ˣ) : (GenericRing K)ˣ :=
  Units.map (LaurentPolynomial.C : ParameterRing K →+* GenericRing K).toMonoidHom c

def constantCoefficient (r : (PhaseField K)ˣ) : (ParameterRing K)ˣ :=
  Units.map (LaurentPolynomial.C : PhaseField K →+* ParameterRing K).toMonoidHom r

def additiveCoefficient (s : (PhaseField K)ˣ) : (ParameterRing K)ˣ :=
  PhysicalTorusLaurent.variableUnit (PhaseField K) ^ 2 / constantCoefficient K s

/-- Every coefficient is independent of the curve coordinate. -/
def genericScalarHom (c : (ParameterRing K)ˣ) :
    MvPolynomial (Fin 1) K →ₐ[K] GenericRing K :=
  aeval (fun _ => (coefficientUnit K c : GenericRing K) * (curveUnit K : GenericRing K))

theorem coefficientUnit_constant (r : (PhaseField K)ˣ) :
    coefficientUnit K (constantCoefficient K r) = constantUnit K r := by
  apply Units.ext
  rfl

theorem coefficientUnit_additive (s : (PhaseField K)ˣ) :
    coefficientUnit K (additiveCoefficient K s) = parameterUnit K ^ 2 / constantUnit K s := by
  simp only [additiveCoefficient, coefficientUnit, map_div, map_pow]
  change parameterUnit K ^ 2 / coefficientUnit K (constantCoefficient K s) = _
  rw [coefficientUnit_constant]

theorem constant_scalarHom (r : (PhaseField K)ˣ) :
    genericScalarHom K (constantCoefficient K r) =
      ((projectionHom K).comp (FourierSourceMaps.scalarHom K r)).comp (localInputHom K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [genericScalarHom, localInputHom, AlgHom.comp_apply, aeval_X,
    coefficientUnit_constant]
  change _ = LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K)
    (LaurentPolynomial.eval₂ LaurentPolynomial.C _ (LaurentPolynomial.T 1))
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  change _ = LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K)
    (LaurentPolynomial.C (r : PhaseField K) * LaurentPolynomial.T 1)
  rw [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_one]
  rfl

theorem additive_scalarHom (s : (PhaseField K)ˣ) :
    additiveHom K s = genericScalarHom K (additiveCoefficient K s) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [additiveHom, genericScalarHom, aeval_X, coefficientUnit_additive]

def genericScalarMorphism (c : (ParameterRing K)ˣ) : genericScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (genericScalarHom K c).toRingHom)

theorem constant_scalarMorphism (r : (PhaseField K)ˣ) :
    genericScalarMorphism K (constantCoefficient K r) =
      (projectionMorphism K ≫ FourierSourceMaps.scalarMorphism K r) ≫ localInputMorphism K := by
  dsimp only [genericScalarMorphism, projectionMorphism, FourierSourceMaps.scalarMorphism,
    localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (constant_scalarHom K r))

theorem additive_scalarMorphism (s : (PhaseField K)ˣ) :
    additiveMorphism K s = genericScalarMorphism K (additiveCoefficient K s) :=
  congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (additive_scalarHom K s))

section Pullbacks

variable {Line : Type v} [Category.{a} Line]
  {Input : Type w} [Category.{b} Input]
  {GenericInput : Type z} [Category.{c} GenericInput]
  {Local : Type d} [Category.{e} Local]
  (P : GenericSourceSpecialization.PullbackComposition
    (Line := Line) (Input := Input) (GenericInput := GenericInput) K)
  (R : LocalPullbacks (L := Local) K P)

/-- Compare the old local scalar recipe with the actual parameter-unit
map, using only the existing general pullback composition laws. -/
def scalarSourceIso (r : (PhaseField K)ˣ) (A : Line) :
    (localSpecialization K P R).obj
        ((R.localEnd (FourierSourceMaps.scalarMorphism K r)).obj (localSource K P R A)) ≅
      (P.generic (genericScalarMorphism K (constantCoefficient K r))).obj A :=
  (R.localEndComposition (projectionMorphism K) (FourierSourceMaps.scalarMorphism K r)).app
      (localSource K P R A) ≪≫
    (R.localComposition (projectionMorphism K ≫ FourierSourceMaps.scalarMorphism K r)
      (localInputMorphism K)).app A ≪≫
    eqToIso (congrArg (fun g => (P.generic g).obj A) (constant_scalarMorphism K r).symm)

end Pullbacks

variable {Line : Type v} [Category.{a} Line]
  {GenericInput : Type w} [Category.{b} GenericInput]
  {G0 : Type c} [Group G0]
  (generic : (genericScheme K ⟶ affineLine K) → Line ⥤ GenericInput)
  (zero : GenericInput → FDRep ℂ G0) (LG : LineGeometry Line)
  (kl as : Line) (tame : G0 →* Multiplicative ℂ)

/-- General geometric origin restriction and the two published primitive
source inputs. The tame guard is essential: scalar pullback need not
preserve wild origin representations. `primitiveZero` is the full nearby
representation, not its invariant stalk or a chosen extension's value. -/
structure PullbackData where
  primitiveZero : Line → FDRep ℂ G0
  scalarZero : ∀ c A, LG.LisseOnUnits A → LG.TameZero A →
    Representation.Equiv (zero ((generic (genericScalarMorphism K c)).obj A)).ρ
      (primitiveZero A).ρ

/-- The old source interface adds the primitive models and lisse-origin laws.
The live application obtains these from the general published source rules. -/
structure Inputs extends PullbackData K generic zero LG where
  LisseAtZero : Line → Prop
  lisseZeroRankOne : ∀ A, LisseAtZero A → LG.LisseOnUnits A → LG.rank A = 1 →
    Representation.Equiv (primitiveZero A).ρ (Representation.trivial ℂ G0 ℂ)
  klModel : Representation.Equiv (primitiveZero kl).ρ (tameRepresentation tame)
  asLisseAtZero : LisseAtZero as

namespace Inputs

variable {K generic zero LG kl as tame} (S : Inputs K generic zero LG kl as tame)

/-- Every parameter-unit scalar model follows from the single source model. -/
def scalarModel (hkl : Kl3Properties LG kl) (c : (ParameterRing K)ˣ) :
    Representation.Equiv (zero ((generic (genericScalarMorphism K c)).obj kl)).ρ
      (tameRepresentation tame) :=
  (S.scalarZero c kl hkl.lisse hkl.tame).trans S.klModel

/-- The literal normalized additive map has trivial geometric origin
inertia because the same AS source extends lisse across zero with rank one. -/
def additiveModel (has : ASProperties LG as) (s : (PhaseField K)ˣ) :
    Representation.Equiv (zero ((generic (additiveMorphism K s)).obj as)).ρ
      (Representation.trivial ℂ G0 ℂ) := by
  rw [additive_scalarMorphism]
  exact (S.scalarZero (additiveCoefficient K s) as has.lisse has.tame).trans
    (S.lisseZeroRankOne as S.asLisseAtZero has.lisse has.rank)

end Inputs
end PrimeGap182.TypeIII.GeometricOriginFromScalar

#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.coefficientUnit_constant
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.coefficientUnit_additive
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.constant_scalarHom
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.additive_scalarHom
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.constant_scalarMorphism
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.additive_scalarMorphism
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.scalarSourceIso
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.Inputs.scalarModel
#print axioms PrimeGap182.TypeIII.GeometricOriginFromScalar.Inputs.additiveModel
