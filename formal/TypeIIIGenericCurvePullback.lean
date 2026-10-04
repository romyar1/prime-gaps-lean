import TypeIIISourceCurveBaseChange

/-!
# The actual generic radial curve is a pullback

The parameter map factors through PhaseField(K)[T,T^-1]. The ring pushout
proved in SourceCurveBaseChange then identifies the existing generic
source specialization with the scheme-theoretic base change of the
original curve projection. Its exact maps, not only its points, agree.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.GenericCurvePullback

open StartingSourceMaps PublishedPhaseApplication PhysicalRadialMorphism
open GenericSourceSpecialization SourceCurveBaseChange

universe u
variable (K : Type u) [Field K]

abbrev ParameterRing := LaurentPolynomial (PhaseField K)
abbrev parameterScheme : Scheme := Spec (.of (ParameterRing K))

/-- The generic direction z is constant over the radial parameter T. -/
def parameterSectionHom : PhysicalTorusMorphism.TorusRing K →ₐ[K] ParameterRing K :=
  PhysicalTorusMorphism.evaluation (PhysicalTorusLaurent.variableUnit (PhaseField K))
    (Units.map (algebraMap (PhaseField K) (ParameterRing K)).toMonoidHom (directionUnit K))

theorem coefficient_parameterSection :
    (coefficientHom K).comp (parameterSectionHom K) = genericParameterHom K := by
  have hd : Units.map (coefficientHom K (A := ParameterRing K)).toRingHom.toMonoidHom
      (Units.map (algebraMap (PhaseField K) (ParameterRing K)).toMonoidHom (directionUnit K)) =
      constantUnit K (directionUnit K) := by
    apply Units.ext
    exact IsScalarTower.algebraMap_apply (PhaseField K) (ParameterRing K) (GenericRing K)
      (directionUnit K)
  have h := PhysicalTorusLaurent.evaluation_natural K (coefficientHom K (A := ParameterRing K))
    (PhysicalTorusLaurent.variableUnit (PhaseField K))
    (Units.map (algebraMap (PhaseField K) (ParameterRing K)).toMonoidHom (directionUnit K))
  exact h.trans (congrArg₂ (PhysicalTorusMorphism.evaluation (K := K) (A := GenericRing K)) rfl hd)

variable (alpha m n : Kˣ)

/-- This map lands in the parameter ring before adjoining the curve x. -/
def radialParameterHom : PhysicalTorusMorphism.TorusRing K →ₐ[K] ParameterRing K :=
  (parameterSectionHom K).comp (radialPhysicalEnd K alpha m n)

theorem coefficient_radialParameter :
    (coefficientHom K).comp (radialParameterHom K alpha m n) =
      (genericParameterHom K).comp (radialPhysicalEnd K alpha m n) := by
  rw [radialParameterHom, ← AlgHom.comp_assoc, coefficient_parameterSection]

/-- The universal base-change map is the existing specialization, with
the same curve coordinate and the same physical parameters. -/
theorem sourceMap_eq_specialization :
    sourceMap K (radialParameterHom K alpha m n) = specializationHom K alpha m n := by
  apply AlgHom.coe_ringHom_injective
  apply source_ringHom_ext_over_parameters K
  · exact (congrArg AlgHom.toRingHom (sourceMap_parameter K (radialParameterHom K alpha m n))).trans
      ((congrArg AlgHom.toRingHom (coefficient_radialParameter K alpha m n)).trans
        (congrArg AlgHom.toRingHom (specialization_parameterHom K alpha m n)).symm)
  · exact (sourceMap_coordinateUnit K (radialParameterHom K alpha m n) 0).trans
      (evaluation_coordinateUnit K (curveUnit K)
        (radialCoefficients K alpha m n).1 (radialCoefficients K alpha m n).2 0).symm

def curveProjection : sourceScheme K ⟶ PhysicalTorusMorphism.torusScheme K :=
  Spec.map (CommRingCat.ofHom (CanonicalCurveInput.parameterHom K).toRingHom)

def genericProjection : genericScheme K ⟶ parameterScheme K :=
  Spec.map (CommRingCat.ofHom (coefficientHom K (A := ParameterRing K)).toRingHom)

def radialParameterMorphism : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K :=
  Spec.map (CommRingCat.ofHom (radialParameterHom K alpha m n).toRingHom)

/-- The generic curve coordinate, independent of all five family parameters. -/
def curveCoordinateMorphism : genericScheme K ⟶ affineLine K :=
  genericInputMorphism K 1 1 1 0

/-- Fixing the curve coordinate retains the labelled zero and infinity
sections. A Cartesian square alone would also allow their interchange. -/
def PreservesCurveCoordinate (g : genericScheme K ⟶ sourceScheme K) : Prop :=
  g ≫ inputMorphism K 0 = curveCoordinateMorphism K

/-- Base change with the curve coordinate retained. This is the scope
needed when separately transporting zero and infinity ramification laws. -/
structure CoordinateBaseChange (g : genericScheme K ⟶ sourceScheme K)
    (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K) : Prop where
  cartesian : IsPullback g (genericProjection K) (curveProjection K) f
  coordinate : PreservesCurveCoordinate K g

theorem specialization_preservesCurveCoordinate :
    PreservesCurveCoordinate K (specializationMorphism K alpha m n) := by
  have h : genericInputHom K alpha m n 0 = genericInputHom K 1 1 1 0 := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [genericInputHom, MvPolynomial.aeval_X, Matrix.cons_val_zero]
  exact (specialization_inputMorphism K alpha m n 0).trans
    (congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (congrArg AlgHom.toRingHom h))

/-- The exact generic specialization square is Cartesian, without a
supplied geometric base-change or pullback hypothesis. -/
theorem genericSourceSquare_isPullback :
    IsPullback (specializationMorphism K alpha m n) (genericProjection K)
      (curveProjection K) (radialParameterMorphism K alpha m n) := by
  have h := sourceSquare_isPullback K (radialParameterHom K alpha m n)
  rw [sourceMap_eq_specialization K alpha m n] at h
  exact h

/-- The actual specialization discharges both the Cartesian and labelled
coordinate requirements of the general pullback/cohomology rules. -/
theorem genericSourceSquare_coordinateBaseChange :
    CoordinateBaseChange K (specializationMorphism K alpha m n)
      (radialParameterMorphism K alpha m n) where
  cartesian := genericSourceSquare_isPullback K alpha m n
  coordinate := specialization_preservesCurveCoordinate K alpha m n

def genericCurvePullbackIso : genericScheme K ≅
    pullback (curveProjection K) (radialParameterMorphism K alpha m n) :=
  (genericSourceSquare_isPullback K alpha m n).isoPullback

theorem genericCurvePullbackIso_fst :
    (genericCurvePullbackIso K alpha m n).hom ≫
      pullback.fst (curveProjection K) (radialParameterMorphism K alpha m n) =
      specializationMorphism K alpha m n := by
  exact (genericSourceSquare_isPullback K alpha m n).isoPullback_hom_fst

theorem genericCurvePullbackIso_snd :
    (genericCurvePullbackIso K alpha m n).hom ≫
      pullback.snd (curveProjection K) (radialParameterMorphism K alpha m n) =
      genericProjection K := by
  exact (genericSourceSquare_isPullback K alpha m n).isoPullback_hom_snd

end PrimeGap182.TypeIII.GenericCurvePullback

#print axioms PrimeGap182.TypeIII.GenericCurvePullback.coefficient_parameterSection
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.coefficient_radialParameter
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.sourceMap_eq_specialization
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.genericSourceSquare_isPullback
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.specialization_preservesCurveCoordinate
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.genericSourceSquare_coordinateBaseChange
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.genericCurvePullbackIso
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.genericCurvePullbackIso_fst
#print axioms PrimeGap182.TypeIII.GenericCurvePullback.genericCurvePullbackIso_snd
