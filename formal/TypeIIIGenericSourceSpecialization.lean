import TypeIIICanonicalCurveInput
import TypeIIIPhysicalRadialMorphism
import TypeIIICanonicalLocalCorrelation

/-!
# The three source pullbacks on the actual generic radial curve

The coefficient ring is PhaseField(K)[T,T^-1][x,x^-1]. The map to the
original curve sends its parameters to lambda=m/(n*z^3) and xi=T^2/A,
where z is the existing transcendental direction and A=alpha*z/m.
The resulting three maps to A1 are x, lambda*x, and xi*x. The parameter
projection commutes with the existing physical radial morphism.

All morphism identities are proved as ring-map identities. General
pullback composition then gives natural source-pullback isomorphisms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.GenericSourceSpecialization

open StartingSourceMaps PublishedPhaseApplication PhysicalRadialMorphism PublishedLocalConstruction

universe u v w z a b c
variable (K : Type u) [Field K]

abbrev GenericRing := LaurentPolynomial (LaurentPolynomial (PhaseField K))
abbrev genericScheme : Scheme := Spec (.of (GenericRing K))

def curveUnit : (GenericRing K)ˣ := PhysicalTorusLaurent.variableUnit _
def parameterUnit : (GenericRing K)ˣ :=
  Units.map (LaurentPolynomial.C : LaurentPolynomial (PhaseField K) →+* GenericRing K).toMonoidHom
    (PhysicalTorusLaurent.variableUnit (PhaseField K))
def constantUnit (x : (PhaseField K)ˣ) : (GenericRing K)ˣ :=
  Units.map (algebraMap (PhaseField K) (GenericRing K)) x
def directionUnit : (PhaseField K)ˣ := Units.mk0 (direction K) direction_ne_zero

variable (alpha m n : Kˣ)

def lambdaUnit : (PhaseField K)ˣ :=
  Units.map (algebraMap K (PhaseField K)) (m / n) / directionUnit K ^ 3
def scaleUnit : (PhaseField K)ˣ :=
  Units.map (algebraMap K (PhaseField K)) (alpha / m) * directionUnit K

theorem lambdaUnit_value : (lambdaUnit K m n : PhaseField K) = angularRatio (m : K) (n : K) := by
  simp [lambdaUnit, directionUnit, angularRatio]

theorem scaleUnit_value : (scaleUnit K alpha m : PhaseField K) = radialScale (alpha : K) (m : K) := by
  simp [scaleUnit, directionUnit, radialScale, div_eq_mul_inv, mul_assoc, mul_comm]

theorem constantUnit_map (x : Kˣ) :
    constantUnit K (Units.map (algebraMap K (PhaseField K)) x) =
      Units.map (algebraMap K (GenericRing K)) x := by
  apply Units.ext
  exact IsScalarTower.algebraMap_apply K (PhaseField K) (GenericRing K) x

def radialCoefficients : (GenericRing K)ˣ × (GenericRing K)ˣ :=
  radialPhysicalParameters K alpha m n (parameterUnit K) (constantUnit K (directionUnit K))

/-- The first specialized parameter is the very same generic angular ratio. -/
theorem radialCoefficients_lambda :
    (radialCoefficients K alpha m n).1 = constantUnit K (lambdaUnit K m n) := by
  change Units.map (algebraMap K (GenericRing K)) (m / n) /
    constantUnit K (directionUnit K) ^ 3 = _
  simp only [lambdaUnit, constantUnit, map_div, map_pow]
  have hm := constantUnit_map K m
  have hn := constantUnit_map K n
  dsimp only [constantUnit] at hm hn
  rw [hm, hn]

/-- The second parameter has exactly the T²/A normalization of the local
Fourier theorem, as an identity of units of the Laurent ring. -/
theorem radialCoefficients_xi :
    (radialCoefficients K alpha m n).2 =
      parameterUnit K ^ 2 / constantUnit K (scaleUnit K alpha m) := by
  have h : constantUnit K (scaleUnit K alpha m) =
      Units.map (algebraMap K (GenericRing K)) (alpha / m) * constantUnit K (directionUnit K) := by
    unfold scaleUnit constantUnit
    rw [map_mul]
    exact congrArg (fun u : (GenericRing K)ˣ =>
      u * Units.map (algebraMap (PhaseField K) (GenericRing K)) (directionUnit K))
      (constantUnit_map K (alpha / m))
  rw [h]
  have unit_identity {U : Type u} [CommGroup U] (a b t z : U) :
      (b / a) * t ^ 2 / z = t ^ 2 / ((a / b) * z) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ac_rfl
  simp only [radialCoefficients, radialPhysicalParameters, map_div]
  exact unit_identity _ _ _ _

def specializationHom : SourceRing K →ₐ[K] GenericRing K :=
  StartingSourceMaps.evaluation (curveUnit K)
    (radialCoefficients K alpha m n).1 (radialCoefficients K alpha m n).2

def specializationMorphism : genericScheme K ⟶ sourceScheme K :=
  Spec.map (CommRingCat.ofHom (specializationHom K alpha m n).toRingHom)

def genericInputHom (i : Fin 3) : MvPolynomial (Fin 1) K →ₐ[K] GenericRing K :=
  aeval (fun _ => ![(curveUnit K : GenericRing K),
    ((radialCoefficients K alpha m n).1 : GenericRing K) * curveUnit K,
    ((radialCoefficients K alpha m n).2 : GenericRing K) * curveUnit K] i)

def genericInputMorphism (i : Fin 3) : genericScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (genericInputHom K alpha m n i).toRingHom)

/-- All three original source maps specialize to their literal kernel
coordinates, before any sheaf or cohomology construction is used. -/
theorem specialization_inputHom (i : Fin 3) :
    (specializationHom K alpha m n).comp (inputHom K i) = genericInputHom K alpha m n i := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  simp only [AlgHom.comp_apply, genericInputHom, aeval_X]
  exact inputHom_evaluation K (curveUnit K)
    (radialCoefficients K alpha m n).1 (radialCoefficients K alpha m n).2 i

theorem specialization_inputMorphism (i : Fin 3) :
    specializationMorphism K alpha m n ≫ inputMorphism K i = genericInputMorphism K alpha m n i := by
  have h := congrArg AlgHom.toRingHom (specialization_inputHom K alpha m n i)
  dsimp only [specializationMorphism, inputMorphism, genericInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h

theorem evaluation_coordinateUnit {R : Type u} [CommRing R] [Algebra K R]
    (x l t : Rˣ) (i : Fin 3) :
    Units.map (StartingSourceMaps.evaluation (K := K) x l t).toRingHom (coordinateUnit K i) =
      ![x, l, t] i := by
  apply Units.ext
  fin_cases i
  · exact evaluation_coordinate x l t 0
  · exact evaluation_coordinate x l t 2
  · exact evaluation_coordinate x l t 4

def genericParameterHom : PhysicalTorusMorphism.TorusRing K →ₐ[K] GenericRing K :=
  PhysicalTorusMorphism.evaluation (parameterUnit K) (constantUnit K (directionUnit K))

/-- The curve projection commutes with the same physical radial map
already used for the global entry. This does not yet assert a pullback. -/
theorem specialization_parameterHom :
    (specializationHom K alpha m n).comp (CanonicalCurveInput.parameterHom K) =
      (genericParameterHom K).comp (radialPhysicalEnd K alpha m n) := by
  rw [genericParameterHom, evaluation_comp_radialPhysicalEnd K alpha m n
    (parameterUnit K) (constantUnit K (directionUnit K))]
  rw [CanonicalCurveInput.parameterHom, PhysicalTorusLaurent.evaluation_natural K
    (specializationHom K alpha m n) (coordinateUnit K 1) (coordinateUnit K 2)]
  refine congrArg₂ (PhysicalTorusMorphism.evaluation (K := K) (A := GenericRing K)) ?_ ?_
  · exact evaluation_coordinateUnit K (curveUnit K)
      (radialCoefficients K alpha m n).1 (radialCoefficients K alpha m n).2 1
  · exact evaluation_coordinateUnit K (curveUnit K)
      (radialCoefficients K alpha m n).1 (radialCoefficients K alpha m n).2 2

section Pullbacks

variable {Line : Type v} [Category.{a} Line]
  {Input : Type w} [Category.{b} Input] {GenericInput : Type z} [Category.{c} GenericInput]

/-- General composition of sheaf pullback on the actual schemes, for
every source map and every curve base change. -/
structure PullbackComposition where
  original : (sourceScheme K ⟶ affineLine K) → Line ⥤ Input
  generic : (genericScheme K ⟶ affineLine K) → Line ⥤ GenericInput
  along : (genericScheme K ⟶ sourceScheme K) → Input ⥤ GenericInput
  composition : ∀ g f, original f ⋙ along g ≅ generic (g ≫ f)

/-- Natural source isomorphisms from the three proved scheme-map
identities. They apply to the original Kl3 and AS objects and their maps. -/
def sourcePullbackIso (P : PullbackComposition (Line := Line) (Input := Input)
    (GenericInput := GenericInput) K) (i : Fin 3) :
    P.original (inputMorphism K i) ⋙ P.along (specializationMorphism K alpha m n) ≅
      P.generic (genericInputMorphism K alpha m n i) :=
  P.composition (specializationMorphism K alpha m n) (inputMorphism K i) ≪≫
    eqToIso (congrArg P.generic (specialization_inputMorphism K alpha m n i))

end Pullbacks
end PrimeGap182.TypeIII.GenericSourceSpecialization

#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.lambdaUnit_value
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.scaleUnit_value
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.constantUnit_map
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.radialCoefficients_lambda
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.radialCoefficients_xi
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.specialization_inputHom
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.specialization_inputMorphism
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.evaluation_coordinateUnit
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.specialization_parameterHom
#print axioms PrimeGap182.TypeIII.GenericSourceSpecialization.sourcePullbackIso
