import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.FiniteType

/-!
# A proper projective-plane model and its torus chart

For every commutative base ring B, the ordinary total-degree grading on
B[X,Y,Z] has degree-zero ring canonically isomorphic to B.  The actual
Proj structure morphism, composed with this base identification, is
proper.  The homogeneous element XYZ defines the actual affine chart
D₊(XYZ), whose inclusion is an open immersion and whose structural map
is the displayed coefficient homomorphism.

All rings and scheme morphisms are constructed explicitly.  No
compactification, chart-ring isomorphism, or properness premise is used.
The zero ring is allowed.  The chart's identification with an iterated
Laurent-polynomial ring is a separate construction.  Over an integral
domain, the zero homogeneous prime proves that the chart is dense.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry
open scoped Classical

variable (B : Type u) [CommRing B]

/-- The actual three-variable homogeneous coordinate ring. -/
abbrev ProjectivePlanePolynomialRing := MvPolynomial (Fin 3) B

/-- The ordinary total-degree grading, with coefficients in degree zero. -/
abbrev projectivePlaneGrading : ℕ → Submodule B (ProjectivePlanePolynomialRing B) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) B

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual coefficient inclusion bijects B with the degree-zero ring. -/
theorem projectivePlaneDegreeZeroCoefficient_bijective :
    Function.Bijective (algebraMap B (projectivePlaneGrading B 0)) := by
  constructor
  · intro x y h
    apply MvPolynomial.C_injective (Fin 3) B
    exact congrArg (fun z : projectivePlaneGrading B 0 =>
      (z : ProjectivePlanePolynomialRing B)) h
  · intro g
    refine ⟨MvPolynomial.coeff 0 g.val, ?_⟩
    apply Subtype.ext
    change MvPolynomial.C (MvPolynomial.coeff 0 g.val) = g.val
    rw [← MvPolynomial.homogeneousComponent_zero]
    exact MvPolynomial.homogeneousComponent_eq_self g.property

/-- The actual degree-zero ring identification, oriented from B. -/
def projectivePlaneDegreeZeroEquiv : B ≃+* projectivePlaneGrading B 0 :=
  RingEquiv.ofBijective (algebraMap B (projectivePlaneGrading B 0))
    (projectivePlaneDegreeZeroCoefficient_bijective B)

@[simp] theorem projectivePlaneDegreeZeroEquiv_toRingHom :
    (projectivePlaneDegreeZeroEquiv B).toRingHom =
      algebraMap B (projectivePlaneGrading B 0) := rfl

@[simp] theorem projectivePlaneDegreeZeroEquiv_coe (b : B) :
    ((projectivePlaneDegreeZeroEquiv B b : projectivePlaneGrading B 0) :
      ProjectivePlanePolynomialRing B) = MvPolynomial.C b := rfl

/-- Finite generation holds over the actual degree-zero ring. -/
instance projectivePlanePolynomialRing_finiteTypeOverDegreeZero :
    Algebra.FiniteType (projectivePlaneGrading B 0) (ProjectivePlanePolynomialRing B) := by
  let : IsScalarTower B (projectivePlaneGrading B 0) (ProjectivePlanePolynomialRing B) :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := projectivePlaneGrading B 0)
      (A := ProjectivePlanePolynomialRing B) rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    B (projectivePlaneGrading B 0) (ProjectivePlanePolynomialRing B)

/-- The actual projective spectrum of the homogeneous coordinate ring. -/
abbrev projectivePlaneModel : Scheme.{u} := Proj (projectivePlaneGrading B)

/-- The actual structural morphism to the original base spectrum. -/
def projectivePlaneToBase : projectivePlaneModel B ⟶ Spec (.of B) :=
  Proj.toSpecZero (projectivePlaneGrading B) ≫
    Spec.map (CommRingCat.ofHom (projectivePlaneDegreeZeroEquiv B).toRingHom)

/-- The constructed projective plane is proper over B. -/
instance projectivePlaneToBase_isProper : IsProper (projectivePlaneToBase B) := by
  change IsProper (Proj.toSpecZero (projectivePlaneGrading B) ≫
    (Scheme.Spec.mapIso (projectivePlaneDegreeZeroEquiv B).toCommRingCatIso.op).hom)
  infer_instance

/-- The product whose nonvanishing defines the two-dimensional torus chart. -/
def projectivePlaneXYZ : ProjectivePlanePolynomialRing B :=
  MvPolynomial.X (0 : Fin 3) * MvPolynomial.X 1 * MvPolynomial.X 2

/-- XYZ is homogeneous of positive degree three, including over the zero ring. -/
theorem projectivePlaneXYZ_homogeneous :
    projectivePlaneXYZ B ∈ projectivePlaneGrading B 3 :=
  ((MvPolynomial.isHomogeneous_X B (0 : Fin 3)).mul
    (MvPolynomial.isHomogeneous_X B 1)).mul (MvPolynomial.isHomogeneous_X B 2)

/-- The literal homogeneous localization giving D₊(XYZ). -/
abbrev ProjectivePlaneTorusChart :=
  HomogeneousLocalization.Away (projectivePlaneGrading B) (projectivePlaneXYZ B)

/-- The actual coefficient map into the homogeneous localization. -/
def projectivePlaneChartCoefficient : B →+* ProjectivePlaneTorusChart B :=
  (HomogeneousLocalization.fromZeroRingHom (projectivePlaneGrading B)
    (Submonoid.powers (projectivePlaneXYZ B))).comp
      (algebraMap B (projectivePlaneGrading B 0))

@[simp] theorem projectivePlaneChartCoefficient_apply (b : B) :
    projectivePlaneChartCoefficient B b =
      HomogeneousLocalization.mk
        ⟨0, algebraMap B (projectivePlaneGrading B 0) b, 1, one_mem _⟩ := rfl

/-- In the ordinary localization, coefficients are still their original constants. -/
theorem projectivePlaneChartCoefficient_val (b : B) :
    (projectivePlaneChartCoefficient B b).val =
      algebraMap (ProjectivePlanePolynomialRing B)
        (Localization.Away (projectivePlaneXYZ B)) (MvPolynomial.C b) := by
  rw [projectivePlaneChartCoefficient_apply, HomogeneousLocalization.val_mk]
  exact Localization.mk_one_eq_algebraMap _

/-- The actual affine-chart inclusion into the projective spectrum. -/
def projectivePlaneTorusChartι :
    Spec (.of (ProjectivePlaneTorusChart B)) ⟶ projectivePlaneModel B :=
  Proj.awayι (projectivePlaneGrading B) (projectivePlaneXYZ B)
    (projectivePlaneXYZ_homogeneous B) (by decide : 0 < (3 : ℕ))

instance projectivePlaneTorusChartι_isOpenImmersion :
    IsOpenImmersion (projectivePlaneTorusChartι B) := by
  unfold projectivePlaneTorusChartι
  infer_instance

/-- The constructed chart has exactly the intended basic-open image. -/
theorem projectivePlaneTorusChartι_opensRange :
    (projectivePlaneTorusChartι B).opensRange =
      Proj.basicOpen (projectivePlaneGrading B) (projectivePlaneXYZ B) :=
  Proj.opensRange_awayι (projectivePlaneGrading B) (projectivePlaneXYZ B)
    (projectivePlaneXYZ_homogeneous B) (by decide : 0 < (3 : ℕ))

/-- The open chart and proper structural morphism factor its actual base map. -/
theorem projectivePlaneTorusChartι_toBase :
    projectivePlaneTorusChartι B ≫ projectivePlaneToBase B =
      Spec.map (CommRingCat.ofHom (projectivePlaneChartCoefficient B)) := by
  rw [projectivePlaneTorusChartι, projectivePlaneToBase, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The displayed chart element is nonzero over an integral domain. -/
theorem projectivePlaneXYZ_ne_zero [IsDomain B] : projectivePlaneXYZ B ≠ 0 :=
  mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero (0 : Fin 3))
    (MvPolynomial.X_ne_zero 1)) (MvPolynomial.X_ne_zero 2)

/-- The zero homogeneous prime is an actual point of the projective plane. -/
def projectivePlaneGenericPoint [IsDomain B] :
    ProjectiveSpectrum (projectivePlaneGrading B) where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem (projectivePlaneGrading B)
      (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X B (0 : Fin 3)))
    exact MvPolynomial.X_ne_zero (0 : Fin 3) hx

/-- The actual zero homogeneous prime is dense in the projective scheme. -/
theorem projectivePlaneGenericPoint_dense [IsDomain B] :
    Dense ({projectivePlaneGenericPoint B} : Set (projectivePlaneModel B)) := by
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure (projectivePlaneGrading B)
    (projectivePlaneGenericPoint B) x).mp
  change (⊥ : HomogeneousIdeal (projectivePlaneGrading B)) ≤ x.asHomogeneousIdeal
  exact bot_le

/-- Over an integral domain the actual open chart has dense image. -/
theorem projectivePlaneTorusChartι_denseRange [IsDomain B] :
    DenseRange (projectivePlaneTorusChartι B) := by
  change Dense ((projectivePlaneTorusChartι B).opensRange : Set (projectivePlaneModel B))
  rw [projectivePlaneTorusChartι_opensRange]
  apply Dense.mono (Set.singleton_subset_iff.mpr ?_) (projectivePlaneGenericPoint_dense B)
  change projectivePlaneXYZ B ∉ (⊥ : HomogeneousIdeal (projectivePlaneGrading B))
  exact projectivePlaneXYZ_ne_zero B

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.ProjectivePlanePolynomialRing
#print axioms PrimeGap182.TypeIII.projectivePlaneGrading
#print axioms PrimeGap182.TypeIII.projectivePlaneDegreeZeroCoefficient_bijective
#print axioms PrimeGap182.TypeIII.projectivePlaneDegreeZeroEquiv
#print axioms PrimeGap182.TypeIII.projectivePlaneDegreeZeroEquiv_toRingHom
#print axioms PrimeGap182.TypeIII.projectivePlaneDegreeZeroEquiv_coe
#print axioms PrimeGap182.TypeIII.projectivePlanePolynomialRing_finiteTypeOverDegreeZero
#print axioms PrimeGap182.TypeIII.projectivePlaneModel
#print axioms PrimeGap182.TypeIII.projectivePlaneToBase
#print axioms PrimeGap182.TypeIII.projectivePlaneToBase_isProper
#print axioms PrimeGap182.TypeIII.projectivePlaneXYZ
#print axioms PrimeGap182.TypeIII.projectivePlaneXYZ_homogeneous
#print axioms PrimeGap182.TypeIII.ProjectivePlaneTorusChart
#print axioms PrimeGap182.TypeIII.projectivePlaneChartCoefficient
#print axioms PrimeGap182.TypeIII.projectivePlaneChartCoefficient_apply
#print axioms PrimeGap182.TypeIII.projectivePlaneChartCoefficient_val
#print axioms PrimeGap182.TypeIII.projectivePlaneTorusChartι
#print axioms PrimeGap182.TypeIII.projectivePlaneTorusChartι_isOpenImmersion
#print axioms PrimeGap182.TypeIII.projectivePlaneTorusChartι_opensRange
#print axioms PrimeGap182.TypeIII.projectivePlaneTorusChartι_toBase
#print axioms PrimeGap182.TypeIII.projectivePlaneXYZ_ne_zero
#print axioms PrimeGap182.TypeIII.projectivePlaneGenericPoint
#print axioms PrimeGap182.TypeIII.projectivePlaneGenericPoint_dense
#print axioms PrimeGap182.TypeIII.projectivePlaneTorusChartι_denseRange
