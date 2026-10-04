import TypeIIIActualTraitGroupFromCoefficientRingEquiv02
import Mathlib.RingTheory.Finiteness.Basic

/-! Common-base algebraic closure and formal-trait transport for algebraic
coefficient extensions. No arbitrary transcendental algebraically closed base
change, native local-group identification or continuous sheaf model is asserted.
This importing source is staged: compile only after independent prerequisite
admission of the genuine coefficient-equivalence transport leaf. -/
noncomputable section
namespace PrimeGap182.TypeIII.AlgebraicConstantFieldCommonTraitTransport
open NativeWildRecognitionFromFixedGeometricTraits
open TraitClosureLiftDifferenceFromEverySeries

section Algebraic
variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- Existing Mathlib coefficient algebra on the actual closure of E. -/
abbrev closureConstantsAlgebra : Algebra K (AlgebraicClosure E) := inferInstance

/-- Its literal constant-field tower, without replacing the scalar instances. -/
theorem closureConstantsAlgebra_algebraMap (k : K) :
    algebraMap K (AlgebraicClosure E) k =
      algebraMap E (AlgebraicClosure E) (algebraMap K E k) :=
  IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) k

variable [Algebra.IsAlgebraic K E]

/-- Both closures are algebraic closures of the SAME K, using the actual
coefficient tower. No non-surjective base map is treated as a RingEquiv. -/
def coefficientAlgEquiv : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure E := by
  letI : IsAlgClosure K (AlgebraicClosure E) :=
    IsAlgClosure.ofAlgebraic K E (AlgebraicClosure E)
  exact IsAlgClosure.equiv K (AlgebraicClosure K) (AlgebraicClosure E)

/-- The SAME chosen coefficient equivalence with its base algebra forgotten. -/
def coefficientRingEquiv : AlgebraicClosure K ≃+* AlgebraicClosure E :=
  (coefficientAlgEquiv K E).toRingEquiv

/-- The chosen coefficient equivalence preserves every K constant. -/
theorem coefficientRingEquiv_overBase (k : K) :
    coefficientRingEquiv K E (algebraMap K (AlgebraicClosure K) k) =
      algebraMap E (AlgebraicClosure E) (algebraMap K E k) := by
  exact ((coefficientAlgEquiv K E).commutes k).trans
    (closureConstantsAlgebra_algebraMap K E k)

def coefficientSeriesEquiv :
    PowerSeries (AlgebraicClosure K) ≃+* PowerSeries (AlgebraicClosure E) :=
  ActualTraitGroupFromCoefficientRingEquiv.seriesEquiv (coefficientRingEquiv K E)

@[simp] theorem coefficientSeriesEquiv_coeff
    (f : PowerSeries (AlgebraicClosure K)) (j : ℕ) :
    (coefficientSeriesEquiv K E f).coeff j = coefficientRingEquiv K E (f.coeff j) :=
  ActualTraitGroupFromCoefficientRingEquiv.seriesEquiv_coeff
    (coefficientRingEquiv K E) f j

@[simp] theorem coefficientSeriesEquiv_parameter :
    coefficientSeriesEquiv K E (PowerSeries.X : PowerSeries (AlgebraicClosure K)) =
      (PowerSeries.X : PowerSeries (AlgebraicClosure E)) :=
  ActualTraitGroupFromCoefficientRingEquiv.seriesEquiv_parameter (coefficientRingEquiv K E)

def coefficientFractionEquiv :
    TraitFraction (AlgebraicClosure K) ≃+* TraitFraction (AlgebraicClosure E) :=
  ActualTraitGroupFromCoefficientRingEquiv.fractionEquiv (coefficientRingEquiv K E)

@[simp] theorem coefficientFractionEquiv_overSeries (f : PowerSeries (AlgebraicClosure K)) :
    coefficientFractionEquiv K E
      (algebraMap (PowerSeries (AlgebraicClosure K)) (TraitFraction (AlgebraicClosure K)) f) =
      algebraMap (PowerSeries (AlgebraicClosure E)) (TraitFraction (AlgebraicClosure E))
        (coefficientSeriesEquiv K E f) :=
  ActualTraitGroupFromCoefficientRingEquiv.fractionEquiv_overSeries
    (coefficientRingEquiv K E) f

def coefficientClosureEquiv :
    TraitClosure (AlgebraicClosure K) ≃+* TraitClosure (AlgebraicClosure E) :=
  ActualTraitGroupFromCoefficientRingEquiv.closureEquiv (coefficientRingEquiv K E)

@[simp] theorem coefficientClosureEquiv_overFraction (x : TraitFraction (AlgebraicClosure K)) :
    coefficientClosureEquiv K E
      (algebraMap (TraitFraction (AlgebraicClosure K)) (TraitClosure (AlgebraicClosure K)) x) =
      algebraMap (TraitFraction (AlgebraicClosure E)) (TraitClosure (AlgebraicClosure E))
        (coefficientFractionEquiv K E x) :=
  ActualTraitGroupFromCoefficientRingEquiv.closureEquiv_overFraction
    (coefficientRingEquiv K E) x

@[simp] theorem coefficientClosureEquiv_overEverySeries
    (f : PowerSeries (AlgebraicClosure K)) :
    coefficientClosureEquiv K E (seriesEmbedding f) =
      seriesEmbedding (coefficientSeriesEquiv K E f) :=
  ActualTraitGroupFromCoefficientRingEquiv.closureEquiv_overEverySeries
    (coefficientRingEquiv K E) f

@[simp] theorem coefficientClosureEquiv_parameter :
    coefficientClosureEquiv K E
      (seriesEmbedding (PowerSeries.X : PowerSeries (AlgebraicClosure K))) =
      seriesEmbedding (PowerSeries.X : PowerSeries (AlgebraicClosure E)) :=
  ActualTraitGroupFromCoefficientRingEquiv.closureEquiv_parameter (coefficientRingEquiv K E)

/-- The two successive closure choices still preserve all the original K constants. -/
theorem coefficientClosureEquiv_overBaseConstant (k : K) :
    coefficientClosureEquiv K E
      (seriesEmbedding (PowerSeries.C (algebraMap K (AlgebraicClosure K) k))) =
      seriesEmbedding (PowerSeries.C
        (algebraMap E (AlgebraicClosure E) (algebraMap K E k))) := by
  rw [coefficientClosureEquiv_overEverySeries]
  change seriesEmbedding (ActualTraitGroupFromCoefficientRingEquiv.seriesEquiv
    (coefficientRingEquiv K E) (PowerSeries.C _)) = _
  rw [ActualTraitGroupFromCoefficientRingEquiv.seriesEquiv_constant,
    coefficientRingEquiv_overBase]

def coefficientGroupEquiv :
    TraitGroup (AlgebraicClosure K) ≃* TraitGroup (AlgebraicClosure E) :=
  ActualTraitGroupFromCoefficientRingEquiv.groupEquiv (coefficientRingEquiv K E)

/-- Equivariance on EVERY element of the literal formal trait closure. -/
theorem coefficientGroupEquiv_intertwines (r : TraitGroup (AlgebraicClosure K))
    (x : TraitClosure (AlgebraicClosure K)) :
    coefficientGroupEquiv K E r (coefficientClosureEquiv K E x) =
      coefficientClosureEquiv K E (r x) :=
  ActualTraitGroupFromCoefficientRingEquiv.groupEquiv_intertwines
    (coefficientRingEquiv K E) r x

/-- Every target fraction is fixed, with the SAME actual target base algebra. -/
theorem coefficientGroupEquiv_commutes (r : TraitGroup (AlgebraicClosure K))
    (x : TraitFraction (AlgebraicClosure E)) :
    coefficientGroupEquiv K E r
      (algebraMap (TraitFraction (AlgebraicClosure E)) (TraitClosure (AlgebraicClosure E)) x) =
      algebraMap (TraitFraction (AlgebraicClosure E)) (TraitClosure (AlgebraicClosure E)) x :=
  ActualTraitGroupFromCoefficientRingEquiv.groupEquiv_commutes
    (coefficientRingEquiv K E) r x

/-- Literal EVERY-series coefficient/action square, with positive X. -/
theorem coefficientGroupEquiv_overEverySeries (r : TraitGroup (AlgebraicClosure K))
    (f : PowerSeries (AlgebraicClosure K)) :
    coefficientGroupEquiv K E r (seriesEmbedding (coefficientSeriesEquiv K E f)) =
      coefficientClosureEquiv K E (r (seriesEmbedding f)) :=
  ActualTraitGroupFromCoefficientRingEquiv.groupEquiv_overEverySeries
    (coefficientRingEquiv K E) r f

end Algebraic

section Finite
variable (K E : Type) [Field K] [Field E] [Algebra K E] [Finite E]

/-- Finite fields give the algebraicity guard by existing Module.Finite;
there is no additional geometric or change-of-constants theorem premise. -/
def finiteCoefficientRingEquiv : AlgebraicClosure K ≃+* AlgebraicClosure E := by
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  exact coefficientRingEquiv K E

theorem finiteCoefficientRingEquiv_overBase (k : K) :
    finiteCoefficientRingEquiv K E (algebraMap K (AlgebraicClosure K) k) =
      algebraMap E (AlgebraicClosure E) (algebraMap K E k) := by
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  exact coefficientRingEquiv_overBase K E k

end Finite
end PrimeGap182.TypeIII.AlgebraicConstantFieldCommonTraitTransport
