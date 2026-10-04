import TypeIIIPublishedPhaseApplication

/-!
# Algebraic extension of the constant field preserves the generic phase field

Both phase fields are algebraic closures of the same rational-function
field after an algebraic constant extension. Their isomorphism is taken
over the original rational-function field, so the generic variable and
original constants are preserved. No geometric family comparison is a
hypothesis in this field-algebra step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors
attribute [local instance] Polynomial.algebra

namespace PrimeGap182.TypeIII.PhaseFieldConstants

open PublishedPhaseApplication

universe u v
variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

local instance rationalAlgebra : Algebra (RatFunc K) (RatFunc L) :=
  RatFunc.liftAlgebra K (RatFunc L)

local instance rationalTower : IsScalarTower (Polynomial K) (RatFunc K) (RatFunc L) :=
  RatFunc.isScalarTower_liftAlgebra K (RatFunc L)

variable [Algebra.IsAlgebraic K L]

/-- Extending algebraic constants also gives an algebraic extension of
rational-function fields. -/
theorem rational_isAlgebraic : Algebra.IsAlgebraic (RatFunc K) (RatFunc L) := by
  let : Algebra.IsAlgebraic (Polynomial L) (RatFunc L) :=
    IsLocalization.isAlgebraic (RatFunc L) (Polynomial L)⁰
  let : Algebra.IsAlgebraic (Polynomial K) (RatFunc L) :=
    Algebra.IsAlgebraic.trans (Polynomial K) (Polynomial L) (RatFunc L)
  exact Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (Polynomial K) (RatFunc K))

local instance rationalAlgebraic : Algebra.IsAlgebraic (RatFunc K) (RatFunc L) :=
  rational_isAlgebraic K L

/-- The field isomorphism fixes the whole original rational-function
field. Algebraic closure uniqueness supplies it, not a family premise. -/
def phaseFieldEquiv : PhaseField K ≃+* PhaseField L :=
  (IsAlgClosure.equiv (RatFunc K) (PhaseField K) (PhaseField L)).toRingEquiv

omit [Algebra.IsAlgebraic K L] in
/-- Polynomial coefficients and the variable are preserved by the
rational-function scalar extension. -/
theorem rational_algebraMap_polynomial (f : Polynomial K) :
    algebraMap (RatFunc K) (RatFunc L) (algebraMap (Polynomial K) (RatFunc K) f) =
      algebraMap (Polynomial L) (RatFunc L) (f.map (algebraMap K L)) := by
  rw [← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (RatFunc L)]
  rfl

/-- The chosen phase-field equivalence fixes the generic direction. -/
theorem phaseFieldEquiv_direction : phaseFieldEquiv K L (direction K) = direction L := by
  change (IsAlgClosure.equiv (RatFunc K) (PhaseField K) (PhaseField L))
    (algebraMap (RatFunc K) (PhaseField K) RatFunc.X) = _
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc L) (PhaseField L)]
  change algebraMap (RatFunc L) (PhaseField L)
    (algebraMap (RatFunc K) (RatFunc L) (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) = _
  rw [rational_algebraMap_polynomial, Polynomial.map_X, RatFunc.algebraMap_X]
  rfl

/-- The original constants are carried to their specified images in L. -/
theorem phaseFieldEquiv_constant (a : K) :
    phaseFieldEquiv K L (algebraMap K (PhaseField K) a) =
      algebraMap L (PhaseField L) (algebraMap K L a) := by
  rw [← phaseField_map_C]
  change (IsAlgClosure.equiv (RatFunc K) (PhaseField K) (PhaseField L))
    (algebraMap (RatFunc K) (PhaseField K) (RatFunc.C a)) = _
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc L) (PhaseField L)]
  change algebraMap (RatFunc L) (PhaseField L)
    (algebraMap (RatFunc K) (RatFunc L) (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))) = _
  rw [rational_algebraMap_polynomial, Polynomial.map_C, RatFunc.algebraMap_C, phaseField_map_C]

/-- Preserve the literal radial scale, not only nonvanishing. -/
theorem phaseFieldEquiv_radialScale (alpha m : K) :
    phaseFieldEquiv K L (radialScale alpha m) =
      radialScale (algebraMap K L alpha) (algebraMap K L m) := by
  simp only [radialScale, map_div₀, map_mul, phaseFieldEquiv_constant, phaseFieldEquiv_direction]

end PrimeGap182.TypeIII.PhaseFieldConstants

#print axioms PrimeGap182.TypeIII.PhaseFieldConstants.rational_isAlgebraic
#print axioms PrimeGap182.TypeIII.PhaseFieldConstants.phaseFieldEquiv
#print axioms PrimeGap182.TypeIII.PhaseFieldConstants.rational_algebraMap_polynomial
#print axioms PrimeGap182.TypeIII.PhaseFieldConstants.phaseFieldEquiv_direction
#print axioms PrimeGap182.TypeIII.PhaseFieldConstants.phaseFieldEquiv_constant
#print axioms PrimeGap182.TypeIII.PhaseFieldConstants.phaseFieldEquiv_radialScale
