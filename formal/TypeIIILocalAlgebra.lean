import TypeIIICorrelationFourier
import TypeIIICurveOpen
import TypeIIICurveGenericPoint
import TypeIIICurveProjection
import TypeIIILineDescent
import TypeIIIArtinSchreierAction
import TypeIIIJordanCorrection
import TypeIIITameLinearAlgebra
import TypeIIICurveTangencyMultiplicity

/-!
# Concrete local algebra supporting the finite-field Type III proof

This entry collects actual finite Fourier identities, phase and quotient
calculations, constant-field descent, curve equations and function fields,
generic projection polynomials, and the Jordan correction model.

It deliberately has no theorem asserting `TypeIII.LocalFourierHypothesis`.
The geometric realization of the correlation, local Fourier and stationary
phase theorems, and uniform weight/complexity bounds still have to be connected
to these results to prove that finite-field proposition. The global analytic
entry `PrimeGaps182Analytic` retains that explicit hypothesis.
-/

#print axioms PrimeGap182.TypeIII.correlation_two_variable_fourier
#print axioms PrimeGap182.TypeIII.toricPhaseFourier_radial
#print axioms PrimeGap182.TypeIII.jordanThreeCentralizerConjugation_trace_nat
#print axioms PrimeGap182.TypeIII.CurvePolynomial.irreducible_bivariate_dvd_euler_eq_linear_charP
#print axioms PrimeGap182.TypeIII.CurveDirection.irreducible_direction_eq_linear_factor_charP
#print axioms PrimeGap182.TypeIII.CurveOpen.exists_nonradial_regular_point_avoiding_finite_charP
#print axioms PrimeGap182.TypeIII.CurveFunctionField.gaussSlope_transcendental_charP
#print axioms PrimeGap182.TypeIII.CurveFunctionField.criticalValue_ne_zero_charP
#print axioms PrimeGap182.TypeIII.CurveFunctionField.parameterEmbedding_X
#print axioms PrimeGap182.TypeIII.CurveFunctionField.generic_tangent_data_charP
#print axioms PrimeGap182.TypeIII.CurveProjection.degree_genericProjectionPolynomial
#print axioms PrimeGap182.TypeIII.rationalAlgebraicClosure_finite_orbit_iff
#print axioms PrimeGap182.TypeIII.zero_mem_lineDescentAffineLine_of_finite_orbit
#print axioms PrimeGap182.TypeIII.algebraicDistinctRectanglePhase_ne_linearReciprocalSqrt
#print axioms PrimeGap182.TypeIII.laurentPoleOneClass_injective
#print axioms PrimeGap182.TypeIII.laurentArtinSchreierAction_poleOneClass
#print axioms PrimeGap182.TypeIII.rescaled_distinctRectanglePhase_not_mem_finite_invariant_artinSchreier_set
#print axioms PrimeGap182.TypeIII.cyclicBranches_has_nontrivial_eigenvector
#print axioms PrimeGap182.TypeIII.scalarTwists_restrictions_eq
#print axioms PrimeGap182.TypeIII.CurveTangencyMultiplicity.generic_tangency_multiplicity_charP
