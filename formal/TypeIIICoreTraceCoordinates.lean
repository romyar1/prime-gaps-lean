import TypeIIICorrectedTraceCovariance
import TypeIIIPublishedParabolicTrace

/-!
# The actual parameter map from parabolic cohomology to the Type III kernel

The sum here is the literal point sum of the Kloosterman tensor and additive
twist on the x-line. Reindexing by xi gives the original correlation.
The fixed monomial map on the physical torus is then checked algebraically.
These coordinate identities need no cohomological premise. The final theorem
combines them with the explicit boundary exact-sequence data and the compact
trace-formula premise; it does not construct their geometric realization.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.FiniteFieldSums

universe u
variable {K : Type u} [Field K] [Fintype K]

/-- The literal point sum for K(x) tensor K(lambda*x)^dual tensor AS(xi*x). -/
def parabolicInputSum (ψ : AddChar K ℂ) (lambda xi : K) : ℂ :=
  ∑ x : Kˣ, kl3 ψ (x : K) * star (kl3 ψ (lambda * (x : K))) * ψ (xi * (x : K))

/-- Reindex by h=xi*x, using an actual equivalence of the unit group. -/
theorem parabolicInputSum_eq_correlation (ψ : AddChar K ℂ)
    (lambda xi : K) (hxi : xi ≠ 0) :
    parabolicInputSum ψ lambda xi = correlation ψ xi⁻¹ (lambda * xi⁻¹) 1 := by
  unfold parabolicInputSum correlation
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 xi hxi)) _ _ ?_
  intro x
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0, one_mul]
  have hfirst : xi⁻¹ * (xi * (x : K)) = (x : K) := by field_simp
  have hsecond : lambda * xi⁻¹ * (xi * (x : K)) = lambda * (x : K) := by field_simp
  rw [hfirst, hsecond]

/-- First coordinate of the actual physical parameter map. -/
def coreLambda (m n x y : K) : K := m * x ^ 3 / (n * y ^ 3)

/-- Second coordinate of the same map. -/
def coreXi (α m x y : K) : K := m * x ^ 2 / (α * y)

omit [Fintype K] in
theorem coreLambda_ne_zero (m n x y : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    coreLambda m n x y ≠ 0 := by
  exact div_ne_zero (mul_ne_zero hm (pow_ne_zero _ hx))
    (mul_ne_zero hn (pow_ne_zero _ hy))

omit [Fintype K] in
theorem coreXi_ne_zero (α m x y : K)
    (hα : α ≠ 0) (hm : m ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    coreXi α m x y ≠ 0 := by
  exact div_ne_zero (mul_ne_zero hm (pow_ne_zero _ hx)) (mul_ne_zero hα hy)

omit [Fintype K] in
theorem coreXi_inv (α m x y : K) :
    (coreXi α m x y)⁻¹ = α * y / (m * x ^ 2) := by
  simp only [coreXi, inv_div]

omit [Fintype K] in
theorem coreLambda_mul_coreXi_inv (α m n x y : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    coreLambda m n x y * (coreXi α m x y)⁻¹ = α * x / (n * y ^ 2) := by
  rw [coreXi_inv]
  unfold coreLambda
  field_simp

/-- The parabolic input sum, pulled back along the checked parameter map,
is exactly the original Type III kernel at every physical torus point. -/
theorem parabolicInputSum_eq_kernel (ψ : AddChar K ℂ) (α m n x y : K)
    (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    parabolicInputSum ψ (coreLambda m n x y) (coreXi α m x y) =
      kernel ψ α m n x y := by
  rw [parabolicInputSum_eq_correlation ψ _ _ (coreXi_ne_zero α m x y hα hm hx hy),
    coreLambda_mul_coreXi_inv α m n x y hm hn hx hy, coreXi_inv]
  simp only [kernel, ite_eq_right (not_or.mpr ⟨hx, hy⟩)]

/-- The signed corrected trace furnished by the parabolic trace argument
has exactly the same normalization as the expected finite-extension factor. -/
theorem signed_parabolicInputSum_eq_correctedKernel (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] (α m n x y : K)
    (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    extensionSign p K *
        (parabolicInputSum (traceAddChar p K) (coreLambda m n x y) (coreXi α m x y) +
          coreCorrection K) =
      extensionSign p K * correctedKernel (traceAddChar p K) α m n x y := by
  rw [parabolicInputSum_eq_kernel (traceAddChar p K) α m n x y hα hm hn hx hy]
  rfl

/-- Rank and signed trace for the supplied actual cohomology maps, after
the proved physical substitution. The compact trace formula is for the
literal Kloosterman-tensor point sum, not for an already corrected core. -/
theorem rank_and_signed_core_trace (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
    {Vc : Type*} [AddCommGroup Vc] [Module ℂ Vc] [FiniteDimensional ℂ Vc]
    {Vpar : Type*} [AddCommGroup Vpar] [Module ℂ Vpar]
    (D : PublishedParabolicTrace.JordanBoundaryData (Fintype.card K : ℂ)
      (PublishedParabolicTrace.complexCard_ne_zero K) Vc Vpar)
    (α m n x y : K) (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hrank : Module.finrank ℂ Vc = 9)
    (htrace : LinearMap.trace ℂ Vc D.compactFrobenius =
      -parabolicInputSum (traceAddChar p K) (coreLambda m n x y) (coreXi α m x y)) :
    Module.finrank ℂ Vpar = 6 ∧
      LinearMap.trace ℂ Vpar
        (((-1 : ℂ) ^ Module.finrank (ZMod p) K) • D.parabolicFrobenius) =
          extensionSign p K * correctedKernel (traceAddChar p K) α m n x y := by
  refine ⟨D.finrank_eq_six hrank, ?_⟩
  have h := D.signed_trace_eq (Module.finrank (ZMod p) K) _ htrace
  rw [h]
  exact signed_parabolicInputSum_eq_correctedKernel p α m n x y hα hm hn hx hy

end PrimeGap182.TypeIII.FiniteFieldSums

#print axioms PrimeGap182.TypeIII.FiniteFieldSums.parabolicInputSum
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.parabolicInputSum_eq_correlation
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.coreLambda
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.coreXi
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.coreLambda_ne_zero
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.coreXi_ne_zero
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.coreXi_inv
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.coreLambda_mul_coreXi_inv
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.parabolicInputSum_eq_kernel
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.signed_parabolicInputSum_eq_correctedKernel
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.rank_and_signed_core_trace
