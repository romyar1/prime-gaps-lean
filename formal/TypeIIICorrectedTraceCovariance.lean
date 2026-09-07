import TypeIIIFiniteFieldCovariance
import TypeIIIGeometricAssembly

/-!
# Corrected Type III trace covariance over every finite extension

The arithmetic functions retain the original correlation, correction
`1 + q⁻¹ + q⁻²`, and four-cycle conjugation pattern. The expected trace of
each corrected rank-six factor over a degree-d extension is multiplied by
`(-1)^(d+1)`. This sign is kept for every subset of the four factors, including
odd-cardinality subsets; it specializes to one over the prime field.

Every identity below is an exact finite-sum or field identity. In particular,
the arithmetic covariance is not a sheaf isomorphism or a statement that a
complex coefficient automorphism preserves absolute values. The functions
are also defined on the axes using the old arithmetic zero convention before
adding the correction; a sheaf application uses their restriction to the torus.
-/

noncomputable section
open scoped BigOperators Classical

universe u

namespace PrimeGap182.TypeIII.FiniteFieldSums

/-- The literal boundary correction, normalized by the size of the field. -/
def coreCorrection (K : Type u) [Fintype K] : ℂ :=
  1 + (Fintype.card K : ℂ)⁻¹ + ((Fintype.card K : ℂ)⁻¹) ^ 2

theorem coreCorrection_star (K : Type u) [Fintype K] :
    star (coreCorrection K) = coreCorrection K := by
  simp only [coreCorrection, star_add, star_one, star_inv₀, star_natCast, star_pow]

theorem coreCorrection_map (K : Type u) [Fintype K] (σ : ℂ →+* ℂ) :
    σ (coreCorrection K) = coreCorrection K := by
  simp only [coreCorrection, map_add, map_one, map_inv₀, map_natCast, map_pow]

section CorrectedSums

variable {K : Type u} [Field K] [Fintype K] (ψ : AddChar K ℂ)

def correctedKernel (α m n x y : K) : ℂ :=
  kernel ψ α m n x y + coreCorrection K

/-- The entries have exactly the same order and conjugations as the
prime-field `correctedCycleFactors`. -/
def correctedCycleFactors (α m m' n n' : K) (i : Fin 4) (x y : K) : ℂ :=
  ![correctedKernel ψ α m n x y,
    star (correctedKernel ψ α m' n x y),
    correctedKernel ψ α m' n' x y,
    star (correctedKernel ψ α m n' x y)] i

def correctedTraceProduct (α m m' n n' : K) (S : Finset (Fin 4)) (x y : K) : ℂ :=
  ∏ i ∈ S, correctedCycleFactors ψ α m m' n n' i x y

theorem correctedKernel_star (α m n x y : K) :
    star (correctedKernel ψ α m n x y) = correctedKernel ψ α m n x y := by
  simp only [correctedKernel, star_add, kernel_star, coreCorrection_star]

theorem correctedCycleFactors_star (α m m' n n' : K) (i : Fin 4) (x y : K) :
    star (correctedCycleFactors ψ α m m' n n' i x y) =
      correctedCycleFactors ψ α m m' n n' i x y := by
  fin_cases i <;> simp [correctedCycleFactors, correctedKernel_star]

theorem correctedKernel_coefficient_parameter_covariance
    (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (α m n x y : K) :
    σ (correctedKernel ψ α m n x y) = correctedKernel ψ (a ^ 2 * α) m n x y := by
  simp only [correctedKernel, map_add, coreCorrection_map,
    kernel_coefficient_covariance ψ σ a ha hσ]

/-- Quadratic parameter covariance is exactly inverse-square physical
dilation, with the original row and column indices fixed. -/
theorem correctedKernel_coefficient_covariance
    (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (α m n x y : K)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    σ (correctedKernel ψ α m n x y) =
      correctedKernel ψ α m n (x / a ^ 2) (y / a ^ 2) := by
  rw [correctedKernel_coefficient_parameter_covariance ψ σ a ha hσ]
  have hb : a ^ 2 ≠ 0 := pow_ne_zero _ ha
  have hx : a ^ 2 * (x / a ^ 2) = x := by field_simp
  have hy : a ^ 2 * (y / a ^ 2) = y := by field_simp
  have h := kernel_common_parameter_dilation ψ α m n (a ^ 2)
    (x / a ^ 2) (y / a ^ 2) hm hn hb
  rw [hx, hy] at h
  exact congrArg (fun z : ℂ => z + coreCorrection K) h

/-- Conjugation is removed only by the proved reality of these particular
finite sums, never by assuming a general coefficient automorphism is a star map. -/
theorem correctedCycleFactors_coefficient_covariance
    (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (α m m' n n' : K)
    (i : Fin 4) (x y : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    σ (correctedCycleFactors ψ α m m' n n' i x y) =
      correctedCycleFactors ψ α m m' n n' i (x / a ^ 2) (y / a ^ 2) := by
  have h₀ := correctedKernel_coefficient_covariance ψ σ a ha hσ α m n x y hm hn
  have h₁ := correctedKernel_coefficient_covariance ψ σ a ha hσ α m' n x y hm' hn
  have h₂ := correctedKernel_coefficient_covariance ψ σ a ha hσ α m' n' x y hm' hn'
  have h₃ := correctedKernel_coefficient_covariance ψ σ a ha hσ α m n' x y hm hn'
  fin_cases i <;> simp [correctedCycleFactors, correctedKernel_star, h₀, h₁, h₂, h₃]

theorem correctedTraceProduct_coefficient_covariance
    (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (α m m' n n' : K)
    (S : Finset (Fin 4)) (x y : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    σ (correctedTraceProduct ψ α m m' n n' S x y) =
      correctedTraceProduct ψ α m m' n n' S (x / a ^ 2) (y / a ^ 2) := by
  simp only [correctedTraceProduct, map_prod]
  exact Finset.prod_congr rfl (fun i _ =>
    correctedCycleFactors_coefficient_covariance ψ σ a ha hσ α m m' n n' i x y
      hm hm' hn hn')

end CorrectedSums

section ExpectedTraces

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [Fintype K] [Algebra (ZMod p) K]

/-- The constant Weil sign twist combined with the degree-one compact
cohomology sign. It is not replaced by one in even extension degree. -/
def extensionSign : ℂ := (-1) ^ (Module.finrank (ZMod p) K + 1)

omit [Fintype K] in
theorem extensionSign_star : star (extensionSign p K) = extensionSign p K := by
  simp only [extensionSign, star_pow, star_neg, star_one]

omit [Fintype K] in
theorem extensionSign_map (σ : ℂ →+* ℂ) : σ (extensionSign p K) = extensionSign p K := by
  simp only [extensionSign, map_pow, map_neg, map_one]

omit [Fintype K] in
/-- Reality of the sign means that applying it before or after the
conjugation in a dual-twisted factor gives the same signed trace. -/
theorem extensionSign_mul_star (z : ℂ) :
    extensionSign p K * star z = star (extensionSign p K * z) := by
  rw [star_mul, extensionSign_star, mul_comm]

/-- Expected arithmetic trace of the actual signed rank-six tensor
subproduct over a finite extension, with the sign applied to every factor. -/
def expectedTrace (α m m' n n' : K) (S : Finset (Fin 4)) (x y : K) : ℂ :=
  ∏ i ∈ S, extensionSign p K *
    correctedCycleFactors (traceAddChar p K) α m m' n n' i x y

theorem expectedTrace_eq_sign_mul_correctedTraceProduct
    (α m m' n n' : K) (S : Finset (Fin 4)) (x y : K) :
    expectedTrace p K α m m' n n' S x y =
      extensionSign p K ^ S.card *
        correctedTraceProduct (traceAddChar p K) α m m' n n' S x y := by
  simp only [expectedTrace, correctedTraceProduct, Finset.prod_mul_distrib, Finset.prod_const]

theorem expectedTrace_empty (α m m' n n' x y : K) :
    expectedTrace p K α m m' n n' ∅ x y = 1 := by
  simp only [expectedTrace, Finset.prod_empty]

theorem expectedTrace_star (α m m' n n' : K) (S : Finset (Fin 4)) (x y : K) :
    star (expectedTrace p K α m m' n n' S x y) =
      expectedTrace p K α m m' n n' S x y := by
  simp only [expectedTrace, star_prod, star_mul, extensionSign_star,
    correctedCycleFactors_star, mul_comm]

/-- Exact covariance for a given automorphism and its actual action on
the canonical trace character of this extension. -/
theorem expectedTrace_coefficient_covariance
    (σ : ℂ ≃+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (traceAddChar p K t) = traceAddChar p K (a * t))
    (α m m' n n' : K) (S : Finset (Fin 4)) (x y : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    σ (expectedTrace p K α m m' n n' S x y) =
      expectedTrace p K α m m' n n' S (x / a ^ 2) (y / a ^ 2) := by
  have hsign : σ (extensionSign p K) = extensionSign p K :=
    extensionSign_map p K σ.toRingHom
  have hproduct : σ (correctedTraceProduct (traceAddChar p K) α m m' n n' S x y) =
      correctedTraceProduct (traceAddChar p K) α m m' n n' S
        (x / a ^ 2) (y / a ^ 2) :=
    correctedTraceProduct_coefficient_covariance (traceAddChar p K) σ.toRingHom
      a ha hσ α m m' n n' S x y hm hm' hn hn'
  rw [expectedTrace_eq_sign_mul_correctedTraceProduct,
    expectedTrace_eq_sign_mul_correctedTraceProduct, map_mul, map_pow]
  rw [hsign, hproduct]

end ExpectedTraces

section PrimeCoefficientAction

variable (p : ℕ) [Fact p.Prime]

/-- One action on the prime-field character acts on the canonical trace
characters of every finite extension, by linearity of the original field trace. -/
theorem traceAddChar_coefficient_covariance_of_prime
    (σ : ℂ →+* ℂ) (a : ZMod p)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (K : Type u) [Field K] [Fintype K] [Algebra (ZMod p) K] (t : K) :
    σ (traceAddChar p K t) =
      traceAddChar p K (algebraMap (ZMod p) K a * t) := by
  have ht : Algebra.trace (ZMod p) K (algebraMap (ZMod p) K a * t) =
      a * Algebra.trace (ZMod p) K t := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self,
      RingHom.id_apply] using (Algebra.trace (ZMod p) K).map_smul a t
  change σ (ZMod.stdAddChar (Algebra.trace (ZMod p) K t)) =
    ZMod.stdAddChar (Algebra.trace (ZMod p) K (algebraMap (ZMod p) K a * t))
  rw [hσ, ht]

/-- The same coefficient automorphism is fixed before the arbitrary
extension field, subset, physical point, and residue parameters. -/
theorem expectedTrace_coefficient_covariance_of_prime
    (σ : ℂ ≃+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (K : Type u) [Field K] [Fintype K] [Algebra (ZMod p) K]
    (α m m' n n' : K) (S : Finset (Fin 4)) (x y : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    σ (expectedTrace p K α m m' n n' S x y) =
      expectedTrace p K α m m' n n' S
        (x / (algebraMap (ZMod p) K a) ^ 2) (y / (algebraMap (ZMod p) K a) ^ 2) :=
  expectedTrace_coefficient_covariance p K σ (algebraMap (ZMod p) K a)
    (by simpa only [map_zero] using (algebraMap (ZMod p) K).injective.ne ha)
    (traceAddChar_coefficient_covariance_of_prime p σ.toRingHom a hσ K)
    α m m' n n' S x y hm hm' hn hn'

/-- The coefficient action relevant to support rigidity is physical
dilation by one quarter, simultaneously over every finite extension. -/
theorem expectedTrace_coefficient_covariance_two
    (σ : ℂ ≃+* ℂ) (h2 : (2 : ZMod p) ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t))
    (K : Type u) [Field K] [Fintype K] [Algebra (ZMod p) K]
    (α m m' n n' : K) (S : Finset (Fin 4)) (x y : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    σ (expectedTrace p K α m m' n n' S x y) =
      expectedTrace p K α m m' n n' S (x / 4) (y / 4) := by
  simpa only [map_ofNat, show (2 : K) ^ 2 = 4 by ring] using
    expectedTrace_coefficient_covariance_of_prime p σ 2 h2 hσ K
      α m m' n n' S x y hm hm' hn hn'

end PrimeCoefficientAction

section PrimeSpecialization

variable (p : ℕ) [Fact p.Prime]

theorem coreCorrection_prime :
    coreCorrection (ZMod p) = (PrimeGap182.TypeIII.coreCorrection p : ℂ) := by
  simp only [coreCorrection, PrimeGap182.TypeIII.coreCorrection, ZMod.card,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem correctedKernel_prime (α m n x y : ZMod p) :
    correctedKernel (traceAddChar p (ZMod p)) α m n x y =
      PrimeGap182.TypeIII.correctedKernel p α m n x y := by
  simp only [correctedKernel, kernel_prime, coreCorrection_prime,
    PrimeGap182.TypeIII.correctedKernel]

theorem correctedCycleFactors_prime (α m m' n n' : ZMod p) (i : Fin 4)
    (x y : ZMod p) :
    correctedCycleFactors (traceAddChar p (ZMod p)) α m m' n n' i x y =
      PrimeGap182.TypeIII.correctedCycleFactors p α m m' n n' i x y := by
  simp only [correctedCycleFactors, PrimeGap182.TypeIII.correctedCycleFactors,
    correctedKernel_prime]

theorem extensionSign_prime : extensionSign p (ZMod p) = 1 := by
  simp only [extensionSign, CommSemiring.finrank_self]
  norm_num

/-- The full expected all-extension trace specializes to the actual
corrected prime-field subproduct, without any residual sign or normalization. -/
theorem expectedTrace_prime (α m m' n n' : ZMod p) (S : Finset (Fin 4))
    (x y : ZMod p) :
    expectedTrace p (ZMod p) α m m' n n' S x y =
      ∏ i ∈ S, PrimeGap182.TypeIII.correctedCycleFactors p α m m' n n' i x y := by
  simp only [expectedTrace, extensionSign_prime, one_mul, correctedCycleFactors_prime]

end PrimeSpecialization

#print axioms coreCorrection
#print axioms coreCorrection_star
#print axioms coreCorrection_map
#print axioms correctedKernel
#print axioms correctedCycleFactors
#print axioms correctedTraceProduct
#print axioms correctedKernel_star
#print axioms correctedCycleFactors_star
#print axioms correctedKernel_coefficient_parameter_covariance
#print axioms correctedKernel_coefficient_covariance
#print axioms correctedCycleFactors_coefficient_covariance
#print axioms correctedTraceProduct_coefficient_covariance
#print axioms extensionSign
#print axioms extensionSign_star
#print axioms extensionSign_map
#print axioms extensionSign_mul_star
#print axioms expectedTrace
#print axioms expectedTrace_eq_sign_mul_correctedTraceProduct
#print axioms expectedTrace_empty
#print axioms expectedTrace_star
#print axioms expectedTrace_coefficient_covariance
#print axioms traceAddChar_coefficient_covariance_of_prime
#print axioms expectedTrace_coefficient_covariance_of_prime
#print axioms expectedTrace_coefficient_covariance_two
#print axioms coreCorrection_prime
#print axioms correctedKernel_prime
#print axioms correctedCycleFactors_prime
#print axioms extensionSign_prime
#print axioms expectedTrace_prime

end PrimeGap182.TypeIII.FiniteFieldSums
