import TypeIIICorrelationCRT
import TypeIIICubicSchur
import TypeIIIMatrixFourthMoment

/-!
# The actual shared Fourier factor as a matching multiplier of the matrix kernel

Primes are partitioned by the reduction of one fixed integer frequency. The matrix is
defined on the full row and column intervals; equality with the original shared correlation
is proved on its active unit rows and columns. Thus coefficient masks can keep the original
arithmetic restrictions while the nonnegative fourth moment is enlarged.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

local instance familyProductNeZero {τ : Type*} [Fintype τ] (q : τ → ℕ)
    [∀ i, Fact (q i).Prime] : NeZero (∏ i, q i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (Fact.out : (q i).Prime).ne_zero)⟩

variable {ι : Type*} [Fintype ι]
variable (q : ι → ℕ) [∀ i, Fact (q i).Prime]

abbrev ZeroFrequencyPrime (c : ℤ) := {i : ι // (c : ZMod (q i)) = 0}
abbrev NonzeroFrequencyPrime (c : ℤ) := {i : ι // (c : ZMod (q i)) ≠ 0}

/-- The parameter contains the original complementary factor, before the zero-frequency
primes were removed. It is independent of both outer modulus variables. -/
def nonzeroFrequencyParameter (a c : ℤ) (i : NonzeroFrequencyPrime q c) : ZMod (q i.1) :=
  (a : ZMod (q i.1)) / (c : ZMod (q i.1)) * ((crtComplement q i.1 : ZMod (q i.1))⁻¹) ^ 2

theorem local_integer_ne_zero (x : ℤ) (hx : IsUnit (x : ZMod (∏ i, q i))) (i : ι) :
    (x : ZMod (q i)) ≠ 0 :=
  (PrimeGap186.isUnit_intCast_of_dvd (q i) (∏ j, q j)
    (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) x hx).ne_zero

theorem crtComplement_ne_zero (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (i : ι) :
    (crtComplement q i : ZMod (q i)) ≠ 0 :=
  ((ZMod.isUnit_iff_coprime (crtComplement q i) (q i)).mpr
    (crtComplement_coprime q hcp i).symm).ne_zero

theorem nonzeroFrequencyParameter_ne_zero
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (a c : ℤ)
    (ha : IsUnit (a : ZMod (∏ i, q i))) (i : NonzeroFrequencyPrime q c) :
    nonzeroFrequencyParameter q a c i ≠ 0 :=
  mul_ne_zero (div_ne_zero (local_integer_ne_zero q a ha i.1) i.2)
    (pow_ne_zero _ (inv_ne_zero (crtComplement_ne_zero q hcp i.1)))

/-- The actual composite correlation splits into its cubic matching factors and the exact
integer kernel at the remaining modulus. -/
theorem shared_modCorrelation_eq_matching_integerKernel
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (a m n u v c : ℤ)
    (ha : IsUnit (a : ZMod (∏ i, q i))) (hm : IsUnit (m : ZMod (∏ i, q i)))
    (hn : IsUnit (n : ZMod (∏ i, q i))) (hu : IsUnit (u : ZMod (∏ i, q i)))
    (hv : IsUnit (v : ZMod (∏ i, q i))) :
    modCorrelation (∏ i, q i)
      ((a : ZMod (∏ i, q i)) * (m : ZMod (∏ i, q i))⁻¹ * ((u : ZMod (∏ i, q i))⁻¹) ^ 3)
      ((a : ZMod (∏ i, q i)) * (n : ZMod (∏ i, q i))⁻¹ * ((v : ZMod (∏ i, q i))⁻¹) ^ 3)
      ((c : ZMod (∏ i, q i)) * ((u : ZMod (∏ i, q i)) * (v : ZMod (∏ i, q i)))⁻¹) =
      (∏ i : ZeroFrequencyPrime q c,
        ((if (m : ZMod (q i.1)) * (u : ZMod (q i.1)) ^ 3 =
            (n : ZMod (q i.1)) * (v : ZMod (q i.1)) ^ 3 then (q i.1 : ℂ) else 0) -
          (zeroCorrelationCorrection (q i.1) : ℂ))) *
        integerKernel (fun i : NonzeroFrequencyPrime q c => q i.1)
          (nonzeroFrequencyParameter q a c) m n
          (u : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))
          (v : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1)) := by
  rw [shared_modCorrelation_prime_product q hcp a m n u v c hm hn hu hv]
  let F (i : ι) := correlation (q i)
    ((a : ZMod (q i)) / ((m : ZMod (q i)) * (u : ZMod (q i)) ^ 3))
    ((a : ZMod (q i)) / ((n : ZMod (q i)) * (v : ZMod (q i)) ^ 3))
    (((c : ZMod (q i)) * (crtComplement q i : ZMod (q i)) ^ 2) /
      ((u : ZMod (q i)) * (v : ZMod (q i))))
  change (∏ i, F i) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => (c : ZMod (q i)) = 0) F]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    have hh := shared_correlation_zero (q i.1) (a : ZMod (q i.1)) 1
      (m : ZMod (q i.1)) (n : ZMod (q i.1)) (u : ZMod (q i.1)) (v : ZMod (q i.1))
      (local_integer_ne_zero q a ha i.1) one_ne_zero (local_integer_ne_zero q m hm i.1)
      (local_integer_ne_zero q n hn i.1) (local_integer_ne_zero q u hu i.1)
      (local_integer_ne_zero q v hv i.1)
    simpa only [F, i.2, zero_mul, zero_div, one_pow, mul_one] using hh
  · have hactive : unitIntegerIndex (fun i : NonzeroFrequencyPrime q c => q i.1) m ∧
        unitIntegerIndex (fun i : NonzeroFrequencyPrime q c => q i.1) n :=
      ⟨fun i => local_integer_ne_zero q m hm i.1, fun i => local_integer_ne_zero q n hn i.1⟩
    rw [integerKernel, ite_eq_left hactive, squarefreeKernel]
    apply Finset.prod_congr rfl
    intro i _
    have hcast (x : ℤ) :
        ((x : ZMod (∏ j : NonzeroFrequencyPrime q c, q j.1)).val : ZMod (q i.1)) =
          (x : ZMod (q i.1)) := by
      rw [← ZMod.cast_eq_val,
        ZMod.cast_intCast (Finset.dvd_prod_of_mem
          (fun j : NonzeroFrequencyPrime q c => q j.1) (Finset.mem_univ i))]
    simp only [hcast]
    exact shared_normalized_correlation_eq_kernel (q i.1)
      (a : ZMod (q i.1)) (c : ZMod (q i.1)) (crtComplement q i.1 : ZMod (q i.1))
      (m : ZMod (q i.1)) (n : ZMod (q i.1)) (u : ZMod (q i.1)) (v : ZMod (q i.1))
      i.2 (crtComplement_ne_zero q hcp i.1) (local_integer_ne_zero q m hm i.1)
      (local_integer_ne_zero q n hn i.1) (local_integer_ne_zero q u hu i.1)
      (local_integer_ne_zero q v hv i.1)

/-- The matrix on complete row and column intervals that represents the shared factor
on all active coefficient entries. -/
def sharedMatchingMatrix (a c A B : ℤ) (N M : ℕ) (u v : ℤ) :
    Matrix (IntegerIntervalIndex A N) (IntegerIntervalIndex B M) ℂ :=
  primeMatchingProduct (fun i : ZeroFrequencyPrime q c => q i.1)
    (fun i m => (m.1 : ZMod (q i.1)) * (u : ZMod (q i.1)) ^ 3)
    (fun i n => (n.1 : ZMod (q i.1)) * (v : ZMod (q i.1)) ^ 3)
    (integerKernelMatrix (fun i : NonzeroFrequencyPrime q c => q i.1)
      (nonzeroFrequencyParameter q a c) A B N M
      (u : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))
      (v : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1)))

theorem sharedMatchingMatrix_apply_of_units
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (a c A B : ℤ) (N M : ℕ) (u v : ℤ)
    (ha : IsUnit (a : ZMod (∏ i, q i))) (hu : IsUnit (u : ZMod (∏ i, q i)))
    (hv : IsUnit (v : ZMod (∏ i, q i)))
    (m : IntegerIntervalIndex A N) (n : IntegerIntervalIndex B M)
    (hm : IsUnit (m.1 : ZMod (∏ i, q i))) (hn : IsUnit (n.1 : ZMod (∏ i, q i))) :
    sharedMatchingMatrix q a c A B N M u v m n =
      modCorrelation (∏ i, q i)
        ((a : ZMod (∏ i, q i)) * (m.1 : ZMod (∏ i, q i))⁻¹ * ((u : ZMod (∏ i, q i))⁻¹) ^ 3)
        ((a : ZMod (∏ i, q i)) * (n.1 : ZMod (∏ i, q i))⁻¹ * ((v : ZMod (∏ i, q i))⁻¹) ^ 3)
        ((c : ZMod (∏ i, q i)) * ((u : ZMod (∏ i, q i)) * (v : ZMod (∏ i, q i)))⁻¹) := by
  exact (shared_modCorrelation_eq_matching_integerKernel q hcp a m.1 n.1 u v c
    ha hm hn hu hv).symm

theorem sharedMatchingMatrix_norm_le (a c A B : ℤ) (N M : ℕ) (u v : ℤ) :
    ‖sharedMatchingMatrix q a c A B N M u v‖ ≤
      (4 : ℝ) ^ Fintype.card (ZeroFrequencyPrime q c) *
        ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) *
        ‖integerKernelMatrix (fun i : NonzeroFrequencyPrime q c => q i.1)
          (nonzeroFrequencyParameter q a c) A B N M
          (u : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))
          (v : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))‖ :=
  primeMatchingProduct_norm_le _ _ _ _

#print axioms nonzeroFrequencyParameter_ne_zero
#print axioms shared_modCorrelation_eq_matching_integerKernel
#print axioms sharedMatchingMatrix_apply_of_units
#print axioms sharedMatchingMatrix_norm_le

end

end PrimeGap182.TypeIII
