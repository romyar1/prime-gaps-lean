import HarmanAnalyticInterfaces182

/-! Actual arbitrary-arity prime boxes and their coprimality-filtered
Siegel--Walfisz estimates feed the common bilinear interface. No prime-box
distribution statement is installed as an axiom. Adapted from Apache-2.0
PrimeGaps186, with source hash checked by the generator. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem central_prime_box_typeII_coherent_log_saving_of_bilinear
    (j k : ℕ) («ω» δ σ η C : ℝ)
    (_hω : 0 < «ω») (_hδ : 0 < δ) (hσ : 0 < σ) (hη : 0 < η) (hC : 1 ≤ C)
    (hsource : SourceBilinearEstimate j «ω» δ σ) :
    ∀ A : ℝ, 0 < A →
      ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
        ∀ x : ℝ, X ≤ x → ∀ Y L U : Fin k → ℝ, ∀ S : Finset (Fin k),
          S.Nonempty → S ≠ Finset.univ →
          (∀ i, x ^ η ≤ Y i ∧ Y i ≤ x ^ (2 : ℝ)) →
          (∀ i, Y i ≤ L i ∧ U i ≤ 2 * Y i) →
          x / C ≤ ∏ i, Y i → (∏ i, Y i) ≤ C * x →
          x ^ (1 / 2 - σ) ≤ ∏ i ∈ S, Y i →
          (∏ i ∈ S, Y i) ≤ x ^ (1 / 2 : ℝ) →
          ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
          ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
            (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
                q ∣ (∏ p ∈ I, p) ∧
                  Nonempty (DenseDivisibilityWitness
                    ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩
                    j q)),
              ‖fullDiscrepancy (primeIntervalBoxAlgebra L U Finset.univ).coeff q a‖) ≤
                K * x / (Real.log x) ^ A := by
  let ι := (Fin k → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × Finset (Fin k)
  let good (x : ℝ) (b : ι) : Prop :=
    b.2.2.2.Nonempty ∧ b.2.2.2 ≠ Finset.univ ∧
      (∀ i, x ^ η ≤ b.1 i ∧ b.1 i ≤ x ^ (2 : ℝ)) ∧
      (∀ i, b.1 i ≤ b.2.1 i ∧ b.2.2.1 i ≤ 2 * b.1 i) ∧
      x / C ≤ ∏ i, b.1 i ∧ (∏ i, b.1 i) ≤ C * x ∧
      x ^ (1 / 2 - σ) ≤ ∏ i ∈ b.2.2.2, b.1 i ∧
      (∏ i ∈ b.2.2.2, b.1 i) ≤ x ^ (1 / 2 : ℝ)
  let C₀ : ℝ := max C ((2 : ℝ) ^ k)
  let X₀ : ℝ := Real.exp 100
  let M (x : ℝ) (b : ι) : ℝ :=
    if good x b then ∏ i ∈ b.2.2.2ᶜ, b.1 i else x ^ (1 / 2 : ℝ)
  let N (x : ℝ) (b : ι) : ℝ :=
    if good x b then ∏ i ∈ b.2.2.2, b.1 i else x ^ (1 / 2 : ℝ)
  let α (x : ℝ) (b : ι) : ℕ →₀ ℂ :=
    if good x b then (primeIntervalBoxAlgebra b.2.1 b.2.2.1 b.2.2.2ᶜ).coeff else 0
  let β (x : ℝ) (b : ι) : ℕ →₀ ℂ :=
    if good x b then (primeIntervalBoxAlgebra b.2.1 b.2.2.1 b.2.2.2).coeff else 0
  have hC₀ : 1 ≤ C₀ := hC.trans (le_max_left _ _)
  have hCC₀ : C ≤ C₀ := le_max_left _ _
  have htwoC₀ : (2 : ℝ) ^ k ≤ C₀ := le_max_right _ _
  have hX₀ : Real.exp 1 ≤ X₀ := Real.exp_le_exp.mpr (by norm_num)
  have hxOne (x : ℝ) (hx : X₀ ≤ x) : 1 ≤ x :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 100)).trans hx
  have hxPos (x : ℝ) (hx : X₀ ≤ x) : 0 < x :=
    zero_lt_one.trans_le (hxOne x hx)
  have hlog (x : ℝ) (hx : X₀ ≤ x) : 1 ≤ Real.log x := by
    have h := (Real.le_log_iff_exp_le (hxPos x hx)).mpr hx
    linarith
  have hYOne (x : ℝ) (hx : X₀ ≤ x) (b : ι) (hg : good x b) :
      ∀ i, 1 ≤ b.1 i := fun i =>
    (Real.one_le_rpow (hxOne x hx) hη.le).trans (hg.2.2.1 i).1
  have hscale : ∀ x : ℝ, X₀ ≤ x → ∀ b : ι,
      x / C₀ ≤ M x b * N x b ∧ M x b * N x b ≤ C₀ * x ∧
      x ^ (1 / 2 - σ) ≤ N x b ∧ N x b ≤ x ^ (1 / 2 : ℝ) := by
    intro x hx b
    by_cases hg : good x b
    · simp only [M, N, ite_eq_left hg]
      rw [Finset.prod_compl_mul_prod]
      exact ⟨(div_le_div_of_nonneg_left (hxPos x hx).le
          (zero_lt_one.trans_le hC) hCC₀).trans hg.2.2.2.2.1,
        hg.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right hCC₀ (hxPos x hx).le),
        hg.2.2.2.2.2.2⟩
    · simp only [M, N, ite_eq_right hg]
      have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
        rw [← Real.rpow_add (hxPos x hx)]
        norm_num
      rw [hsq]
      exact ⟨div_le_self (hxPos x hx).le hC₀,
        le_mul_of_one_le_left (hxPos x hx).le hC₀,
        Real.rpow_le_rpow_of_exponent_le (hxOne x hx) (by linarith), le_rfl⟩
  have hsupport : ∀ x : ℝ, X₀ ≤ x → ∀ b : ι,
      (∀ n ∈ (α x b).support, 1 * M x b ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * M x b) ∧
      (∀ n ∈ (β x b).support, 1 * N x b ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * N x b) := by
    intro x hx b
    by_cases hg : good x b
    · simp only [α, β, M, N, ite_eq_left hg, one_mul]
      have hbound (s : Finset (Fin k)) (n : ℕ)
          (hn : n ∈ (primeIntervalBoxAlgebra b.2.1 b.2.2.1 s).coeff.support) :
          (∏ i ∈ s, b.1 i) ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * ∏ i ∈ s, b.1 i := by
        obtain ⟨hlo, hhi⟩ := primeIntervalBoxAlgebra_support_bounds
          b.1 b.2.1 b.2.2.1 (hYOne x hx b hg) hg.2.2.2.1 s n hn
        exact ⟨hlo, hhi.trans (mul_le_mul_of_nonneg_right htwoC₀
          (Finset.prod_nonneg fun i _ => zero_le_one.trans (hYOne x hx b hg i)))⟩
      exact ⟨hbound _, hbound _⟩
    · constructor
      · intro n hn
        simp only [α, ite_eq_right hg, Finsupp.support_zero, Finset.notMem_empty] at hn
      · intro n hn
        simp only [β, ite_eq_right hg, Finsupp.support_zero, Finset.notMem_empty] at hn
  have hcoeff : ∀ x : ℝ, X₀ ≤ x → ∀ b : ι, ∀ n : ℕ,
      ‖α x b n‖ ≤ 1 * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ k ∧
      ‖β x b n‖ ≤ 1 * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ k := by
    intro x hx b n
    have hnorm (s : Finset (Fin k)) :
        ‖(primeIntervalBoxAlgebra b.2.1 b.2.2.1 s).coeff n‖ ≤
          1 * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ k := by
      have hpow : 1 ≤ (Real.log x) ^ k := one_le_pow₀ (hlog x hx)
      exact (primeIntervalBoxAlgebra_coeff_norm_le b.2.1 b.2.2.1 s n).trans
        (by simpa only [one_mul] using
          le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg _) _) hpow)
    by_cases hg : good x b
    · simpa only [α, β, ite_eq_left hg] using And.intro (hnorm b.2.2.2ᶜ) (hnorm b.2.2.2)
    · simp only [α, β, ite_eq_right hg, Finsupp.zero_apply, norm_zero, one_mul, and_self]
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (pow_nonneg (zero_le_one.trans (hlog x hx)) _)
  have hSW : ∀ A : ℝ, 0 < A →
      ∃ KSW XSW : ℝ, 0 < KSW ∧ X₀ ≤ XSW ∧
        ∀ x : ℝ, XSW ≤ x → ∀ b : ι,
        ∀ q r a : ℕ, 0 < q → 0 < r → Nat.Coprime a q →
          ‖fullDiscrepancy ((β x b).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            KSW * ((q * r).divisors.card : ℝ) ^ 1 * N x b /
              (Real.log x) ^ A := by
    intro A hA
    obtain ⟨KSW, XSW, hKSW, hXSW, hsw⟩ :=
      prime_interval_box_all_moduli_siegelWalfisz k η hη A hA
    refine ⟨KSW, XSW, hKSW, hXSW, ?_⟩
    intro x hx b q r a hq hr ha
    by_cases hg : good x b
    · simpa only [β, N, ite_eq_left hg, pow_one] using
        hsw x hx b.1 b.2.1 b.2.2.1 b.2.2.2 hg.1 hg.2.2.1 hg.2.2.2.1 q r a hq hr ha
    · simp only [β, N, ite_eq_right hg, Finsupp.filter_zero, fullDiscrepancy,
        progressionMass, reducedMass, Finsupp.support_zero, Finset.sum_empty,
        zero_div, sub_self, norm_zero]
      exact div_nonneg
        (mul_nonneg (mul_nonneg hKSW.le (pow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (hxPos x (hXSW.trans hx)).le _))
        (Real.rpow_nonneg (zero_le_one.trans (hlog x (hXSW.trans hx))) _)
  intro A hA
  obtain ⟨K, X, hK, hX, hdist⟩ :=
    hsource M N α β 1 C₀ 1 X₀ k 1 (by norm_num) hC₀ (by norm_num) hX₀
      hscale hsupport hcoeff hSW A hA
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx Y L U S hS hSproper hY hcuts hprodLo hprodHi hNlo hNhi I hI a ha
  let b : ι := (Y, L, U, S)
  have hg : good x b := ⟨hS, hSproper, hY, hcuts, hprodLo, hprodHi, hNlo, hNhi⟩
  have hd := hdist x hx b I hI a ha
  simpa only [α, β, ite_eq_left hg, b, primeIntervalBoxAlgebra_partition] using hd

#print axioms central_prime_box_typeII_coherent_log_saving_of_bilinear

end PrimeGap182Analytic.Harman
