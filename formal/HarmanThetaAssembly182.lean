import HarmanShortAnalytic182
import HarmanLongDistribution182

/-! Full discrepancy of the six literal new sifted-theta weights. Both
the short and long branches are supplied by proved estimates at the
new cutoffs. The only intermediate analytic premise is the bilinear
estimate at a positive parameter retreat. Adapted from Apache-2.0
PrimeGaps186 at the pinned hash in the generator. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186
namespace PrimeGap182Analytic.Harman

open Classical in
theorem siftedTheta_coherent_distribution_of_bilinear
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10)
    (j : ℕ) (hj : 1 ≤ j) («ω» δ σdist : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσclass : (1 / 2 : ℝ) - 41361 / 100000 + τ < σdist)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 12 ∧
      (1 / 4 : ℝ) + 7 * («ω» + r) + 2 * (δ + r) < 34941 / 100000 - τ ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σdist)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ l : Fin 6,
      ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
      let ρx : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n ((siftedTheta x l (fun _ => 1) n : ℝ) : ℂ)
      let Q : Finset ℕ :=
        (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter
          (fun q => q ∣ ∏ p ∈ I, p ∧
            Nonempty (DenseDivisibilityWitness Y j q))
      (∑ q ∈ Q, ‖fullDiscrepancy ρx q a‖) ≤ K * x / (Real.log x) ^ A := by
  let σ : ℝ := 1 / 2 - 41361 / 100000 + τ
  have hσ : 0 < σ := by dsimp only [σ]; linarith only [hτ]
  have hσa : (1 / 2 : ℝ) - σ < 41361 / 100000 := by
    dsimp only [σ]
    linarith only [hτ]
  obtain ⟨r, hr, hωupper, hsmooth, hbilinear⟩ := hretreat
  have hσhalf : σ < 1 / 2 := by dsimp only [σ]; linarith only [hτsmall]
  have hbilinear' : SourceBilinearEstimate j («ω» + r) (δ + r) σ :=
    hbilinear.mono_sigma hσclass.le
  have hlevel : (1 / 2 : ℝ) + 2 * («ω» + r) < 58639 / 100000 - τ := by
    linarith only [hsmooth, hδ, hr, hτsmall]
  obtain ⟨Xr, hXr⟩ := eventually_atTop.mp
    (central_subpower_modulus_family_subset j «ω» δ r hr L0 hL0 hL0sub)
  intro A hA
  obtain ⟨Ks, Xs, hKs, hXs, hs⟩ :=
    sifted_short_subpower_coherent_log_saving_of_bilinear τ hτ hτsmall j hj «ω» δ hω hδ
      ⟨r, hr, hlevel, hsmooth, hbilinear'⟩ L0 hL0 hL0sub A hA
  obtain ⟨Kl, Xl, hKl, _hXl, hl⟩ :=
    sifted_long_pure_power_distribution_of_bilinear j («ω» + r) (δ + r) σ
      (by linarith) (by linarith) hσ (by linarith only [hωupper]) hσhalf hσa hbilinear' A hA
  refine ⟨Ks + Kl, max Xs (max Xl Xr), by positivity,
    hXs.trans_le (le_max_left _ _), ?_⟩
  intro x hx l Y hY I hI a ha ρx Q
  have hxs : Xs ≤ x := (le_max_left _ _).trans hx
  have hxl : Xl ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxr : Xr ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  let z : ℝ := x ^ ((8639 : ℝ) / 50000)
  let M0 : ℝ := x ^ (1 - (34941 : ℝ) / 100000)
  let S0 : ArithmeticFunction ℝ :=
    ⟨fun n => if (n : ℝ) ≤ M0 then
      ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0, by simp⟩
  let short : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    Finsupp.single n
      (((S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
  let long : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    Finsupp.single n
      ((siftedTheta x l (fun _ => 1) n -
        (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
  have hshort : (∑ q ∈ Q, ‖fullDiscrepancy short q a‖) ≤
      Ks * x / (Real.log x) ^ A := hs x hxs l Y hY I hI a ha
  have hlong : (∑ q ∈ Q, ‖fullDiscrepancy long q a‖) ≤
      Kl * x / (Real.log x) ^ A := by
    have hsubset := hXr x hxr Y hY I
    have hbound := hl x hxl l I hI a ha
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q _ _ => norm_nonneg (fullDiscrepancy long q a))).trans hbound
  have hsplit : ρx = short + long := by
    change (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n ((siftedTheta x l (fun _ => 1) n : ℝ) : ℂ)) =
        (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n
            (((S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)) +
        (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n
            ((siftedTheta x l (fun _ => 1) n -
              (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Finsupp.single_add]
    congr 1
    push_cast
    ring
  have hmask (P : ℕ → Prop) [DecidablePred P] :
      (short + long).sum (fun n c => if P n then c else (0 : ℂ)) =
        short.sum (fun n c => if P n then c else (0 : ℂ)) +
          long.sum (fun n c => if P n then c else (0 : ℂ)) := by
    apply Finsupp.sum_add_index'
    · intro n
      simp
    · intro n c d
      by_cases hp : P n <;> simp [hp]
  have hdiscrepancy (q : ℕ) :
      fullDiscrepancy ρx q a =
        fullDiscrepancy short q a + fullDiscrepancy long q a := by
    rw [hsplit]
    have hp := hmask (fun n => n % q = a % q)
    have hr := hmask (fun n => Nat.Coprime n q)
    simp only [Finsupp.sum] at hp hr
    simp only [fullDiscrepancy, progressionMass, reducedMass, hp, hr, add_div]
    ring
  calc
    (∑ q ∈ Q, ‖fullDiscrepancy ρx q a‖) ≤
        ∑ q ∈ Q, (‖fullDiscrepancy short q a‖ + ‖fullDiscrepancy long q a‖) := by
      apply Finset.sum_le_sum
      intro q _
      rw [hdiscrepancy]
      exact norm_add_le _ _
    _ = (∑ q ∈ Q, ‖fullDiscrepancy short q a‖) +
        (∑ q ∈ Q, ‖fullDiscrepancy long q a‖) := Finset.sum_add_distrib
    _ ≤ Ks * x / (Real.log x) ^ A + Kl * x / (Real.log x) ^ A :=
      add_le_add hshort hlong
    _ = (Ks + Kl) * x / (Real.log x) ^ A := by ring

#print axioms siftedTheta_coherent_distribution_of_bilinear

end PrimeGap182Analytic.Harman
