import SharpMinorantAssembly182
import HarmanThetaAssembly182
import HarmanCentralDistribution182
import HarmanT3Subpower182
import HarmanEligibleDistribution182
import SieveSourceTransfer182

/-! The actual sharp minorant on the exact dense source moduli. All twelve
literal Buchstab pieces, including the two eligible remainders and their
collision errors, are estimated by proved component theorems. The explicit
intermediate inputs are the bilinear and new Type III estimates at one
positive parameter retreat; no component distribution is postulated. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic

open Harman

theorem selbergClosedSequence182_sharp_residuals (x : ℝ) :
    selbergClosedSequence182 1 x =
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, Finsupp.single n
        (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
          sharpResidualCount x 1 n : ℝ) : ℂ) := by
  classical
  unfold selbergClosedSequence182
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  dsimp [selbergWeight182]
  rw [sharpMinorant_eq_two_residuals]

theorem closedMinorantSource_of_analytic_inputs
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ (1 / 10 ^ 10 : ℝ))
    (j : ℕ) (hj : 1 ≤ j) («ω» δ σdist σIII : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσclass : (1 / 2 : ℝ) - 41361 / 100000 + τ < σdist)
    (hσhalf : σdist < 1 / 2) (hσIIIhi : σIII < 2159 / 25000 - τ)
    (hlevel : (1 / 2 : ℝ) + 2 * «ω» < 53 / 100)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 12 ∧
      PrimeGap182.TypeIII.PositiveSmoothTypeIIIGlobalEstimate («ω» + r) (δ + r) σIII ∧
      (1 / 4 : ℝ) + 7 * («ω» + r) + 2 * (δ + r) < 34941 / 100000 - τ ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σdist)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ClosedSourceLogSaving182 1 j «ω» δ L0 := by
  classical
  obtain ⟨r, hr, hru, hIII, hsmooth, hbilinear⟩ := hretreat
  have hretθ : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 12 ∧
      (1 / 4 : ℝ) + 7 * («ω» + r) + 2 * (δ + r) < 34941 / 100000 - τ ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σdist :=
    ⟨r, hr, hru, hsmooth, hbilinear⟩
  have hretc : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σdist :=
    ⟨r, hr, by linarith only [hru], hbilinear⟩
  have hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σdist := by
    linarith only [hτ, hσclass]
  intro A hA
  obtain ⟨Kθ, Xθ, hKθ, _hXθ, hθ⟩ :=
    siftedTheta_coherent_distribution_of_bilinear τ hτ hτsmall j hj «ω» δ σdist
      hω hδ hσclass hretθ L0 hL0 hL0sub A hA
  obtain ⟨KL, XL, hKL, _hXL, hL⟩ :=
    sourceLargeFirst_coherent_log_saving_of_bilinear j «ω» δ σdist hω hδ hσgap
      hretc L0 hL0 hL0sub A hA
  obtain ⟨KC, XC, hKC, _hXC, hC⟩ :=
    sourceCentralPair_coherent_log_saving_of_bilinear j «ω» δ σdist hω hδ hσgap
      hretc L0 hL0 hL0sub A hA
  obtain ⟨KT, XT, hKT, _hXT, hT⟩ :=
    sourceT3_subpower_coherent_log_saving_of_analytic_inputs τ hτ hτsmall j hj
      «ω» δ σdist σIII hω hδ hσclass hσhalf hσIIIhi
      ⟨r, hr, hru, hIII, hsmooth, hbilinear⟩ L0 hL0 hL0sub A hA
  obtain ⟨K4, X4, hK4, _hX4, h4⟩ :=
    sourceT4_sub_sourceU1_coherent_log_saving_of_bilinear j «ω» δ σdist hω hδ hσgap
      hretc L0 hL0 hL0sub A hA
  obtain ⟨K5, X5, hK5, _hX5, h5⟩ :=
    sourceFive_sub_sharpResidual_coherent_log_saving_of_bilinear j «ω» δ σdist
      hω hδ hlevel hσgap hretc L0 hL0 hL0sub A hA
  have hparts : ∀ i : Fin 12, ∃ K X : ℝ, 0 < K ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sharpBuchstabPiece x i n : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧ Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
    intro i
    fin_cases i
    · exact ⟨Kθ, Xθ, hKθ, fun x hx Y hY I hI a ha => hθ x hx 0 Y hY I hI a ha⟩
    · exact ⟨Kθ, Xθ, hKθ, fun x hx Y hY I hI a ha => hθ x hx 1 Y hY I hI a ha⟩
    · exact ⟨Kθ, Xθ, hKθ, fun x hx Y hY I hI a ha => hθ x hx 2 Y hY I hI a ha⟩
    · exact ⟨Kθ, Xθ, hKθ, fun x hx Y hY I hI a ha => hθ x hx 3 Y hY I hI a ha⟩
    · exact ⟨Kθ, Xθ, hKθ, fun x hx Y hY I hI a ha => hθ x hx 4 Y hY I hI a ha⟩
    · exact ⟨KL, XL, hKL, hL⟩
    · exact ⟨KC, XC, hKC, hC⟩
    · exact ⟨KT, XT, hKT, hT⟩
    · exact ⟨K5, X5, hK5, fun x hx Y hY I hI a ha => h5 x hx 0 Y hY I hI a ha⟩
    · exact ⟨K4, X4, hK4, h4⟩
    · exact ⟨Kθ, Xθ, hKθ, fun x hx Y hY I hI a ha => hθ x hx 5 Y hY I hI a ha⟩
    · exact ⟨K5, X5, hK5, fun x hx Y hY I hI a ha => h5 x hx 1 Y hY I hI a ha⟩
  obtain ⟨K, X, hK, hX, hb⟩ :=
    sharp_minorant_log_saving_of_twelve_components j «ω» δ A L0 hparts
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx I hI a ha
  have hx1 : 1 < x := hX.trans_le hx
  let Y : Set.Ici (1 : ℝ) := ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩
  have hY : (Y : ℝ) = x ^ δ :=
    max_eq_right (Real.one_le_rpow hx1.le hδ.le)
  have hb := hb x hx Y hY I hI a ha
  simpa only [sourceModuli182, selbergClosedSequence182_sharp_residuals, Y] using hb

#print axioms selbergClosedSequence182_sharp_residuals
#print axioms closedMinorantSource_of_analytic_inputs

end PrimeGap182Analytic
