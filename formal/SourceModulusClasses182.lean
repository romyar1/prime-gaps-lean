import SourceDenseData182

/-! Exact source classes used by the six actual moment pairings. Prime
weights use the old ladder, sharp minorants the new ladder, and defects
only the common and subtraction sources. Presieving is absorbed by the
strict difference between the recorded and physical radial scales. -/

noncomputable section
open PrimeGap186

namespace PrimeGap182

def trialPresieveExponent : ℚ := 1 / 10000000000
def trialBaseModulusExponent : ℚ := 4999999 / 10000000

def TrialDenseModulus182 (density : ℕ) («ω» δ : ℚ) (x : ℝ) (q : ℕ) : Prop :=
  (q : ℝ) ≤ x ^ ((1 / 2 : ℝ) + 2 * («ω» : ℝ)) ∧
    Nonempty (DenseDivisibilityWitness
      ⟨max 1 (x ^ (δ : ℝ)), by exact le_max_left 1 (x ^ (δ : ℝ))⟩ density q)

def TrialSupportedModulus182 (w : Fin 3) (x : ℝ) (q : ℕ) : Prop :=
  (q : ℝ) ≤ x ^ (trialBaseModulusExponent : ℝ) ∨
    (w = 0 ∧ ∃ row ∈ trialOldSourceRows, TrialDenseModulus182 row.order row.omega row.delta x q) ∨
    (w = 1 ∧ ∃ row ∈ trialNewSourceRows, TrialDenseModulus182 row.order row.omega row.delta x q) ∨
    TrialDenseModulus182 2 trialCommonSourceOmega trialCommonSourceDelta x q ∨
    TrialDenseModulus182 2 trialSubtractionSourceRow.omega trialSubtractionSourceRow.delta x q

def TrialPresieveRetreat (B ξ «ω» δ : ℚ) : Prop :=
  trialPresieveExponent ≤ trialRhoStar * ξ ∧ trialRhoStar * ξ ≤ δ ∧
    trialPresieveExponent + trialRhoStar * B < 1 / 2 + 2 * «ω»

instance (B ξ «ω» δ : ℚ) : Decidable (TrialPresieveRetreat B ξ «ω» δ) := by
  unfold TrialPresieveRetreat
  infer_instance

set_option maxRecDepth 4096 in
theorem trialSourceRows_presieve_retreat : ∀ ν : Fin 2, ∀ row ∈ trialSourceRows ν,
    TrialPresieveRetreat row.upperBand row.activation row.omega row.delta := by
  decide +kernel

theorem trialOtherSources_presieve_retreat :
    TrialPresieveRetreat (2 * trialEnlargedRadius) (trialCommonSourceDelta / trialRho)
      trialCommonSourceOmega trialCommonSourceDelta ∧
    TrialPresieveRetreat trialSubtractionSourceRow.upperBand trialSubtractionSourceRow.activation
      trialSubtractionSourceRow.omega trialSubtractionSourceRow.delta ∧
    trialPresieveExponent + trialRhoStar * ((1 / 2) / trialRho) < trialBaseModulusExponent ∧
    trialBaseModulusExponent < 1 / 2 ∧ 0 < trialPresieveExponent := by
  decide +kernel

theorem trialDenseModulus_presieve (density : ℕ) (B ξ «ω» δ : ℚ)
    (hg : TrialPresieveRetreat B ξ «ω» δ) (x : ℝ) (hx : 1 < x)
    (W D E : ℕ) (hW : 0 < W) (hWs : (W : ℝ) ≤ x ^ (trialPresieveExponent : ℝ))
    (hDW : D.Coprime W) (hEW : E.Coprime W)
    (hd : ∃ hξ : 1 ≤ (x ^ (trialRhoStar : ℝ)) ^ (ξ : ℝ),
      Nonempty (DenseDivisibilityWitness
        ⟨(x ^ (trialRhoStar : ℝ)) ^ (ξ : ℝ), hξ⟩ density (D.lcm E)))
    (hsize : (D.lcm E : ℝ) ≤ (x ^ (trialRhoStar : ℝ)) ^ (B : ℝ)) :
    TrialDenseModulus182 density «ω» δ x (W.lcm (D.lcm E)) := by
  obtain ⟨hξ, hd⟩ := hd
  have hWY : (W : ℝ) ≤ (x ^ (trialRhoStar : ℝ)) ^ (ξ : ℝ) := by
    rw [← Real.rpow_mul (zero_le_one.trans hx.le)]
    exact hWs.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by exact_mod_cast hg.1))
  have hpresieve := denseDivisibility_presieve_lcm hd hW hWY hDW hEW
  have hcop : W.Coprime (D.lcm E) :=
    (hDW.symm.mul_right hEW.symm).coprime_dvd_right (Nat.lcm_dvd_mul D E)
  constructor
  · calc
      (W.lcm (D.lcm E) : ℝ) = (W : ℝ) * (D.lcm E : ℝ) := by
        rw [hcop.lcm_eq_mul, Nat.cast_mul]
      _ ≤ x ^ (trialPresieveExponent : ℝ) * (x ^ (trialRhoStar : ℝ)) ^ (B : ℝ) :=
        mul_le_mul hWs hsize (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx.le) _)
      _ = x ^ ((trialPresieveExponent : ℝ) + (trialRhoStar : ℝ) * (B : ℝ)) := by
        rw [← Real.rpow_mul (zero_le_one.trans hx.le), Real.rpow_add (zero_lt_one.trans hx)]
      _ ≤ x ^ ((1 / 2 : ℝ) + 2 * («ω» : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by
          have hh : ((trialPresieveExponent + trialRhoStar * B : ℚ) : ℝ) ≤
              ((1 / 2 + 2 * «ω» : ℚ) : ℝ) := by exact_mod_cast hg.2.2.le
          norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hh
          exact hh)
  · apply denseDivisibility_mono_scale _ hpresieve
    change (x ^ (trialRhoStar : ℝ)) ^ (ξ : ℝ) ≤ max 1 (x ^ (δ : ℝ))
    rw [← Real.rpow_mul (zero_le_one.trans hx.le)]
    exact (Real.rpow_le_rpow_of_exponent_le hx.le (by exact_mod_cast hg.2.1)).trans
      (le_max_right _ _)

theorem trialBaseModulus_presieve (x : ℝ) (hx : 1 < x) (W N : ℕ)
    (hW : 0 < W) (hN : 0 < N) (hWs : (W : ℝ) ≤ x ^ (trialPresieveExponent : ℝ))
    (hs : (N : ℝ) ≤ (x ^ (trialRhoStar : ℝ)) ^ (((1 / 2) / trialRho : ℚ) : ℝ)) :
    (W.lcm N : ℝ) ≤ x ^ (trialBaseModulusExponent : ℝ) := by
  calc
    (W.lcm N : ℝ) ≤ (W : ℝ) * (N : ℝ) := by exact_mod_cast Nat.lcm_le_mul hW hN
    _ ≤ x ^ (trialPresieveExponent : ℝ) *
        (x ^ (trialRhoStar : ℝ)) ^ (((1 / 2) / trialRho : ℚ) : ℝ) :=
      mul_le_mul hWs hs (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx.le) _)
    _ = x ^ ((trialPresieveExponent : ℝ) +
        (trialRhoStar : ℝ) * (((1 / 2) / trialRho : ℚ) : ℝ)) := by
      rw [← Real.rpow_mul (zero_le_one.trans hx.le), Real.rpow_add (zero_lt_one.trans hx)]
    _ ≤ x ^ (trialBaseModulusExponent : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx.le (by
        exact_mod_cast trialOtherSources_presieve_retreat.2.2.1.le)

#print axioms trialSourceRows_presieve_retreat
#print axioms trialOtherSources_presieve_retreat
#print axioms trialDenseModulus_presieve
#print axioms trialBaseModulus_presieve

end PrimeGap182
