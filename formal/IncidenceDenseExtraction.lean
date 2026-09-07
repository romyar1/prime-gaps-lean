import IncidenceFrequencyCoefficients

/-!
# Coefficient-dependent dense extraction

The short factor is selected at the actual target N/(q₀² x^(50ε) H²).
The target is allowed to depend on the original frequency radius. The
available dense-divisibility witness is the baseline's recursive witness,
not a new assumed divisor-selection principle.
-/

noncomputable section

namespace PrimeGap182Audit

open PrimeGap186

def incidenceCoefficientTarget (N q H x ε : ℝ) : ℝ :=
  N / (q ^ 2 * x ^ (50 * ε) * H ^ 2)

/-- Elementary legality of the coefficient-dependent target, retaining
the full retreat relative to the original source factor. -/
theorem incidenceCoefficientTarget_le (N R q H x ε : ℝ)
    (hR : 0 < R) (hq : 0 < q) (hH : 0 < H) (hx : 0 < x)
    (hscale : R * (x ^ ε) ^ 2 ≤ N)
    (hfrequency : N ≤ R * x ^ ε * (q * H)) :
    incidenceCoefficientTarget N q H x ε ≤ R / x ^ (50 * ε) := by
  have hE : 0 < x ^ ε := Real.rpow_pos_of_pos hx ε
  have hEB : x ^ ε ≤ q * H := by
    have hp : 0 < R * x ^ ε := mul_pos hR hE
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hscale, hfrequency]
  have hNR : N ≤ R * (q * H) ^ 2 :=
    hfrequency.trans (by
      have hm := mul_le_mul_of_nonneg_left hEB (mul_pos hR (mul_pos hq hH)).le
      nlinarith only [hm])
  have hx50 : 0 < x ^ (50 * ε) := Real.rpow_pos_of_pos hx _
  unfold incidenceCoefficientTarget
  apply (div_le_div_iff₀ (by positivity) hx50).mpr
  nlinarith [mul_le_mul_of_nonneg_right hNR hx50.le]

theorem incidenceCoefficientTarget_one_le (N q H x ε ω δ γ : ℝ)
    (hx : 1 ≤ x) (hq : 0 < q) (hH : 0 < H)
    (hHbound : q * H ≤ x ^ (4 * ω + δ)) (hNbound : x ^ γ ≤ N)
    (hexponent : 8 * ω + 2 * δ + 50 * ε ≤ γ) :
    1 ≤ incidenceCoefficientTarget N q H x ε := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hden : 0 < q ^ 2 * x ^ (50 * ε) * H ^ 2 := by positivity
  unfold incidenceCoefficientTarget
  apply (le_div_iff₀ hden).mpr
  simp only [one_mul]
  calc
    _ = (q * H) ^ 2 * x ^ (50 * ε) := by ring
    _ ≤ (x ^ (4 * ω + δ)) ^ 2 * x ^ (50 * ε) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_pos hq hH).le hHbound 2) (by positivity)
    _ = x ^ (8 * ω + 2 * δ + 50 * ε) := by
      rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
      congr 1
      ring
    _ ≤ x ^ γ := Real.rpow_le_rpow_of_exponent_le hx hexponent
    _ ≤ N := hNbound

/-- Actual order-three extraction at the coefficient-dependent target.
Both retained factors keep an order-one dense-divisibility witness. -/
theorem incidenceCoefficientTarget_extract
    (Y : Set.Ici (1 : ℝ)) (R : ℕ)
    (hR : Nonempty (DenseDivisibilityWitness Y 3 R))
    (N q H x ε ω δ γ : ℝ) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hq : 0 < q) (hH : 0 < H)
    (hscale : (R : ℝ) * (x ^ ε) ^ 2 ≤ N)
    (hfrequency : N ≤ (R : ℝ) * x ^ ε * (q * H))
    (hHbound : q * H ≤ x ^ (4 * ω + δ)) (hNbound : x ^ γ ≤ N)
    (hexponent : 8 * ω + 2 * δ + 50 * ε ≤ γ) :
    ∃ u Δ : ℕ, R = u * Δ ∧
      Nonempty (DenseDivisibilityWitness Y 1 u) ∧
      Nonempty (DenseDivisibilityWitness Y 1 Δ) ∧
      incidenceCoefficientTarget N q H x ε / (Y : ℝ) ≤ Δ ∧
      (Δ : ℝ) ≤ incidenceCoefficientTarget N q H x ε ∧
      (Δ : ℝ) ≤ (R : ℝ) / x ^ (50 * ε) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hN : 0 < N := (Real.rpow_pos_of_pos hx0 γ).trans_le hNbound
  have hRpos : (0 : ℝ) < R := by exact_mod_cast denseDivisibility_pos hR
  have hupper := incidenceCoefficientTarget_le N R q H x ε hRpos hq hH hx0
    hscale hfrequency
  have hlower := incidenceCoefficientTarget_one_le N q H x ε ω δ γ hx hq hH
    hHbound hNbound hexponent
  have hpow : 1 ≤ x ^ (50 * ε) := Real.one_le_rpow hx (by positivity)
  have hupperR : incidenceCoefficientTarget N q H x ε ≤ (R : ℝ) :=
    hupper.trans (div_le_self hRpos.le hpow)
  have htarget : incidenceCoefficientTarget N q H x ε ≤ (Y : ℝ) * R :=
    hupperR.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right Y.property hRpos.le)
  obtain ⟨u, Δ, hprod, hu, hΔ, hlo, hhi⟩ :=
    (denseDivisibility_succ_iff.mp hR).2 1 1 (by norm_num)
      (incidenceCoefficientTarget N q H x ε) hlower htarget
  exact ⟨u, Δ, hprod, hu, hΔ, hlo, hhi, hhi.trans hupper⟩

/-- The new strict region supplies simultaneous positive margins for
the source range, reciprocal collision term, all three complete-mode
errors, the divided row scale, and the legal extraction lower bound. -/
theorem incidenceTypeII_positive_margins (ω δ γlo γhi : ℝ)
    (hω : 0 < ω) (hδ : 0 < δ)
    (hsource : 12 * ω + 6 * δ < γlo)
    (hupper : γhi < 1 / 2 - 2 * ω)
    (hfarey : 2 * γhi + 4 * ω + 2 * δ < 1)
    (hrow : 16 * ω + 7 * δ < γlo)
    (hosc : 3 / 2 + 40 * ω + 16 * δ < 5 * γlo) :
    ∃ ε : ℝ, 0 < ε ∧
      12 * ω + 6 * δ + 1000 * ε < γlo ∧
      γhi + 1000 * ε < 1 / 2 - 2 * ω ∧
      2 * γhi + 4 * ω + 2 * δ + 1000 * ε < 1 ∧
      16 * ω + 7 * δ + 1000 * ε < γlo ∧
      3 / 2 + 40 * ω + 16 * δ + 1000 * ε < 5 * γlo ∧
      1 / 2 + 16 * ω + 6 * δ + 1000 * ε < 2 * γlo ∧
      8 * ω + 2 * δ + 50 * ε < γlo := by
  have hlast : 1 / 2 + 16 * ω + 6 * δ < 2 * γlo := by linarith
  have hextract : 8 * ω + 2 * δ < γlo := by linarith
  let a := min (γlo - (12 * ω + 6 * δ))
    (min (1 / 2 - 2 * ω - γhi)
      (min (1 - (2 * γhi + 4 * ω + 2 * δ))
        (min (γlo - (16 * ω + 7 * δ))
          (min (5 * γlo - (3 / 2 + 40 * ω + 16 * δ))
            (min (2 * γlo - (1 / 2 + 16 * ω + 6 * δ))
              (γlo - (8 * ω + 2 * δ)))))))
  have ha : 0 < a := by
    dsimp only [a]
    simp only [lt_min_iff, sub_pos]
    exact ⟨hsource, hupper, hfarey, hrow, hosc, hlast, hextract⟩
  have hb : a ≤ γlo - (12 * ω + 6 * δ) ∧
      a ≤ 1 / 2 - 2 * ω - γhi ∧
      a ≤ 1 - (2 * γhi + 4 * ω + 2 * δ) ∧
      a ≤ γlo - (16 * ω + 7 * δ) ∧
      a ≤ 5 * γlo - (3 / 2 + 40 * ω + 16 * δ) ∧
      a ≤ 2 * γlo - (1 / 2 + 16 * ω + 6 * δ) ∧
      a ≤ γlo - (8 * ω + 2 * δ) := by
    have hb : a ≤ min (γlo - (12 * ω + 6 * δ))
        (min (1 / 2 - 2 * ω - γhi)
          (min (1 - (2 * γhi + 4 * ω + 2 * δ))
            (min (γlo - (16 * ω + 7 * δ))
              (min (5 * γlo - (3 / 2 + 40 * ω + 16 * δ))
                (min (2 * γlo - (1 / 2 + 16 * ω + 6 * δ))
                  (γlo - (8 * ω + 2 * δ))))))) := le_refl a
    simpa only [le_min_iff] using hb
  refine ⟨a / 2000, by positivity, ?_⟩
  rcases hb with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

#print axioms incidenceCoefficientTarget_le
#print axioms incidenceCoefficientTarget_one_le
#print axioms incidenceCoefficientTarget_extract
#print axioms incidenceTypeII_positive_margins

end PrimeGap182Audit
