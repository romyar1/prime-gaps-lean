import IncidenceFourContributions

/-!
# Four contributions for the original masked physical energy

This composes the proved outside-divisor, compatibility, frequency-sector,
and smooth-window estimates. The outside divisors and the exact coefficient
point and total bounds remain visible in the result.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators ContDiff

set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

def incidenceFourTerms (η Ebase esc q Λ w₂ Bcoeff E₀ τcoeff Harm : ℝ) (J : ℕ) : ℝ :=
  (2 * Ebase * esc + q ^ (1 / 2 + η) * J * Ebase + q ^ (1 / 2 + η) * (2 * esc)) *
    (τcoeff * E₀) +
    ((J : ℝ) * q ^ (3 / 2 + η)) * (6 * (Λ / w₂) * Bcoeff ^ 2) * Harm

theorem incidenceMaskedPhysical_four_contributions (hK4 : AllIncidenceRankFourBounds)
    (η c₀ R : ℝ) (hη : 0 < η) (hc₀ : 0 < c₀) (hR : 0 ≤ R)
    (Ap Ep : ℕ → ℝ) (hAp : ∀ j, 0 ≤ Ap j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ j y, |iteratedDeriv j ψ y| ≤ Ap j * (Real.log x) ^ Ep j) →
      ∀ q₀ g q w : ℕ, ∀ [NeZero q₀] [NeZero g] [NeZero q] [NeZero w],
      Nat.Coprime q₀ (g * q) → Nat.Coprime g q → Squarefree q →
      Nat.Coprime w (q₀ * (g * q)) →
      ∀ A B : ℤ, IsUnit (A : ZMod (q₀ * (g * q))) →
      ∀ w₂ : ℕ, 0 < w₂ → Nat.Coprime w₂ q → g ∣ w₂ →
      ∀ N esc Λ Ewidth d₀ L κ Ccard Bcoeff E₀ τcoeff τa τe Ddensity : ℝ,
      0 < N → 0 < esc → 0 < Λ → 0 < Ewidth →
      0 ≤ L → 0 ≤ κ → 0 ≤ Ccard → 0 ≤ Bcoeff →
      0 ≤ τcoeff → 0 ≤ τa → 0 ≤ τe → 1 ≤ Ddensity →
      ∀ D : Finset ℕ, ∀ ρ : ℕ → ℝ,
      (∀ e ∈ D, 0 ≤ ρ e ∧ ρ e ≤ L) →
      (∀ e ∈ D, e ≠ 0 ∧ Nat.Coprime e (q₀ * (g * q)) ∧ Nat.Coprime w e ∧
        Nat.Coprime w₂ e ∧ (e.divisors.card : ℝ) ≤ τe ∧
        |(w : ℝ) * (e : ℝ) - d₀| ≤ Ewidth ∧ c₀ * esc ≤ (e : ℝ) ∧ (e : ℝ) ≤ 2 * esc) →
      ∀ S : ZMod q₀ → Finset (ZMod q₀),
      (∀ r, IsUnit r → ((S r).card : ℝ) ≤ κ) →
      ∀ Freq : Finset ℤ,
      (∀ l ∈ Freq, (w₂ : ℤ) ∣ l ∧ Λ ≤ |(l : ℝ)| ∧ |(l : ℝ)| ≤ 2 * Λ ∧
        IsUnit ((l / (w₂ : ℤ) : ℤ) : ZMod q)) →
      (∀ l ∈ Freq, (l.natAbs.divisors.card : ℝ) ≤ τcoeff) →
      (∀ t ∈ incidenceRowDivisors D, ∀ a ∈ incidenceDividedCoefficientSet Freq (t * w₂),
        (a.natAbs.divisors.card : ℝ) ≤ τa) →
      ∀ coeff : ℤ → ℂ, (∀ l ∈ Freq, ‖coeff l‖ ≤ Bcoeff) →
      (∑ l ∈ Freq, ‖coeff l‖ ^ 2) ≤ E₀ →
      ∀ I : Finset ℤ, (∀ n : ℤ, ψ ((n : ℝ) / N) ≠ 0 → n ∈ I) →
      ∀ Js : ℕ → ℕ,
      (∀ c ∈ w.divisors, 0 < Js c ∧
        Λ ≤ (Js c : ℝ) * (N / ((c : ℝ) * (q₀ : ℝ) * esc))) →
      let V₀ : ℕ → ℝ := fun c => (R / c₀ + 2) * (N / ((c : ℝ) * (q₀ : ℝ) * esc))
      (∀ c ∈ w.divisors, ∀ t ∈ incidenceRowDivisors D,
        (Λ / ((t * w₂ : ℕ) : ℝ)) * V₀ c ≤ Ddensity * (q : ℝ)) →
      (∀ c ∈ w.divisors, ∀ t ∈ incidenceRowDivisors D,
        ((incidenceDividedCoefficientSet Freq (t * w₂)).card : ℝ) ≤ Ccard * V₀ c) →
      (∑ e ∈ D, ρ e * incidencePhysicalEnergyOrZero
        (m := q₀ * (g * q)) (w := w) e A B Freq I coeff
          (fun n => if (n : ZMod q₀) ∈ S (e : ZMod q₀)
            then (ψ ((n : ℝ) / N) : ℂ) else 0)) ≤
      (w.divisors.card : ℝ) * κ * τe *
        ((q₀ : ℝ) * κ * ((1 + x ^ (2 * η)) * K * L) *
          (9 * Ddensity * (Ccard + 8 * τa))) *
        ∑ c ∈ w.divisors, V₀ c *
          incidenceFourTerms η (Ewidth / ((w : ℝ) * (q₀ : ℝ))) esc q
            Λ w₂ Bcoeff E₀ τcoeff (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) (Js c) := by
  obtain ⟨K, hK, hwindow⟩ :=
    incidenceOriginalProgression_four_contributions hK4 η c₀ R hη hc₀ hR Ap Ep hAp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hwindow, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro ψ hψ hsψ hder q₀ g q w _ _ _ _ h0 hg hq hwm A B hA w₂ hw₂ hwq hgw
    N esc Λ Ewidth d₀ L κ Ccard Bcoeff E₀ τcoeff τa τe Ddensity
    hN hesc hΛ hEwidth hL hκ hCcard hBcoeff hτcoeff hτa hτe hDdensity
    D ρ hρ hD S hS Freq hFreq hdivisors hτ coeff hcoeff henergy I hsI Js hJs
    V₀ hdensity hcard
  have hwR : 0 < (w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne w)
  have hq₀m : q₀ ∣ q₀ * (g * q) := dvd_mul_right _ _
  have hqm : q ∣ q₀ * (g * q) := (dvd_mul_left q g).trans (dvd_mul_left _ _)
  have hb := incidencePhysicalWeighted_masked_to_progression hwm hq₀m w₂ A B Freq I
    (fun l hl => (hFreq l hl).1) S κ τe hκ hτe hS D ρ (fun e he => (hρ e he).1)
    (fun e he => ⟨(hD e he).1, (hD e he).2.1, (hD e he).2.2.1,
      (hD e he).2.2.2.1, (hD e he).2.2.2.2.1⟩)
    coeff (fun n => (ψ ((n : ℝ) / N) : ℂ))
    (fun n hn => hsI n (fun hz => hn (by rw [hz, Complex.ofReal_zero])))
  apply hb.trans
  calc
    _ ≤ (w.divisors.card : ℝ) * κ * τe *
        ∑ c ∈ w.divisors.attach,
          (q₀ : ℝ) * κ * ((1 + x ^ (2 * η)) * K * L) *
            (9 * Ddensity * (Ccard + 8 * τa) * V₀ c.1 *
              incidenceFourTerms η (Ewidth / ((w : ℝ) * (q₀ : ℝ))) esc q
                Λ w₂ Bcoeff E₀ τcoeff (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) (Js c.1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro c _
      have hcw : c.1 ∣ w := Nat.dvd_of_mem_divisors c.2
      have hc : 0 < (c.1 : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors c.2
      let uc : (ZMod (q₀ * (g * q)))ˣ := ZMod.unitOfCoprime c.1 (hwm.of_dvd_left hcw)
      let vc : (ZMod q₀)ˣ := ZMod.unitOfCoprime c.1 ((hwm.of_dvd_left hcw).of_dvd_right hq₀m)
      let z : ZMod (q₀ * (g * q)) := (A : ZMod _) * ((uc⁻¹ : (ZMod _)ˣ) : ZMod _)
      let Ac : ℤ := z.val
      have hAc : (Ac : ZMod (q₀ * (g * q))) = z := by
        simp only [Ac, Int.cast_natCast, ZMod.natCast_zmod_val]
      have hAcm : IsUnit (Ac : ZMod (q₀ * (g * q))) := by
        rw [hAc]
        exact hA.mul (uc⁻¹).isUnit
      have hh := hx ψ hψ hsψ hder q₀ g q h0 hg hq Ac
        (B * ((w / c.1 : ℕ) : ℤ)) (incidenceIntegerUnit_of_dvd hqm Ac hAcm)
        w₂ hw₂ hwq hgw N c.1 esc Λ Ewidth w d₀ L κ Ccard Bcoeff E₀ τcoeff τa Ddensity
        hN hc hesc hΛ hEwidth hwR hL hκ hCcard hBcoeff hτcoeff hτa hDdensity
        (Js c.1) (hJs c.1 c.2).1 (hJs c.1 c.2).2 D ρ hρ
        (fun e he => ⟨(hD e he).2.1.of_dvd_right (dvd_mul_left _ _),
          (hD e he).2.2.2.2.2⟩)
        (incidenceAllCompatibilityLines vc S)
        (incidenceAllCompatibilityLines_card vc S κ hκ hS)
        Freq (fun l hl => (hFreq l hl).2) hdivisors hτ coeff hcoeff henergy
        (hdensity c.1 c.2) (hcard c.1 c.2)
      simpa only [hAc, z, uc, vc, incidenceFourTerms, V₀,
        Int.cast_mul, Int.cast_natCast] using hh
    _ = _ := by
      rw [← Finset.sum_attach w.divisors (fun c => V₀ c *
        incidenceFourTerms η (Ewidth / ((w : ℝ) * (q₀ : ℝ))) esc q
          Λ w₂ Bcoeff E₀ τcoeff (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) (Js c))]
      conv_lhs => rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceMaskedPhysical_four_contributions
