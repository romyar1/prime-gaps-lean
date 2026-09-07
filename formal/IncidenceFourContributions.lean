import IncidenceMaskedOriginal
import IncidenceSectorSummation

/-!
# Four explicit contributions from the original progression energy

The coefficient norm and total squared mass are kept separate. The
actual dyadic sets determine the short oscillatory mass; no ambient
operator norm replaces them.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators ContDiff

set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem incidenceOriginalProgression_four_contributions (hK4 : AllIncidenceRankFourBounds)
    (η c₀ R : ℝ) (hη : 0 < η) (hc₀ : 0 < c₀) (hR : 0 ≤ R)
    (Ap Ep : ℕ → ℝ) (hAp : ∀ j, 0 ≤ Ap j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ j y, |iteratedDeriv j ψ y| ≤ Ap j * (Real.log x) ^ Ep j) →
      ∀ q₀ g q : ℕ, ∀ [NeZero q₀] [NeZero g] [NeZero q],
      Nat.Coprime q₀ (g * q) → Nat.Coprime g q → Squarefree q →
      ∀ A B : ℤ, IsUnit (A : ZMod q) →
      ∀ w₂ : ℕ, 0 < w₂ → Nat.Coprime w₂ q → g ∣ w₂ →
      ∀ N c esc Λ Ewidth w d₀ L κ Ccard Bcoeff E₀ τcoeff τa Ddensity : ℝ,
      0 < N → 0 < c → 0 < esc → 0 < Λ → 0 < Ewidth → 0 < w →
      0 ≤ L → 0 ≤ κ → 0 ≤ Ccard → 0 ≤ Bcoeff → 0 ≤ τcoeff → 0 ≤ τa → 1 ≤ Ddensity →
      ∀ J : ℕ, 0 < J → Λ ≤ (J : ℝ) * (N / (c * (q₀ : ℝ) * esc)) →
      ∀ D : Finset ℕ, ∀ ρ : ℕ → ℝ,
      (∀ e ∈ D, 0 ≤ ρ e ∧ ρ e ≤ L) →
      (∀ e ∈ D, Nat.Coprime e (g * q) ∧
        |w * (e : ℝ) - d₀| ≤ Ewidth ∧ c₀ * esc ≤ (e : ℝ) ∧ (e : ℝ) ≤ 2 * esc) →
      ∀ Lines : ZMod q₀ → Finset (ZMod q₀), (∀ r, ((Lines r).card : ℝ) ≤ κ) →
      ∀ S : Finset ℤ,
      (∀ l ∈ S, Λ ≤ |(l : ℝ)| ∧ |(l : ℝ)| ≤ 2 * Λ ∧
        IsUnit ((l / (w₂ : ℤ) : ℤ) : ZMod q)) →
      (∀ l ∈ S, (l.natAbs.divisors.card : ℝ) ≤ τcoeff) →
      (∀ t ∈ incidenceRowDivisors D, ∀ a ∈ incidenceDividedCoefficientSet S (t * w₂),
        (a.natAbs.divisors.card : ℝ) ≤ τa) →
      ∀ coeff : ℤ → ℂ, (∀ l ∈ S, ‖coeff l‖ ≤ Bcoeff) →
      (∑ l ∈ S, ‖coeff l‖ ^ 2) ≤ E₀ →
      let V₀ := (R / c₀ + 2) * (N / (c * (q₀ : ℝ) * esc))
      (∀ t ∈ incidenceRowDivisors D,
        (Λ / ((t * w₂ : ℕ) : ℝ)) * V₀ ≤ Ddensity * (q : ℝ)) →
      (∀ t ∈ incidenceRowDivisors D,
        ((incidenceDividedCoefficientSet S (t * w₂)).card : ℝ) ≤ Ccard * V₀) →
      incidenceOriginalProgressionEnergy (m := q₀ * (g * q)) (q₀ := q₀)
        (A : ZMod _) B D ρ w₂ S Lines coeff (fun n => (ψ (c * (n : ℝ) / N) : ℂ)) ≤
      (q₀ : ℝ) * κ * ((1 + x ^ (2 * η)) * K * L) *
        (9 * Ddensity * (Ccard + 8 * τa) * V₀ *
          ((2 * (Ewidth / (w * (q₀ : ℝ))) * esc +
              (q : ℝ) ^ (1 / 2 + η) * J * (Ewidth / (w * (q₀ : ℝ))) +
              (q : ℝ) ^ (1 / 2 + η) * (2 * esc)) * (τcoeff * E₀) +
            ((J : ℝ) * (q : ℝ) ^ (3 / 2 + η)) *
              (6 * (Λ / (w₂ : ℝ)) * Bcoeff ^ 2) *
                ∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹)) := by
  obtain ⟨K, hK, hwindow⟩ := incidenceOriginalSector_window_bound hK4 η c₀ R hη hc₀ hR Ap Ep hAp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hwindow, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro ψ hψ hsψ hder q₀ g q _ _ _ h0 hg hq A B hA w₂ hw₂ hwq hgw
    N c esc Λ Ewidth w d₀ L κ Ccard Bcoeff E₀ τcoeff τa Ddensity
    hN hc hesc hΛ hEwidth hw hL hκ hCcard hBcoeff hτcoeff hτa hDdensity
    J hJ hJscale D ρ hρ hD Lines hLines S hS hdivisors hτ coeff hcoeff henergy V₀ hdensity hcard
  have hq₀R : 0 < (q₀ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₀)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hV₀ : 0 < V₀ := by dsimp only [V₀]; positivity
  have htpos (t : ℕ) (ht : t ∈ incidenceRowDivisors D) : 0 < t := by
    obtain ⟨_, _, hte⟩ := Finset.mem_biUnion.mp ht
    exact Nat.pos_of_mem_divisors hte
  have hdyadic : ∀ l ∈ S, Λ ≤ |(l : ℝ)| ∧ |(l : ℝ)| ≤ 2 * Λ :=
    fun l hl => ⟨(hS l hl).1, (hS l hl).2.1⟩
  have hunit : ∀ l ∈ S, IsUnit ((l / (w₂ : ℤ) : ℤ) : ZMod q) :=
    fun l hl => (hS l hl).2.2
  have hAt (t : ℕ) (ht : t ∈ incidenceRowDivisors D)
      (a : ℤ) (ha : a ∈ incidenceDividedCoefficientSet S (t * w₂)) :
      Λ / ((t * w₂ : ℕ) : ℝ) ≤ |(a : ℝ)| ∧
        |(a : ℝ)| ≤ 2 * (Λ / ((t * w₂ : ℕ) : ℝ)) ∧ IsUnit (a : ZMod q) :=
    ⟨(incidenceDividedCoefficient_dyadic S (t * w₂) (mul_pos (htpos t ht) hw₂) Λ hdyadic a ha).1,
      (incidenceDividedCoefficient_dyadic S (t * w₂) (mul_pos (htpos t ht) hw₂) Λ hdyadic a ha).2,
      incidenceFrequencySectors_quotient_unit S q t w₂ (htpos t ht).ne' hw₂.ne' hunit a ha⟩
  have hell (t : ℕ) (ht : t ∈ incidenceRowDivisors D)
      (a : ℤ) (ha : a ∈ incidenceDividedCoefficientSet S (t * w₂)) :
      |((((t * w₂ : ℕ) : ℤ) * a : ℤ) : ℝ) / Λ| ≤ 2 := by
    have hh := (hS _ ((incidenceDividedCoefficientSet_mem S (t * w₂)
      (mul_pos (htpos t ht) hw₂).ne' a).mp ha)).2.1
    rw [abs_div, abs_of_pos hΛ]
    exact (div_le_iff₀ hΛ).mpr hh
  have hb := hx ψ hψ hsψ hder q₀ g q h0 hg hq A B hA w₂ hwq hgw
    N c esc Λ Ewidth w d₀ L κ hN hc hesc hΛ hEwidth hw hL hκ
    J hJ hJscale D ρ hρ hD Lines hLines S (fun t => Λ / ((t * w₂ : ℕ) : ℝ)) τa hτa
    (fun t ht => by have ht0 := htpos t ht; positivity) hAt hτ hell coeff
  have hscale (t : ℕ) : Ewidth / (w * (t : ℝ) * (q₀ : ℝ)) =
      (Ewidth / (w * (q₀ : ℝ))) / (t : ℝ) := by ring
  simp_rw [hscale] at hb
  apply hb.trans
  have hsum := incidenceSectorWindow_sum_le (incidenceRowDivisors D) htpos S w₂ hw₂
    Λ (Ewidth / (w * (q₀ : ℝ))) esc V₀ (q : ℝ) Bcoeff E₀ Ccard τcoeff τa Ddensity η J
    hΛ (by positivity) hesc.le hV₀.le hqR hBcoeff hCcard hτcoeff hτa hDdensity
    hdyadic hdivisors coeff hcoeff henergy hdensity hcard
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceOriginalProgression_four_contributions
