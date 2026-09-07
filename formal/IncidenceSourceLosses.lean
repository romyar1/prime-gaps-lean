import IncidenceSubpowerLoss
import IncidenceEnergyBudget

/-!
# A proved uniform loss packet for the source assembly

Every field is an explicit scalar, divisor, or finite harmonic bound.
The uniform construction below derives the packet for the actual logarithmic
profile envelopes. No source-energy or distribution assertion is a field.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

structure IncidenceSourceLosses
    (x «ω» δ γ ε η C R L Z P K Lrow Bamp : ℝ) (J : ℕ) : Prop where
  power : P = x ^ (ε / 100)
  C_small : C ≤ P
  geometry : R * C ^ 2 + 2 ≤ P
  cardinal : 25 * C ^ 2 ≤ P
  width : (5 / 2 : ℝ) ≤ P
  window : 1 + x ^ (2 * η) ≤ P
  kernel : K ≤ P
  row : Lrow ≤ P
  coefficient : 150 * C ^ 6 * Bamp ^ 2 ≤ P
  taylor_count : 162 * (J + 1 : ℕ) ^ 2 ≤ P
  envelope : L ≤ x ^ (20 * ε)
  angular : 2 * C * L ≤ x ^ (25 * ε)
  retreat : Z = x ^ (54 * ε)
  oscillatory_gap : 600 * ε ≤ 5 * γ - 3 / 2 - 40 * «ω» - 16 * δ
  row_gap : 250 * ε ≤ 2 * γ - 1 / 2 - 16 * «ω» - 6 * δ
  density : (R * C ^ 2 + 2) * L ^ 4 * x ^ (2 * γ + 4 * «ω» + 2 * δ - 1) ≤ 1
  frequency : 4 * C ^ 3 * x ^ (5 * ε) ≤ L
  short : (5 / 2 : ℝ) * x ^ (-5 * ε) ≤ C
  large : 11 ≤ x ^ ε
  divisors : ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ x ^ (100 : ℝ) →
    (n.divisors.card : ℝ) ≤ P
  harmonic : ∀ (Dmax : ℕ) (W : Finset ℕ), W ⊆ Finset.Icc 1 Dmax →
    (Dmax : ℝ) ≤ x ^ (100 : ℝ) → (∑ t ∈ W, (t : ℝ)⁻¹) ≤ P

set_option maxHeartbeats 2400000

theorem incidenceSourceLosses_eventually
    («ω» δ γlo γhi ε C R K Lrow Cj TM CM EM : ℝ) (J : ℕ)
    (hε : 0 < ε) (hC : 1 ≤ C) (_hR : 1 ≤ R)
    (hgap : 600 * ε ≤ 5 * γlo - 3 / 2 - 40 * «ω» - 16 * δ)
    (hrowgap : 250 * ε ≤ 2 * γlo - 1 / 2 - 16 * «ω» - 6 * δ)
    (hdensity : 100 * ε ≤ 1 - 2 * γhi - 4 * «ω» - 2 * δ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      IncidenceSourceLosses x «ω» δ γ ε (ε / 100000) C R
        (C ^ 10 * x ^ (8 * ε)) (x ^ (54 * ε)) (x ^ (ε / 100)) K Lrow
        (Cj * (TM * (CM * (Real.log x) ^ EM)) ^ 2) J := by
  let η := ε / 100000
  let coeffConst := 150 * C ^ 6 * Cj ^ 2 * TM ^ 4 * CM ^ 4
  have hconst (a : ℝ) : ∀ᶠ x : ℝ in Filter.atTop, a ≤ x ^ (ε / 100) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 100)).eventually_ge_atTop a
  filter_upwards [hconst C, hconst (R * C ^ 2 + 2), hconst (25 * C ^ 2),
    hconst (5 / 2), hconst K, hconst Lrow, hconst (162 * (J + 1 : ℕ) ^ 2),
    incidenceLog_subpower coeffConst (4 * EM) (ε / 100) (by positivity),
    (tendsto_rpow_atTop (by positivity : 0 < ε / 200)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop hε).eventually_ge_atTop 11,
    incidenceDivisors_subpower (ε / 100) 100 (by positivity) (by norm_num),
    incidenceHarmonic_subpower (ε / 100) 100 (by positivity) (by norm_num),
    Filter.eventually_ge_atTop (Real.exp 1)] with x
      hCx hgeo hcard hwidth hK hrow hJ hcoeff htwo hlarge hdiv hharm hxe
  have hx : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxe
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 < Real.log x := by
    have hh : 1 ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
    exact zero_lt_one.trans_le hh
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hCε : C ≤ x ^ ε := hCx.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  have hL : C ^ 10 * x ^ (8 * ε) ≤ x ^ (20 * ε) := by
    calc
      _ ≤ (x ^ ε) ^ 10 * x ^ (8 * ε) := by gcongr
      _ = x ^ (18 * ε) := by
        rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hwin : 1 + x ^ (2 * η) ≤ x ^ (ε / 100) := by
    have hhalf : 1 ≤ x ^ (ε / 200) := Real.one_le_rpow hx (by positivity)
    have heta : x ^ (2 * η) ≤ x ^ (ε / 200) :=
      Real.rpow_le_rpow_of_exponent_le hx (by dsimp only [η]; linarith)
    calc
      _ ≤ 2 * x ^ (ε / 200) := by linarith only [hhalf, heta]
      _ ≤ x ^ (ε / 200) * x ^ (ε / 200) := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  have hcoefficient : 150 * C ^ 6 * (Cj * (TM * (CM * (Real.log x) ^ EM)) ^ 2) ^ 2 ≤
      x ^ (ε / 100) := by
    calc
      _ = coeffConst * ((Real.log x) ^ EM) ^ 4 := by dsimp only [coeffConst]; ring
      _ = coeffConst * (Real.log x) ^ (4 * EM) := by
        rw [← Real.rpow_mul_natCast hlog.le]
        congr 2
        norm_num
        ring
      _ ≤ _ := hcoeff
  have hangular : 2 * C * (C ^ 10 * x ^ (8 * ε)) ≤ x ^ (25 * ε) := by
    calc
      _ ≤ x ^ ε * x ^ ε * x ^ (20 * ε) := by
        gcongr
        linarith only [hlarge]
      _ = x ^ (22 * ε) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hfrequency : 4 * C ^ 3 * x ^ (5 * ε) ≤ C ^ 10 * x ^ (8 * ε) := by
    have hCpow : C ^ 3 ≤ C ^ 10 := pow_le_pow_right₀ hC (by norm_num)
    calc
      _ ≤ x ^ (3 * ε) * C ^ 10 * x ^ (5 * ε) := by
        gcongr
        exact (by linarith only [hlarge] : 4 ≤ x ^ ε).trans
          (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
      _ = C ^ 10 * (x ^ (3 * ε) * x ^ (5 * ε)) := by ring
      _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring
  have hshort : (5 / 2 : ℝ) * x ^ (-5 * ε) ≤ C := by
    have hfive : (5 / 2 : ℝ) ≤ x ^ (5 * ε) :=
      (by linarith only [hlarge] : (5 / 2 : ℝ) ≤ x ^ ε).trans
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
    calc
      _ ≤ x ^ (5 * ε) * x ^ (-5 * ε) := mul_le_mul_of_nonneg_right hfive (by positivity)
      _ = 1 := by
        rw [← Real.rpow_add hx0, show 5 * ε + -5 * ε = 0 by ring, Real.rpow_zero]
      _ ≤ _ := hC
  intro γ hlo hhi
  refine ⟨rfl, hCx, hgeo, hcard, hwidth, hwin, hK, hrow, hcoefficient, hJ,
    hL, hangular, rfl, by linarith only [hgap, hlo],
    by linarith only [hrowgap, hlo], ?_, hfrequency, hshort, hlarge, hdiv, hharm⟩
  calc
    _ ≤ x ^ (ε / 100) * (x ^ (20 * ε)) ^ 4 *
        x ^ (2 * γ + 4 * «ω» + 2 * δ - 1) := by gcongr
    _ = x ^ (ε / 100 + 80 * ε + 2 * γ + 4 * «ω» + 2 * δ - 1) := by
      rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      norm_num
      ring
    _ ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hdensity, hhi, hε])
    _ = 1 := Real.rpow_zero x

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourceLosses_eventually
