import IncidenceMaskedFour
import IncidenceCorrectedNormalization

/-!
# Normalizing the actual four sector contributions

The uniform small loss P is separate from the angular and frequency-height
losses Ly and Lj. In particular the mean term incurs neither Ly nor Lj.
The common coefficient and density correction is retained as q₀³.
-/

noncomputable section
namespace PrimeGap182Audit
open scoped BigOperators

set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem incidenceOscillatory_rpow_bounds (q q₀ m P η : ℝ)
    (hq : 0 < q) (hq₀ : 0 < q₀) (hm : 0 < m) (_hP : 0 ≤ P)
    (hqm : q₀ * q ≤ m) (hη : q ^ η ≤ P) :
    q ^ (1 / 2 + η) ≤ P * Real.sqrt m / q₀ ^ (1 / 2 : ℝ) ∧
      q ^ (3 / 2 + η) ≤ P * m ^ (3 / 2 : ℝ) / q₀ ^ (3 / 2 : ℝ) := by
  have hqm' : q ≤ m / q₀ := (le_div_iff₀ hq₀).mpr (by simpa only [mul_comm] using hqm)
  have hp (s : ℝ) (hs : 0 ≤ s) :
      q ^ (s + η) ≤ P * m ^ s / q₀ ^ s := by
    rw [Real.rpow_add hq]
    have hh := Real.rpow_le_rpow hq.le hqm' hs
    rw [Real.div_rpow hm.le hq₀.le] at hh
    exact (mul_le_mul hh hη (Real.rpow_nonneg hq.le _) (by positivity)).trans_eq (by ring)
  exact ⟨by simpa only [Real.sqrt_eq_rpow] using hp (1 / 2) (by norm_num),
    hp (3 / 2) (by norm_num)⟩

theorem incidenceFourTerms_normalize
    (x δ η P Ly Lj q q₀ m V Ebase esc Λ w w₂ v₀ H N Δ₁ Δ B E₀ τ Harm : ℝ)
    (J : ℕ)
    (hx : 0 < x) (hP : 1 ≤ P) (hLy : 0 < Ly) (hLj : 0 < Lj)
    (hq : 0 < q) (hq₀ : 0 < q₀) (hm : 0 < m) (hw : 0 < w) (hw₂ : 1 ≤ w₂)
    (hv₀ : 0 < v₀) (hH : 0 < H) (hN : 0 < N) (hΔ₁ : 0 < Δ₁) (hΔ : 0 < Δ)
    (_hV0 : 0 ≤ V) (hEbase0 : 0 ≤ Ebase) (hesc0 : 0 ≤ esc) (hΛ0 : 0 ≤ Λ)
    (hE₀ : 0 ≤ E₀) (hτ : 0 ≤ τ) (hHarm : 0 ≤ Harm)
    (hqm : q₀ * q ≤ m) (hη : q ^ η ≤ P) (hΔ₁Δ : Δ₁ ≤ Δ)
    (hV : V ≤ P * N * w / (q₀ * Δ))
    (hEbase : Ebase ≤ P * Δ₁ / (w * q₀)) (hesc : esc ≤ P * Δ / w)
    (hΛ : Λ ≤ Ly * q₀ * x ^ δ * H ^ 2 / (w * v₀))
    (hJ : (J : ℝ) ≤ Lj * x ^ δ)
    (hmass : τ * E₀ ≤ P ^ 2 * q₀ ^ 2 * v₀ * H ^ 2)
    (hpoint : B ^ 2 * Harm ≤ P ^ 2 * q₀ ^ 2 * v₀ ^ 2) :
    V * incidenceFourTerms η Ebase esc q Λ w₂ B E₀ τ Harm J / (v₀ ^ 2 * N ^ 2) ≤
      P ^ 5 *
        (2 * (q₀ ^ 3 * (Δ₁ * H ^ 2 / (q₀ ^ 3 * w * v₀ * N))) +
          Lj * (q₀ ^ 3 * (x ^ δ * Real.sqrt m * H ^ 2 /
            (q₀ ^ (7 / 2 : ℝ) * v₀ * N))) +
          2 * (q₀ ^ 3 * (Real.sqrt m * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N)))) +
        6 * P ^ 4 * Ly * Lj *
          (q₀ ^ 3 * (x ^ (2 * δ) * m ^ (3 / 2 : ℝ) * H ^ 2 /
            (q₀ ^ (5 / 2 : ℝ) * v₀ * N * Δ))) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  obtain ⟨hhalf, hthree⟩ := incidenceOscillatory_rpow_bounds q q₀ m P η hq hq₀ hm hP0.le hqm hη
  have hw₂0 : 0 < w₂ := zero_lt_one.trans_le hw₂
  have hden : 0 < v₀ ^ 2 * N ^ 2 := by positivity
  have hΛdiv : Λ / w₂ ≤ Ly * q₀ * x ^ δ * H ^ 2 / (w * v₀) :=
    (div_le_self hΛ0 hw₂).trans hΛ
  have hq25 : q₀ ^ (5 / 2 : ℝ) = q₀ ^ 2 * q₀ ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hq₀, Real.rpow_two]
  have hq35 : q₀ ^ (7 / 2 : ℝ) = q₀ ^ 3 * q₀ ^ (1 / 2 : ℝ) := by
    rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num, Real.rpow_add hq₀, Real.rpow_ofNat]
  have hq25' : q₀ ^ (5 / 2 : ℝ) = q₀ * q₀ ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hq₀, Real.rpow_one]
  have hqhalf : q₀ ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hq₀ _)
  have hqthree : q₀ ^ (3 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hq₀ _)
  have harea : V * (2 * Ebase * esc) * (τ * E₀) / (v₀ ^ 2 * N ^ 2) ≤
      2 * P ^ 5 * (q₀ ^ 3 * (Δ₁ * H ^ 2 / (q₀ ^ 3 * w * v₀ * N))) := by
    calc
      _ ≤ (P * N * w / (q₀ * Δ)) *
          (2 * (P * Δ₁ / (w * q₀)) * (P * Δ / w)) *
          (P ^ 2 * q₀ ^ 2 * v₀ * H ^ 2) / (v₀ ^ 2 * N ^ 2) := by gcongr
      _ = _ := by
        field_simp
  have hrowtwo : V * (q ^ (1 / 2 + η) * (2 * esc)) * (τ * E₀) / (v₀ ^ 2 * N ^ 2) ≤
      2 * P ^ 5 * (q₀ ^ 3 * (Real.sqrt m * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N))) := by
    calc
      _ ≤ (P * N * w / (q₀ * Δ)) *
          ((P * Real.sqrt m / q₀ ^ (1 / 2 : ℝ)) * (2 * (P * Δ / w))) *
          (P ^ 2 * q₀ ^ 2 * v₀ * H ^ 2) / (v₀ ^ 2 * N ^ 2) := by gcongr
      _ = _ := by
        rw [hq25]
        field_simp
  have hrowone : V * (q ^ (1 / 2 + η) * J * Ebase) * (τ * E₀) / (v₀ ^ 2 * N ^ 2) ≤
      P ^ 5 * Lj * (q₀ ^ 3 * (x ^ δ * Real.sqrt m * H ^ 2 /
        (q₀ ^ (7 / 2 : ℝ) * v₀ * N))) := by
    calc
      _ ≤ (P * N * w / (q₀ * Δ)) *
          ((P * Real.sqrt m / q₀ ^ (1 / 2 : ℝ)) * (Lj * x ^ δ) *
            (P * Δ₁ / (w * q₀))) *
          (P ^ 2 * q₀ ^ 2 * v₀ * H ^ 2) / (v₀ ^ 2 * N ^ 2) := by gcongr
      _ = (P ^ 5 * Lj * (q₀ ^ 3 * (x ^ δ * Real.sqrt m * H ^ 2 /
          (q₀ ^ (7 / 2 : ℝ) * v₀ * N)))) * (Δ₁ / Δ) := by
        rw [hq35]
        field_simp
      _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one hΔ).mpr hΔ₁Δ)
  have hosc : V * ((J : ℝ) * q ^ (3 / 2 + η)) * (6 * (Λ / w₂)) *
      (B ^ 2 * Harm) / (v₀ ^ 2 * N ^ 2) ≤
      6 * P ^ 4 * Ly * Lj * (q₀ ^ 3 *
        (x ^ (2 * δ) * m ^ (3 / 2 : ℝ) * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N * Δ))) := by
    calc
      _ ≤ (P * N * w / (q₀ * Δ)) * ((Lj * x ^ δ) *
          (P * m ^ (3 / 2 : ℝ) / q₀ ^ (3 / 2 : ℝ))) *
          (6 * (Ly * q₀ * x ^ δ * H ^ 2 / (w * v₀))) *
          (P ^ 2 * q₀ ^ 2 * v₀ ^ 2) / (v₀ ^ 2 * N ^ 2) := by gcongr
      _ = _ := by
        rw [hq25', show 2 * δ = δ + δ by ring, Real.rpow_add hx]
        field_simp
  calc
    _ = V * (2 * Ebase * esc) * (τ * E₀) / (v₀ ^ 2 * N ^ 2) +
        V * (q ^ (1 / 2 + η) * J * Ebase) * (τ * E₀) / (v₀ ^ 2 * N ^ 2) +
        V * (q ^ (1 / 2 + η) * (2 * esc)) * (τ * E₀) / (v₀ ^ 2 * N ^ 2) +
        V * ((J : ℝ) * q ^ (3 / 2 + η)) * (6 * (Λ / w₂)) *
          (B ^ 2 * Harm) / (v₀ ^ 2 * N ^ 2) := by unfold incidenceFourTerms; ring
    _ ≤ _ := by linarith only [harea, hrowone, hrowtwo, hosc]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceOscillatory_rpow_bounds
#print axioms PrimeGap182Audit.incidenceFourTerms_normalize
