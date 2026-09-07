import IncidenceTaylorScale

/-! The Taylor parameter for the literal natural-number source periods,
derived directly from the original size intervals. -/

noncomputable section
namespace PrimeGap182Audit

theorem incidenceSourceTaylorScale_from_actual_scales
    (C x ε R₀ Q U V Δ M H d₀ TM : ℝ)
    (r₁ q₀ u₁ v₁ v₂ q₂ : ℕ)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hε : 0 < ε)
    (hR₀ : 0 < R₀) (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V)
    (hΔ : 0 < Δ) (hM : 0 < M) (hH : 0 < H) (hTM : 0 ≤ TM)
    (hpos : 0 < r₁ ∧ 0 < q₀ ∧ 0 < u₁ ∧ 0 < v₁ ∧ 0 < v₂ ∧ 0 < q₂)
    (hrlo : R₀ / C ≤ (r₁ : ℝ) * Δ) (hulo : U / C ≤ (u₁ : ℝ))
    (hv₁lo : V / C ≤ (v₁ : ℝ)) (hv₂lo : V / C ≤ (v₂ : ℝ))
    (hqlo : Q / (C * (q₀ : ℝ)) ≤ (q₂ : ℝ))
    (hUVlo : Q / (q₀ : ℝ) ≤ C * U * V) (hdlo : Δ / C ≤ d₀)
    (hHdef : H = x ^ ε * R₀ * Q ^ 2 / ((q₀ : ℝ) * M)) :
    let R₁ := r₁ * q₀ * u₁ * v₁ * q₂
    let R₂ := r₁ * q₀ * u₁ * v₂ * q₂
    (x ^ (-5 * ε) * Δ) / d₀ *
      (1 + TM * M * (2 * C * H) / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹)) ≤
        (C + 4 * TM * C ^ 8) * x ^ (-4 * ε) := by
  intro R₁ R₂
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hd₀ : 0 < d₀ := (div_pos hΔ hC0).trans_le hdlo
  have hr₁ : 0 < (r₁ : ℝ) := by exact_mod_cast hpos.1
  have hq₀ : 0 < (q₀ : ℝ) := by exact_mod_cast hpos.2.1
  have hu₁ : 0 < (u₁ : ℝ) := by exact_mod_cast hpos.2.2.1
  have hq₂ : 0 < (q₂ : ℝ) := by exact_mod_cast hpos.2.2.2.2.2
  have hperiod (v : ℕ) (hv : 0 < v) (hvlo : V / C ≤ (v : ℝ)) :
      0 < ((r₁ * q₀ * u₁ * v * q₂ : ℕ) : ℝ) ∧
      M * H / (d₀ * ((r₁ * q₀ * u₁ * v * q₂ : ℕ) : ℝ)) ≤ C ^ 6 * x ^ ε := by
    have hv0 : 0 < (v : ℝ) := by exact_mod_cast hv
    have hp : 0 < ((r₁ * q₀ * u₁ * v * q₂ : ℕ) : ℝ) := by
      simp only [Nat.cast_mul]
      positivity
    have hlo := incidenceSourcePeriod_lower C R₀ Q U V Δ
      (q₀ : ℝ) (r₁ : ℝ) (u₁ : ℝ) (v : ℝ) (q₂ : ℝ) d₀
      hC0 hR₀ hQ hU hV hΔ hq₀ hr₁ hu₁ hv0 hq₂ hd₀
      hrlo hulo hvlo hqlo hUVlo hdlo
    refine ⟨hp, ?_⟩
    exact incidenceSourcePeriod_ratio C x ε R₀ Q (q₀ : ℝ) M H
      ((r₁ * q₀ * u₁ * v * q₂ : ℕ) : ℝ) d₀
      hC0 hx0 hR₀ hQ hq₀ hM hH hp hd₀ hHdef
      (by simpa only [Nat.cast_mul] using hlo)
  obtain ⟨hR₁, h₁⟩ := hperiod v₁ hpos.2.2.2.1 hv₁lo
  obtain ⟨hR₂, h₂⟩ := hperiod v₂ hpos.2.2.2.2.1 hv₂lo
  exact incidenceSourceTaylorScale_bound C x ε Δ d₀ M H TM (R₁ : ℝ) (R₂ : ℝ)
    hC hx hε hΔ hd₀ hM.le hH.le hTM hR₁ hR₂ hdlo h₁ h₂

#print axioms incidenceSourceTaylorScale_from_actual_scales

end PrimeGap182Audit
