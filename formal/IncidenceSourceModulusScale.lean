import IncidenceFrequencyBlock

/-!
# The actual source modulus and its real scale

The gcd/lcm identity is proved for the actual natural-number parameters.
The C⁶ interval then follows from the six original size comparisons.
Its Δ is the selected divisor scale, before multiplication by x^(-5ε).
-/

noncomputable section
namespace PrimeGap182Audit

theorem incidenceSourceModulus_gcd_lcm (r₁ q₀ u₁ v₁ v₂ q₂ : ℕ) :
    (r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂) * Nat.gcd v₁ v₂ =
      r₁ * q₀ * u₁ * v₁ * v₂ * q₂ := by
  calc
    _ = (r₁ * q₀ * u₁ * q₂) * (Nat.gcd v₁ v₂ * Nat.lcm v₁ v₂) := by ring
    _ = _ := by rw [Nat.gcd_mul_lcm]; ring

theorem incidenceLog_size_interval (C X z : ℝ)
    (hC : 0 < C) (hX : 0 < X) (hz : 0 < z)
    (hlo : X / C ≤ z) (hhi : z ≤ C * X) :
    Real.log X - Real.log C ≤ Real.log z ∧ Real.log z ≤ Real.log C + Real.log X := by
  constructor
  · have h := (Real.log_le_log_iff (div_pos hX hC) hz).mpr hlo
    simpa only [Real.log_div hX.ne' hC.ne'] using h
  · have h := (Real.log_le_log_iff hz (mul_pos hC hX)).mpr hhi
    simpa only [Real.log_mul hC.ne' hX.ne'] using h

theorem incidenceSourceModulus_scale
    (C R₀ Q U V Δ q₀ v₀ m r₁ u₁ v₁ v₂ q₂ : ℝ)
    (hC : 0 < C) (hR₀ : 0 < R₀) (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V)
    (hΔ : 0 < Δ) (hq₀ : 0 < q₀) (hv₀ : 0 < v₀) (hm : 0 < m)
    (hr₁ : 0 < r₁) (hu₁ : 0 < u₁) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hq₂ : 0 < q₂)
    (hmprod : m * v₀ = r₁ * q₀ * u₁ * v₁ * v₂ * q₂)
    (hrlo : R₀ / C ≤ r₁ * Δ) (hrhi : r₁ * Δ ≤ C * R₀)
    (hulo : U / C ≤ u₁) (huhi : u₁ ≤ C * U)
    (hv₁lo : V / C ≤ v₁) (hv₁hi : v₁ ≤ C * V)
    (hv₂lo : V / C ≤ v₂) (hv₂hi : v₂ ≤ C * V)
    (hqlo : Q / (C * q₀) ≤ q₂) (hqhi : q₂ ≤ C * Q / q₀)
    (hUVlo : Q / q₀ ≤ C * U * V) (hUVhi : U * V ≤ C * Q / q₀) :
    R₀ * Q ^ 2 * V / (C ^ 6 * q₀ * Δ * v₀) ≤ m ∧
      m ≤ C ^ 6 * R₀ * Q ^ 2 * V / (q₀ * Δ * v₀) := by
  have hr := incidenceLog_size_interval C R₀ (r₁ * Δ) hC hR₀ (mul_pos hr₁ hΔ) hrlo hrhi
  have hu := incidenceLog_size_interval C U u₁ hC hU hu₁ hulo huhi
  have hv1 := incidenceLog_size_interval C V v₁ hC hV hv₁ hv₁lo hv₁hi
  have hv2 := incidenceLog_size_interval C V v₂ hC hV hv₂ hv₂lo hv₂hi
  have hq := incidenceLog_size_interval C (Q / q₀) q₂ hC (div_pos hQ hq₀) hq₂
    (by simpa only [div_div, mul_comm q₀ C] using hqlo)
    (by simpa only [mul_div_assoc] using hqhi)
  have hUV := incidenceLog_size_interval C (Q / q₀) (U * V) hC (div_pos hQ hq₀)
    (mul_pos hU hV)
    ((div_le_iff₀ hC).mpr (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hUVlo))
    (by simpa only [mul_div_assoc] using hUVhi)
  have hprod := congrArg Real.log hmprod
  simp (disch := positivity) only [Real.log_mul, Real.log_div] at hr hq hUV hprod
  constructor
  · apply (Real.log_le_log_iff (by positivity) hm).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Nat.cast_ofNat]
    linarith only [hr.1, hu.1, hv1.1, hv2.1, hq.1, hUV.1, hprod]
  · apply (Real.log_le_log_iff hm (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Nat.cast_ofNat]
    linarith only [hr.2, hu.2, hv1.2, hv2.2, hq.2, hUV.2, hprod]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourceModulus_gcd_lcm
#print axioms PrimeGap182Audit.incidenceLog_size_interval
#print axioms PrimeGap182Audit.incidenceSourceModulus_scale
