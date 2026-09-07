import IncidenceSourceGeometry
import IncidenceEnergyRowSupport

/-!
# Geometric constants for the literal supported source rows

The e scale is CΔ/w and the lower comparability constant is C⁻².
The Farey scale and the angular count are computed from those actual
constants rather than from a separately assumed row envelope.
-/

noncomputable section
namespace PrimeGap182Audit

set_option maxHeartbeats 1600000

theorem incidenceSourceRows_comparable (C Δ Δ₁ d₀ TD w e : ℝ)
    (hC : 1 ≤ C) (hΔ : 0 < Δ) (_hΔ₁ : 0 < Δ₁) (hw : 0 < w)
    (hcenterlo : Δ / C ≤ d₀) (hcenterhi : d₀ ≤ C * Δ)
    (hshort : TD * Δ₁ ≤ C * Δ)
    (hlocal : d₀ ≤ w * e ∧ w * e ≤ d₀ + TD * Δ₁) :
    (1 / C ^ 2) * (C * Δ / w) ≤ e ∧ e ≤ 2 * (C * Δ / w) ∧
      |w * e - d₀| ≤ TD * Δ₁ := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hrat : (1 / C ^ 2) * (C * Δ / w) = Δ / (C * w) := by field_simp
  rw [hrat]
  refine ⟨(div_le_iff₀ (mul_pos hC0 hw)).mpr ?_, ?_, ?_⟩
  · have hlo := (div_le_iff₀ hC0).mp hcenterlo
    nlinarith only [hlo, mul_le_mul_of_nonneg_left hlocal.1 hC0.le]
  · rw [← mul_div_assoc]
    exact (le_div_iff₀ hw).mpr (by nlinarith only [hlocal.2, hcenterhi, hshort])
  · rw [abs_of_nonneg (sub_nonneg.mpr hlocal.1)]
    linarith only [hlocal.2]

namespace IncidenceSourceEnvelope

variable {x «ω» δ γ L Z A M N H q₀ v₀ w Δ₁ Δ m : ℝ}
variable (h : IncidenceSourceEnvelope x «ω» δ γ L Z A M N H q₀ v₀ w Δ₁ Δ m)

include h

theorem source_actual_farey_scale (C R c : ℝ) (hC : 1 ≤ C) (hR : 1 ≤ R)
    (hc : 1 ≤ c) (hcw : c ≤ w) :
    let esc := C * Δ / w
    let V₀ := (R / (1 / C ^ 2) + 2) * (N / (c * q₀ * esc))
    H ^ 2 ≤ V₀ ∧ V₀ ≤ (R * C ^ 2 + 2) * (N * w / (q₀ * Δ)) ∧
      V₀ = ((R * C ^ 2 + 2) / C) * (N * w / (c * q₀ * Δ)) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw, hΔ₁, hΔ, hm⟩ := h.positive
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  intro esc V₀
  have hid : V₀ = ((R * C ^ 2 + 2) / C) * (N * w / (c * q₀ * Δ)) := by
    dsimp only [V₀, esc]
    field_simp
  have hfactor : 1 ≤ (R * C ^ 2 + 2) / C := by
    apply (one_le_div hC0).mpr
    nlinarith [sq_nonneg (C - 1), mul_le_mul_of_nonneg_right hR (sq_nonneg C)]
  have hfactor0 : 0 ≤ R * C ^ 2 + 2 := by positivity
  have hbase : 0 ≤ N * w / (c * q₀ * Δ) := by positivity
  refine ⟨?_, ?_, hid⟩
  · rw [hid]
    exact (h.source_row_scale_lower hc hcw).trans
      (le_mul_of_one_le_left hbase hfactor)
  · rw [hid]
    have hcle : N * w / (c * q₀ * Δ) ≤ N * w / (q₀ * Δ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_right hc (mul_pos hq₀ hΔ).le]
    exact mul_le_mul (div_le_self hfactor0 hC) hcle hbase hfactor0

theorem source_actual_angular_count (C c Y : ℝ) (hC : 1 ≤ C)
    (hc : 1 ≤ c) (hcw : c ≤ w) (hY0 : 0 < Y)
    (hY : Y ≤ L * q₀ * x ^ δ * H ^ 2 / v₀) :
    let esc := C * Δ / w
    let Vbase := N / (c * q₀ * esc)
    let J := max 1 ⌈(Y / w) / Vbase⌉₊
    0 < J ∧ Y / w ≤ (J : ℝ) * Vbase ∧ (J : ℝ) ≤ 2 * C * L * x ^ δ := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw, hΔ₁, hΔ, hm⟩ := h.positive
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  intro esc Vbase J
  have hV : 0 < Vbase := by dsimp only [Vbase, esc]; positivity
  have hid : (Y / w) / Vbase = C * ((Y / w) / (N * w / (c * q₀ * Δ))) := by
    dsimp only [Vbase, esc]
    field_simp
  have hratio : (Y / w) / Vbase ≤ C * L * x ^ δ := by
    rw [hid]
    exact (mul_le_mul_of_nonneg_left (h.source_angular_ratio hY0 hc hcw hY) hC0.le).trans_eq (by ring)
  have hratio0 : 0 ≤ (Y / w) / Vbase := by positivity
  have hbase : 1 ≤ C * L * x ^ δ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC h.hL)
      (Real.one_le_rpow h.hx h.hδ)
  have hceil := (Nat.ceil_lt_add_one hratio0).le
  refine ⟨Nat.zero_lt_of_lt (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)), ?_, ?_⟩
  · apply (div_le_iff₀ hV).mp
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  · dsimp only [J]
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by nlinarith only [hbase]) (by nlinarith only [hbase, hratio, hceil])

theorem source_actual_incidence_density (C R c Y w₂ t g : ℝ)
    (hC : 1 ≤ C) (hR : 1 ≤ R) (hc : 1 ≤ c) (hcw : c ≤ w)
    (hY0 : 0 < Y) (hw₂ : 1 ≤ w₂) (ht : 1 ≤ t) (hg : 0 < g) (hgw : g ≤ w₂)
    (hY : Y ≤ L * q₀ * x ^ δ * H ^ 2 / v₀) :
    let esc := C * Δ / w
    let V₀ := (R / (1 / C ^ 2) + 2) * (N / (c * q₀ * esc))
    (Y / (w * w₂ * t)) * V₀ / (m / (q₀ * g)) ≤
      (R * C ^ 2 + 2) * (q₀ * L ^ 4 * x ^ (2 * γ + 4 * «ω» + 2 * δ - 1)) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw, hΔ₁, hΔ, hm⟩ := h.positive
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hw₂0 : 0 < w₂ := zero_lt_one.trans_le hw₂
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  intro esc V₀
  have hid := (h.source_actual_farey_scale C R c hC hR hc hcw).2.2
  change V₀ = _ at hid
  rw [hid]
  have hfactor : (R * C ^ 2 + 2) / C ≤ R * C ^ 2 + 2 := div_le_self (by positivity) hC
  calc
    _ ≤ (R * C ^ 2 + 2) *
        ((Y / (w * w₂ * t)) * (N * w / (c * q₀ * Δ)) / (m / (q₀ * g))) := by
      have hh := mul_le_mul_of_nonneg_right hfactor
        (show 0 ≤ (Y / (w * w₂ * t)) * (N * w / (c * q₀ * Δ)) / (m / (q₀ * g)) by positivity)
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (h.source_incidence_density hY0 hc hw₂ ht hg hgw hY) (by positivity)

end IncidenceSourceEnvelope
end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourceRows_comparable
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.source_actual_farey_scale
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.source_actual_angular_count
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.source_actual_incidence_density
