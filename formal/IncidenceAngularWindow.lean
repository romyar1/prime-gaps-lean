import IncidenceUniformSourceWindow

/-!
# Exact finite angular cells for the physical source rows

The cells are disjoint floor intervals. Since the incidence window
already permits bounded nonsmooth weights, this partition has no
derivative loss and no smooth-partition hypothesis.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

def incidenceAngularIndex (J : ℕ) (e γ : ℝ) : ℕ := ⌊(J : ℝ) * γ / e⌋₊

theorem incidenceAngularIndex_spec (J : ℕ) (hJ : 0 < J)
    (e γ : ℝ) (he : 0 < e) (hγ : 0 ≤ γ) (hγe : γ < e) :
    incidenceAngularIndex J e γ < J ∧
      0 ≤ γ / e - (incidenceAngularIndex J e γ : ℝ) / J ∧
      γ / e - (incidenceAngularIndex J e γ : ℝ) / J < (J : ℝ)⁻¹ := by
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hx : 0 ≤ (J : ℝ) * γ / e := div_nonneg (mul_nonneg hJr.le hγ) he.le
  have hxJ : (J : ℝ) * γ / e < J := by
    rw [div_lt_iff₀ he]
    exact mul_lt_mul_of_pos_left hγe hJr
  have hfloor := Nat.floor_le hx
  have hlt := Nat.lt_floor_add_one ((J : ℝ) * γ / e)
  have hdelta : γ / e - (incidenceAngularIndex J e γ : ℝ) / J =
      ((J : ℝ) * γ / e - (incidenceAngularIndex J e γ : ℝ)) / J := by
    field_simp
  refine ⟨(Nat.floor_lt hx).mpr hxJ, ?_, ?_⟩
  · rw [hdelta]
    exact div_nonneg (sub_nonneg.mpr hfloor) hJr.le
  · rw [hdelta, ← one_div]
    apply (div_lt_div_iff_of_pos_right hJr).mpr
    dsimp only [incidenceAngularIndex]
    linarith

theorem incidenceAngularPartition_sum {α : Type*} [AddCommMonoid α]
    (J : ℕ) (hJ : 0 < J) (e γ : ℝ) (he : 0 < e) (hγ : 0 ≤ γ) (hγe : γ < e)
    (a : α) :
    (∑ j ∈ Finset.range J, if incidenceAngularIndex J e γ = j then a else 0) = a := by
  classical
  have hi := (incidenceAngularIndex_spec J hJ e γ he hγ hγe).1
  simp [hi]

theorem incidenceAngularCount_exists (Λ V : ℝ) (hΛ : 0 < Λ) (hV : 0 < V) :
    ∃ J : ℕ, 0 < J ∧ Λ ≤ (J : ℝ) * V ∧ (J : ℝ) ≤ 1 + Λ / V := by
  refine ⟨⌈Λ / V⌉₊, Nat.ceil_pos.mpr (div_pos hΛ hV), ?_, ?_⟩
  · exact (div_le_iff₀ hV).mp (Nat.le_ceil _)
  · exact (Nat.ceil_lt_add_one (div_pos hΛ hV).le).le.trans_eq (add_comm _ _)

theorem incidenceAngularWindow_spec (J : ℕ) (hJ : 0 < J)
    (Λ V esc t e γ : ℝ) (hΛ : 0 < Λ) (hV : 0 < V)
    (hscale : Λ ≤ (J : ℝ) * V) (ht : 0 < t)
    (he : 0 < e) (hee : e ≤ 2 * esc) (hγ : 0 ≤ γ) (hγe : γ < e) :
    let τ : ℝ := (incidenceAngularIndex J e γ : ℝ) / J
    |(γ / e - τ) * Λ / V| ≤ 1 ∧
      |γ - (τ * t) * (e / t)| ≤ 2 * esc / J := by
  intro τ
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  obtain ⟨_, hlo, hhi⟩ := incidenceAngularIndex_spec J hJ e γ he hγ hγe
  change 0 ≤ γ / e - τ at hlo
  change γ / e - τ < (J : ℝ)⁻¹ at hhi
  have hratio : γ / e - τ ≤ (J : ℝ)⁻¹ := hhi.le
  have hlt : (γ / e - τ) * Λ ≤ V := by
    calc
      _ ≤ (J : ℝ)⁻¹ * Λ := mul_le_mul_of_nonneg_right hratio hΛ.le
      _ ≤ (J : ℝ)⁻¹ * ((J : ℝ) * V) :=
        mul_le_mul_of_nonneg_left hscale (inv_nonneg.mpr hJr.le)
      _ = V := by field_simp
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg (mul_nonneg hlo hΛ.le) hV.le)]
    exact (div_le_one hV).mpr hlt
  · have hid : γ - (τ * t) * (e / t) = e * (γ / e - τ) := by field_simp
    rw [hid, abs_of_nonneg (mul_nonneg he.le hlo)]
    calc
      _ ≤ e * (J : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hratio he.le
      _ ≤ (2 * esc) * (J : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hee (inv_nonneg.mpr hJr.le)
      _ = 2 * esc / J := by rw [div_eq_mul_inv]

theorem incidenceSourceCoordinates_norm_le (z : IncidenceSourceCoordinates)
    (B : ℝ) (hB : 0 ≤ B) (hz : ∀ i, |z i| ≤ B) : ‖z‖ ≤ 2 * B := by
  have hs : ‖z‖ ^ 2 ≤ 4 * B ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 4, B ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hz i)
      _ = _ := by simp
  nlinarith [norm_nonneg z]

theorem incidenceSourceCoordinate_norm_bound (z : IncidenceSourceCoordinates)
    (c C T : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hz0 : c ≤ |z 0|) (hz0' : |z 0| ≤ C) (hz1 : |z 1| ≤ 1)
    (hz2 : |z 2| ≤ 2) (hP : |incidenceSourceCoordinatePolynomial z| ≤ T) :
    ‖z‖ ≤ 2 * (C + T / c + 5) := by
  have hcross : |z 1 * z 2| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hz1 hz2 (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hsum : |z 1 * z 2 + z 3| ≤ T / c := by
    apply (le_div_iff₀ hc).mpr
    calc
      _ ≤ |z 0| * |z 1 * z 2 + z 3| := by
        nlinarith only [mul_le_mul_of_nonneg_right hz0 (abs_nonneg (z 1 * z 2 + z 3))]
      _ = |incidenceSourceCoordinatePolynomial z| := by
        rw [incidenceSourceCoordinatePolynomial, abs_mul]
      _ ≤ T := hP
  have hz3 : |z 3| ≤ T / c + 2 := by
    have hh := abs_sub (z 1 * z 2 + z 3) (z 1 * z 2)
    have hi : z 1 * z 2 + z 3 - z 1 * z 2 = z 3 := by ring
    rw [hi] at hh
    linarith
  have htdiv : 0 ≤ T / c := div_nonneg hT hc.le
  apply incidenceSourceCoordinates_norm_le z _ (by positivity)
  intro i
  fin_cases i
  · change |z 0| ≤ _; linarith
  · change |z 1| ≤ _; linarith
  · change |z 2| ≤ _; linarith
  · change |z 3| ≤ _; linarith

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceAngularIndex_spec
#print axioms PrimeGap182Audit.incidenceAngularPartition_sum
#print axioms PrimeGap182Audit.incidenceAngularCount_exists
#print axioms PrimeGap182Audit.incidenceAngularWindow_spec
#print axioms PrimeGap182Audit.incidenceSourceCoordinates_norm_le
#print axioms PrimeGap182Audit.incidenceSourceCoordinate_norm_bound
