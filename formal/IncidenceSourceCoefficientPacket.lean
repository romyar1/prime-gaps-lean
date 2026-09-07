import IncidenceSourceCoefficients

/-! Finite coefficient bounds from the literal signed source window.
The frequency fibers retain q0; their pointwise squares retain q0^2.
The estimates here use only the displayed source size comparisons. -/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

theorem incidenceSource_window_bounds
    (C x ε V H Hstar : ℝ) (q₀ : ℕ)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hε : 0 ≤ ε) (hV : 0 < V) (hH : 1 ≤ H)
    (hq : 0 < q₀) (hstar : |Hstar| ≤ C * H)
    (hVlo : x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C * V) :
    let Hbound : ℕ := ⌊2 * |Hstar|⌋₊
    let J : Finset ℤ := (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter
      (fun h : ℤ => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)
    (Hbound : ℝ) ≤ 2 * C * H ∧
      (Hbound : ℝ) ≤ (2 * C ^ 3) * q₀ * (V / C) ∧
      J ⊆ (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter (fun h => h ≠ 0) ∧
      (J.card : ℝ) ≤ 5 * C * H := by
  intro Hbound J
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hq0 : 0 < (q₀ : ℝ) := by exact_mod_cast hq
  have hHb : (Hbound : ℝ) ≤ 2 * C * H :=
    (Nat.floor_le (by positivity : 0 ≤ 2 * |Hstar|)).trans (by nlinarith only [hstar])
  have hHqV : H ≤ C * V * q₀ := by
    have hh := (div_le_iff₀ hq0).mp hVlo
    have hx5 : 1 ≤ x ^ (5 * ε) := Real.one_le_rpow hx (by positivity)
    nlinarith only [hh, mul_le_mul_of_nonneg_right hx5 hH0.le]
  have hHV : (Hbound : ℝ) ≤ (2 * C ^ 3) * q₀ * (V / C) := by
    calc
      (Hbound : ℝ) ≤ 2 * C * H := hHb
      _ ≤ 2 * C * (C * V * q₀) := mul_le_mul_of_nonneg_left hHqV (by positivity)
      _ = _ := by field_simp
  have hJ : J ⊆ (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter (fun h => h ≠ 0) := by
    intro h hh
    obtain ⟨hi, hlo, _⟩ := Finset.mem_filter.mp hh
    refine Finset.mem_filter.mpr ⟨hi, ?_⟩
    intro hz
    simp only [hz, Int.cast_zero, zero_div] at hlo
    norm_num at hlo
  have hcard := PrimeGap186.int_finset_card_le_of_mem_real_Icc J
    (-(Hbound : ℝ)) (Hbound : ℝ) (by linarith only [show (0 : ℝ) ≤ Hbound by positivity]) (by
      intro h hh
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩)
  have hCH : 1 ≤ C * H := one_le_mul_of_one_le_of_one_le hC hH
  exact ⟨hHb, hHV, hJ, by linarith only [hcard, hHb, hCH]⟩

theorem incidenceSource_block_frequency_height
    (C x δ ε V H : ℝ) (Hbound v₁ v₂ m w₁ w₂ : ℕ) (J : Finset ℤ)
    (hC : 1 ≤ C) (_hx : 0 < x) (hV : 0 < V) (hH : 0 < H)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hHb : (Hbound : ℝ) ≤ 2 * C * H)
    (hJ : J ⊆ (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter (fun h => h ≠ 0))
    (hv₁hi : (v₁ : ℝ) ≤ C * V) (hv₂hi : (v₂ : ℝ) ≤ C * V)
    (hVhi : V ≤ C * x ^ (δ + 5 * ε) * H)
    (Y : ℤ) (hS : (incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y).Nonempty) :
    0 < |(Y : ℝ)| ∧
      |(Y : ℝ)| ≤ 4 * C ^ 3 * x ^ (δ + 5 * ε) * H ^ 2 / (Nat.gcd v₁ v₂ : ℝ) := by
  obtain ⟨h, hh⟩ := hS
  have hband := (Finset.mem_filter.mp hh).2.2.2
  have hYne : (Y : ℝ) ≠ 0 := by
    intro hz
    simp only [hz, div_zero] at hband
    norm_num at hband
  have hYpos : 0 < |(Y : ℝ)| := abs_pos.mpr hYne
  have hratio : |(incidenceReducedFrequency v₁ v₂ h : ℝ)| / |(Y : ℝ)| =
      (incidenceReducedFrequency v₁ v₂ h : ℝ) / (Y : ℝ) := by
    rw [← abs_div, abs_of_nonneg (zero_le_one.trans hband.1)]
  have hYfreq : |(Y : ℝ)| ≤ |(incidenceReducedFrequency v₁ v₂ h : ℝ)| := by
    have hb := (le_div_iff₀ hYpos).mp (hratio.symm ▸ hband.1)
    simpa only [one_mul] using hb
  have hg : 0 < (Nat.gcd v₁ v₂ : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left v₂ hv₁
  have hpair := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  have hcoord (n : ℤ) (hn : n ∈ J) : |(n : ℝ)| ≤ (Hbound : ℝ) := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp (hJ hn)).1
    exact abs_le.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hs : (Nat.gcd v₁ v₂ : ℝ) * (incidenceReducedFrequency v₁ v₂ h : ℝ) =
      (h.1 : ℝ) * v₂ - (h.2 : ℝ) * v₁ := by
    exact_mod_cast incidenceReducedFrequency_scale v₁ v₂ h
  have habs : (Nat.gcd v₁ v₂ : ℝ) * |(incidenceReducedFrequency v₁ v₂ h : ℝ)| =
      |(h.1 : ℝ) * v₂ - (h.2 : ℝ) * v₁| := by
    simpa only [abs_mul, abs_of_pos hg] using congrArg abs hs
  refine ⟨hYpos, (le_div_iff₀ hg).mpr ?_⟩
  calc
    |(Y : ℝ)| * (Nat.gcd v₁ v₂ : ℝ) ≤
        |(incidenceReducedFrequency v₁ v₂ h : ℝ)| * (Nat.gcd v₁ v₂ : ℝ) :=
      mul_le_mul_of_nonneg_right hYfreq hg.le
    _ = |(h.1 : ℝ) * v₂ - (h.2 : ℝ) * v₁| := by simpa only [mul_comm] using habs
    _ ≤ |(h.1 : ℝ)| * v₂ + |(h.2 : ℝ)| * v₁ := by
      simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ v₁ by positivity),
        abs_of_nonneg (show (0 : ℝ) ≤ v₂ by positivity)] using abs_sub (h.1 * (v₂ : ℝ)) (h.2 * (v₁ : ℝ))
    _ ≤ (Hbound : ℝ) * (C * V) + (Hbound : ℝ) * (C * V) := by
      gcongr
      · exact hcoord _ hpair.1
      · exact hcoord _ hpair.2
    _ ≤ (2 * C * H) * (C * V) + (2 * C * H) * (C * V) := by gcongr
    _ = 4 * C ^ 2 * H * V := by ring
    _ ≤ 4 * C ^ 2 * H * (C * x ^ (δ + 5 * ε) * H) := by gcongr
    _ = _ := by ring

theorem incidenceSource_coefficients_from_scales
    (C x ε V H Hstar : ℝ) (q₀ v₁ v₂ m w₁ w₂ : ℕ)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hε : 0 ≤ ε) (hV : 0 < V) (hH : 1 ≤ H)
    (hq : 0 < q₀) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hstar : |Hstar| ≤ C * H)
    (hVlo : x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C * V)
    (hv₁lo : V / C ≤ (v₁ : ℝ))
    (Y : ℤ) (a : ℤ × ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B) :
    let Hbound : ℕ := ⌊2 * |Hstar|⌋₊
    let J : Finset ℤ := (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter
      (fun h : ℤ => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)
    let S := incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y
    let c := incidenceGroupedCoefficient S (incidenceQuotientFrequency w₁ v₁ v₂) a
    (∀ h ∈ S, ‖a h‖ ≤ B) →
      (∀ y, ‖c y‖ ≤ 6 * C ^ 3 * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B) ∧
      (∀ y, ‖c y‖ ^ 2 ≤ 36 * C ^ 6 * (q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) ^ 2 * B ^ 2) ∧
      (∀ Λ : Finset ℤ, (∑ y ∈ Λ, ‖c y‖ ^ 2) ≤
        150 * C ^ 5 * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B ^ 2 * H ^ 2) := by
  intro Hbound J S c ha
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨_hHb, hHV, hJ, hcard⟩ := incidenceSource_window_bounds
    C x ε V H Hstar q₀ hC hx hε hV hH hq hstar hVlo
  have hL : 1 ≤ 2 * C ^ 3 := by nlinarith only [one_le_pow₀ hC (n := 3)]
  have hVmax : V / C ≤ (max v₁ v₂ : ℕ) :=
    hv₁lo.trans (by exact_mod_cast Nat.le_max_left v₁ v₂)
  obtain ⟨hpoint, henergy⟩ := incidenceSourceFrequencyBlock_coefficients
    Hbound J hJ v₁ v₂ m w₁ w₂ q₀ hv₁ hv₂ hq (V / C) (2 * C ^ 3)
    (div_pos hV hC0) hL hHV hVmax Y a B hB ha
  have hScard : (S.card : ℝ) ≤ 25 * C ^ 2 * H ^ 2 := by
    have hsub : S ⊆ J ×ˢ J :=
      (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    calc
      (S.card : ℝ) ≤ ((J ×ˢ J).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ = (J.card : ℝ) ^ 2 := by rw [Finset.card_product, Nat.cast_mul, pow_two]
      _ ≤ (5 * C * H) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      _ = _ := by ring
  have hpoint' (y : ℤ) : ‖c y‖ ≤ 6 * C ^ 3 * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B := by
    convert hpoint y using 1
    ring
  refine ⟨hpoint', ?_, ?_⟩
  · intro y
    exact (pow_le_pow_left₀ (norm_nonneg _) (hpoint' y) 2).trans_eq (by ring)
  · intro Λ
    calc
      _ ≤ 3 * (2 * C ^ 3) * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B ^ 2 * S.card := henergy Λ
      _ ≤ 3 * (2 * C ^ 3) * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B ^ 2 * (25 * C ^ 2 * H ^ 2) :=
        mul_le_mul_of_nonneg_left hScard (by positivity)
      _ = _ := by ring

theorem incidenceSource_coefficient_common_loss
    (C B P H : ℝ) (q₀ v₀ : ℕ) (c : ℤ → ℂ)
    (hC : 1 ≤ C) (hq : 1 ≤ q₀) (hP : 150 * C ^ 6 * B ^ 2 ≤ P)
    (hpoint : ∀ y, ‖c y‖ ^ 2 ≤ 36 * C ^ 6 * (q₀ : ℝ) ^ 2 * (v₀ : ℝ) ^ 2 * B ^ 2)
    (henergy : ∀ Λ : Finset ℤ, (∑ y ∈ Λ, ‖c y‖ ^ 2) ≤
      150 * C ^ 5 * q₀ * (v₀ : ℝ) * B ^ 2 * H ^ 2) :
    (∀ y, ‖c y‖ ^ 2 ≤ P * (q₀ : ℝ) ^ 2 * (v₀ : ℝ) ^ 2) ∧
      (∀ Λ : Finset ℤ, (∑ y ∈ Λ, ‖c y‖ ^ 2) ≤ P * (q₀ : ℝ) ^ 2 * v₀ * H ^ 2) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hC56 : C ^ 5 ≤ C ^ 6 := pow_le_pow_right₀ hC (by norm_num)
  have hqR : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq
  have hq2 : (q₀ : ℝ) ≤ (q₀ : ℝ) ^ 2 := le_self_pow₀ hqR (by norm_num)
  have hP36 : 36 * C ^ 6 * B ^ 2 ≤ P :=
    (by nlinarith only [sq_nonneg B, pow_nonneg hC0 6] : 36 * C ^ 6 * B ^ 2 ≤ 150 * C ^ 6 * B ^ 2).trans hP
  constructor
  · intro y
    calc
      _ ≤ 36 * C ^ 6 * (q₀ : ℝ) ^ 2 * (v₀ : ℝ) ^ 2 * B ^ 2 := hpoint y
      _ = (36 * C ^ 6 * B ^ 2) * ((q₀ : ℝ) ^ 2 * (v₀ : ℝ) ^ 2) := by ring
      _ ≤ P * ((q₀ : ℝ) ^ 2 * (v₀ : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hP36 (by positivity)
      _ = _ := by ring
  · intro Λ
    calc
      _ ≤ 150 * C ^ 5 * q₀ * (v₀ : ℝ) * B ^ 2 * H ^ 2 := henergy Λ
      _ ≤ 150 * C ^ 6 * (q₀ : ℝ) ^ 2 * (v₀ : ℝ) * B ^ 2 * H ^ 2 := by gcongr
      _ = (150 * C ^ 6 * B ^ 2) * ((q₀ : ℝ) ^ 2 * v₀ * H ^ 2) := by ring
      _ ≤ P * ((q₀ : ℝ) ^ 2 * v₀ * H ^ 2) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = _ := by ring

#print axioms incidenceSource_window_bounds
#print axioms incidenceSource_block_frequency_height
#print axioms incidenceSource_coefficients_from_scales
#print axioms incidenceSource_coefficient_common_loss

end PrimeGap182Audit
