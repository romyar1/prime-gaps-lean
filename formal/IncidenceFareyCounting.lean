import IncidenceSourceCRT

/-!
# Exact interval and determinant counts for the Farey coefficient map

The arithmetic-progression counting proof is extracted, with attribution,
from the local `hap` argument of `PrimeGap186.int_linear_image_dvd_card_le`
(the unchanged baseline, lines 86258–86287). The new determinant-fiber
argument is for arbitrary centers and does not require unit numerators.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

theorem incidenceIntegerProgression_card_le (S : Finset ℤ) (u v : ℝ)
    (k a : ℤ) (hk : 0 < k) (huv : u ≤ v)
    (hS : ∀ n ∈ S, u ≤ (n : ℝ) ∧ (n : ℝ) ≤ v)
    (hmod : ∀ n ∈ S, Int.ModEq k n a) :
    (S.card : ℝ) ≤ 1 + (v - u) / (k : ℝ) := by
  classical
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hd : ∀ n ∈ S, k ∣ n - a := fun n hn => (hmod n hn).symm.dvd
  have hinj : Set.InjOn (fun n : ℤ => (n - a) / k) (S : Set ℤ) := by
    intro n hn m hm hnm
    exact (Int.sub_left_inj a).mp
      ((Int.ediv_left_inj (hd n hn) (hd m hm)).mp hnm)
  have hQ := PrimeGap186.int_finset_card_le_of_mem_real_Icc
    (S.image (fun n : ℤ => (n - a) / k))
    ((u - (a : ℝ)) / (k : ℝ)) ((v - (a : ℝ)) / (k : ℝ))
    (div_le_div_of_nonneg_right (sub_le_sub_right huv _) hkR.le) (by
      intro q hq
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
      rw [Int.cast_div (hd n hn) hkR.ne', Int.cast_sub]
      exact ⟨div_le_div_of_nonneg_right (sub_le_sub_right (hS n hn).1 _) hkR.le,
        div_le_div_of_nonneg_right (sub_le_sub_right (hS n hn).2 _) hkR.le⟩)
  calc
    (S.card : ℝ) = ((S.image (fun n : ℤ => (n - a) / k)).card : ℝ) := by
      rw [Finset.card_image_of_injOn hinj]
    _ ≤ 1 + (v - (a : ℝ)) / (k : ℝ) -
        (u - (a : ℝ)) / (k : ℝ) := hQ
    _ = 1 + (v - u) / (k : ℝ) := by ring

/-- A fixed integer determinant has only an arithmetic progression of
possible first coordinates. Signs of the nonzero denominators are free. -/
theorem incidenceDeterminant_fiber_card_le (S : Finset (ℤ × ℤ))
    (a b d : ℤ) (ha : a ≠ 0) (V c : ℝ) (hV : 0 ≤ V)
    (hS : ∀ z ∈ S, b * z.1 - a * z.2 = d)
    (hI : ∀ z ∈ S, |(z.1 : ℝ) - c| ≤ V) :
    (S.card : ℝ) ≤ 1 + 2 * V * (Int.gcd a b : ℝ) / |(a : ℝ)| := by
  classical
  let g : ℕ := Int.gcd a b
  let k : ℤ := (a.natAbs : ℤ) / (g : ℤ)
  have haN : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have haI : 0 < (a.natAbs : ℤ) := by exact_mod_cast haN
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left b ha
  have hgI : 0 < (g : ℤ) := by exact_mod_cast hg
  have hga : (g : ℤ) ∣ (a.natAbs : ℤ) := by
    exact_mod_cast (Nat.gcd_dvd_left a.natAbs b.natAbs)
  have hk : 0 < k := Int.ediv_pos_of_pos_of_dvd haI hgI.le hga
  have hgR : (g : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) = |(a : ℝ)| / (g : ℝ) := by
    have habs : (a.natAbs : ℝ) = |(a : ℝ)| := by
      calc
        (a.natAbs : ℝ) = ((a.natAbs : ℤ) : ℝ) := rfl
        _ = ((|a| : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)
        _ = |(a : ℝ)| := Int.cast_abs
    dsimp only [k]
    rw [Int.cast_div hga hgR]
    simp only [Int.cast_natCast, habs]
  have hinj : Set.InjOn Prod.fst (S : Set (ℤ × ℤ)) := by
    intro z hz w hw hzw
    apply Prod.ext hzw
    apply mul_left_cancel₀ ha
    have hzD := hS z hz
    have hwD := hS w hw
    rw [hzw] at hzD
    linarith
  rcases S.eq_empty_or_nonempty with hzero | ⟨z₀, hz₀⟩
  · rw [hzero, Finset.card_empty, Nat.cast_zero]
    positivity
  have hmod : ∀ r ∈ S.image Prod.fst, Int.ModEq k r z₀.1 := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    have hmul : Int.ModEq (a.natAbs : ℤ) (b * z.1) (b * z₀.1) := by
      apply Int.modEq_iff_dvd.mpr
      have he : b * z₀.1 - b * z.1 = a * (z₀.2 - z.2) := by
        have h₀ := hS z₀ hz₀
        have h₁ := hS z hz
        linarith
      rw [he]
      exact dvd_mul_of_dvd_left (Int.natAbs_dvd_self (a := a)) _
    have hc := Int.ModEq.cancel_left_div_gcd haI hmul
    simpa only [k, g, Int.gcd_def, Int.natAbs_natCast] using hc
  have hb := incidenceIntegerProgression_card_le (S.image Prod.fst)
    (c - V) (c + V) k z₀.1 hk (by linarith) (by
      intro r hr
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
      have h := abs_le.mp (hI z hz)
      constructor <;> linarith) hmod
  rw [Finset.card_image_of_injOn hinj, hkR] at hb
  calc
    (S.card : ℝ) ≤ 1 + (c + V - (c - V)) / (|(a : ℝ)| / (g : ℝ)) := hb
    _ = _ := by dsimp only [g]; field_simp; ring

/-- Determinant collision count in two arbitrary translated intervals.
The constants use V as a half-width, so no convention about endpoints is
hidden in the statement. -/
theorem incidenceDeterminant_mod_card_le (S : Finset (ℤ × ℤ))
    (a b q d₀ : ℤ) (ha : a ≠ 0) (hq : 0 < q)
    (U V c₁ c₂ : ℝ) (hU : 0 < U) (hV : 0 ≤ V)
    (haU : U ≤ |(a : ℝ)|) (ha2U : |(a : ℝ)| ≤ 2 * U)
    (hb2U : |(b : ℝ)| ≤ 2 * U)
    (hS : ∀ z ∈ S, Int.ModEq q (b * z.1 - a * z.2) d₀)
    (hI : ∀ z ∈ S, |(z.1 : ℝ) - c₁| ≤ V ∧ |(z.2 : ℝ) - c₂| ≤ V) :
    (S.card : ℝ) ≤ (1 + 8 * U * V / (q : ℝ)) *
      (1 + 2 * V * (Int.gcd a b : ℝ) / U) := by
  classical
  let D : ℤ × ℤ → ℤ := fun z => b * z.1 - a * z.2
  let center : ℝ := (b : ℝ) * c₁ - (a : ℝ) * c₂
  have hrange : ∀ d ∈ S.image D,
      center - 4 * U * V ≤ (d : ℝ) ∧ (d : ℝ) ≤ center + 4 * U * V := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
    have he : ((D z : ℤ) : ℝ) - center =
        (b : ℝ) * ((z.1 : ℝ) - c₁) - (a : ℝ) * ((z.2 : ℝ) - c₂) := by
      simp only [D, center, Int.cast_sub, Int.cast_mul]
      ring
    have hbnd : |((D z : ℤ) : ℝ) - center| ≤ 4 * U * V := by
      rw [he]
      calc
        _ ≤ |(b : ℝ) * ((z.1 : ℝ) - c₁)| +
            |(a : ℝ) * ((z.2 : ℝ) - c₂)| := abs_sub _ _
        _ = |(b : ℝ)| * |(z.1 : ℝ) - c₁| +
            |(a : ℝ)| * |(z.2 : ℝ) - c₂| := by rw [abs_mul, abs_mul]
        _ ≤ (2 * U) * V + (2 * U) * V := by
          exact add_le_add (mul_le_mul hb2U (hI z hz).1 (abs_nonneg _) (by positivity))
            (mul_le_mul ha2U (hI z hz).2 (abs_nonneg _) (by positivity))
        _ = _ := by ring
    have h := abs_le.mp hbnd
    constructor <;> linarith
  have hD := incidenceIntegerProgression_card_le (S.image D)
    (center - 4 * U * V) (center + 4 * U * V) q d₀ hq
    (by nlinarith [mul_nonneg hU.le hV])
    hrange (by
      intro d hd
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
      exact hS z hz)
  have hfiber (d : ℤ) (_hd : d ∈ S.image D) :
      ((S.filter (fun z => D z = d)).card : ℝ) ≤
        1 + 2 * V * (Int.gcd a b : ℝ) / U := by
    have hf := incidenceDeterminant_fiber_card_le (S.filter (fun z => D z = d))
      a b d ha V c₁ hV (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2) (by
        intro z hz
        exact (hI z (Finset.mem_filter.mp hz).1).1)
    apply hf.trans
    exact add_le_add le_rfl
      (div_le_div_of_nonneg_left (a := 2 * V * (Int.gcd a b : ℝ)) (by positivity) hU haU)
  have hsum : (S.card : ℝ) =
      ∑ d ∈ S.image D, ((S.filter (fun z => D z = d)).card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image D S)
  rw [hsum]
  calc
    _ ≤ ∑ _d ∈ S.image D, (1 + 2 * V * (Int.gcd a b : ℝ) / U) :=
      Finset.sum_le_sum hfiber
    _ = ((S.image D).card : ℝ) * (1 + 2 * V * (Int.gcd a b : ℝ) / U) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 + (center + 4 * U * V - (center - 4 * U * V)) / (q : ℝ)) *
        (1 + 2 * V * (Int.gcd a b : ℝ) / U) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = _ := by ring

#print axioms incidenceIntegerProgression_card_le
#print axioms incidenceDeterminant_fiber_card_le
#print axioms incidenceDeterminant_mod_card_le

end PrimeGap182Audit
