import IncidenceNormalizedWindow
import IncidencePhysicalCompatibility

/-!
# Actual numerator support and row-independent Farey intervals

Compact support of the original smooth numerator profile determines an
interval for k centred at -τλ-ζ/q₀ on every angular cell. The finite
progression reindexing can therefore use that interval without dropping
terms from a complex sum.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceIntegerInterval (center radius : ℝ) : Finset ℤ :=
  Finset.Icc ⌈center - radius⌉ ⌊center + radius⌋

theorem incidenceIntegerInterval_mem (center radius : ℝ) (k : ℤ) :
    k ∈ incidenceIntegerInterval center radius ↔ |(k : ℝ) - center| ≤ radius := by
  simp only [incidenceIntegerInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem incidenceSourceCoordinate_last_bound (z : IncidenceSourceCoordinates)
    (c₀ R : ℝ) (hc₀ : 0 < c₀) (hz0 : c₀ ≤ |z 0|)
    (hz1 : |z 1| ≤ 1) (hz2 : |z 2| ≤ 2)
    (hP : |incidenceSourceCoordinatePolynomial z| ≤ R) :
    |z 3| ≤ R / c₀ + 2 := by
  have hcross : |z 1 * z 2| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hz1 hz2 (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hsum : |z 1 * z 2 + z 3| ≤ R / c₀ := by
    apply (le_div_iff₀ hc₀).mpr
    calc
      _ ≤ |z 0| * |z 1 * z 2 + z 3| := by
        nlinarith only [mul_le_mul_of_nonneg_right hz0 (abs_nonneg (z 1 * z 2 + z 3))]
      _ = |incidenceSourceCoordinatePolynomial z| := by
        rw [incidenceSourceCoordinatePolynomial, abs_mul]
      _ ≤ R := hP
  have hh := abs_sub (z 1 * z 2 + z 3) (z 1 * z 2)
  rw [show z 1 * z 2 + z 3 - z 1 * z 2 = z 3 by ring] at hh
  linarith

theorem incidencePhysicalNumerator_support
    (ψ : ℝ → ℝ) (R c₀ : ℝ) (hc₀ : 0 < c₀)
    (hs : Function.support ψ ⊆ Set.Icc (-R) R)
    (N c q₀ esc Λ τ ζ e γ ell k : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hq₀ : q₀ ≠ 0) (hesc : esc ≠ 0) (hΛ : Λ ≠ 0)
    (hV : 0 < N / (c * q₀ * esc))
    (he0 : c₀ ≤ |e / esc|)
    (hangular : |(γ / e - τ) * Λ / (N / (c * q₀ * esc))| ≤ 1)
    (hell : |ell / Λ| ≤ 2)
    (hψ : ψ (c * (ζ * e + q₀ * (γ * ell + e * k)) / N) ≠ 0) :
    |k - (-τ * ell - ζ / q₀)| ≤ (R / c₀ + 2) * (N / (c * q₀ * esc)) := by
  have he : e ≠ 0 := by
    intro he
    rw [he, zero_div, abs_zero] at he0
    exact hc₀.not_ge he0
  let z := incidenceSourceRowCoordinates esc Λ (N / (c * q₀ * esc)) τ e γ +
    incidenceSourceInputCoordinates Λ (N / (c * q₀ * esc)) τ ζ q₀ ell k
  have hz0 : c₀ ≤ |z 0| := by simpa [z, incidenceSourceRowCoordinates, incidenceSourceInputCoordinates] using he0
  have hz1 : |z 1| ≤ 1 := by simpa [z, incidenceSourceRowCoordinates, incidenceSourceInputCoordinates] using hangular
  have hz2 : |z 2| ≤ 2 := by simpa [z, incidenceSourceRowCoordinates, incidenceSourceInputCoordinates] using hell
  have hpoly : incidenceSourceCoordinatePolynomial z = c * (ζ * e + q₀ * (γ * ell + e * k)) / N :=
    incidenceSourceCoordinatePolynomial_identity N c q₀ esc Λ τ ζ e γ ell k hN hc hq₀ hesc hΛ he
  have hP : |incidenceSourceCoordinatePolynomial z| ≤ R := by
    rw [hpoly, abs_le]
    exact hs hψ
  have hb := incidenceSourceCoordinate_last_bound z c₀ R hc₀ hz0 hz1 hz2 hP
  have hz3 : z 3 = (k + τ * ell + ζ / q₀) / (N / (c * q₀ * esc)) := by
    simp [z, incidenceSourceRowCoordinates, incidenceSourceInputCoordinates]
  rw [hz3, abs_div, abs_of_pos hV] at hb
  have hlin : k - (-τ * ell - ζ / q₀) = k + τ * ell + ζ / q₀ := by ring
  rw [hlin]
  exact (div_le_iff₀ hV).mp hb

theorem incidenceProgressionIndex_mem (a b : ℤ) (ha : a ≠ 0) (I : Finset ℤ) (k : ℤ) :
    k ∈ (I.filter (fun n => Int.ModEq a b n)).image (fun n => (n - b) / a) ↔
      b + a * k ∈ I := by
  constructor
  · intro hk
    obtain ⟨n, hn, hnk⟩ := Finset.mem_image.mp hk
    have hid : b + a * ((n - b) / a) = n := by
      rw [Int.mul_ediv_cancel' (Int.modEq_iff_dvd.mp (Finset.mem_filter.mp hn).2)]
      ring
    rw [← hnk, hid]
    exact (Finset.mem_filter.mp hn).1
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨b + a * k, Finset.mem_filter.mpr ⟨hn, ?_⟩, ?_⟩
    · rw [Int.modEq_iff_dvd, add_sub_cancel_left]
      exact dvd_mul_right _ _
    · rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ ha]

theorem incidenceFiniteSum_eq_of_support {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (S T : Finset ι) (f : ι → M)
    (hS : ∀ i, f i ≠ 0 → i ∈ S) (hT : ∀ i, f i ≠ 0 → i ∈ T) :
    (∑ i ∈ S, f i) = ∑ i ∈ T, f i := by
  have hzeroS (i : ι) (_ : i ∈ S ∪ T) (hi : i ∉ S) : f i = 0 :=
    not_not.mp (fun h => hi (hS i h))
  have hzeroT (i : ι) (_ : i ∈ S ∪ T) (hi : i ∉ T) : f i = 0 :=
    not_not.mp (fun h => hi (hT i h))
  exact (Finset.sum_subset Finset.subset_union_left hzeroS).trans
    (Finset.sum_subset Finset.subset_union_right hzeroT).symm

theorem incidenceOriginalProgression_window_sum
    (a b : ℤ) (ha : a ≠ 0) (I J : Finset ℤ) (ψ G : ℤ → ℂ)
    (hI : ∀ n, ψ n ≠ 0 → n ∈ I)
    (hJ : ∀ k, ψ (b + a * k) ≠ 0 → k ∈ J) :
    (∑ n ∈ I, if Int.ModEq a b n then ψ n * G n else 0) =
      ∑ k ∈ J, ψ (b + a * k) * G (b + a * k) := by
  rw [incidenceProgression_sum_reindex]
  apply incidenceFiniteSum_eq_of_support
  · intro k hk
    rw [incidenceProgressionIndex_mem a b ha]
    exact hI _ (left_ne_zero_of_mul hk)
  · intro k hk
    exact hJ _ (left_ne_zero_of_mul hk)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceIntegerInterval_mem
#print axioms PrimeGap182Audit.incidenceSourceCoordinate_last_bound
#print axioms PrimeGap182Audit.incidencePhysicalNumerator_support
#print axioms PrimeGap182Audit.incidenceProgressionIndex_mem
#print axioms PrimeGap182Audit.incidenceFiniteSum_eq_of_support
#print axioms PrimeGap182Audit.incidenceOriginalProgression_window_sum
