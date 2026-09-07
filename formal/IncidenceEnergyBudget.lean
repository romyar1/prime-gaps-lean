import IncidenceContributionSaving

/-!
# Collection of the actual positive energy prefactors

The two outside factors q₀ κ cancel against the raw energy normalization.
This finite inequality retains every divisor, window and Taylor factor.
The hypotheses in these lemmas are scalar bounds used by the source
assembly; they do not assert a source-distribution estimate.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

set_option maxHeartbeats 1600000

theorem incidenceMaskedMain_collect
    {ι : Type*} (W : Finset ι) (T : ι → ℝ)
    (E P q₀ κ v₀ N τw τe Win K Lrow Ccard τa saving : ℝ)
    (hP : 1 ≤ P) (hq₀ : 0 ≤ q₀) (hκ : 0 ≤ κ) (hv₀ : 0 < v₀) (hN : 0 < N)
    (hsaving : 0 ≤ saving)
    (hτw : 0 ≤ τw ∧ τw ≤ P) (hτe : 0 ≤ τe ∧ τe ≤ P)
    (hWin : 0 ≤ Win ∧ Win ≤ P) (hK : 0 ≤ K ∧ K ≤ P)
    (hLrow : 0 ≤ Lrow ∧ Lrow ≤ P)
    (hCcard : 0 ≤ Ccard ∧ Ccard ≤ P) (hτa : 0 ≤ τa ∧ τa ≤ P)
    (hcard : (W.card : ℝ) ≤ P)
    (hterms : ∀ c ∈ W, T c / (v₀ ^ 2 * N ^ 2) ≤ saving)
    (hE : E ≤ τw * κ * τe *
      (q₀ * κ * (Win * K * Lrow) * (9 * q₀ * (Ccard + 8 * τa))) *
        ∑ c ∈ W, T c) :
    E ≤ (q₀ * κ * v₀ * N) ^ 2 * (81 * P ^ 7 * saving) := by
  rcases hτw with ⟨hτw0, hτw⟩
  rcases hτe with ⟨hτe0, hτe⟩
  rcases hWin with ⟨hWin0, hWin⟩
  rcases hK with ⟨hK0, hK⟩
  rcases hLrow with ⟨hLrow0, hLrow⟩
  rcases hCcard with ⟨hCcard0, hCcard⟩
  rcases hτa with ⟨hτa0, hτa⟩
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hsum : (∑ c ∈ W, T c) ≤ P * (v₀ ^ 2 * N ^ 2 * saving) := by
    calc
      _ ≤ ∑ _c ∈ W, v₀ ^ 2 * N ^ 2 * saving := by
        apply Finset.sum_le_sum
        intro c hc
        have hh := (div_le_iff₀ (by positivity : 0 < v₀ ^ 2 * N ^ 2)).mp (hterms c hc)
        simpa only [mul_comm] using hh
      _ = (W.card : ℝ) * (v₀ ^ 2 * N ^ 2 * saving) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hfactor : Ccard + 8 * τa ≤ 9 * P := by linarith only [hCcard, hτa]
  apply hE.trans
  calc
    _ ≤ τw * κ * τe *
        (q₀ * κ * (Win * K * Lrow) * (9 * q₀ * (Ccard + 8 * τa))) *
          (P * (v₀ ^ 2 * N ^ 2 * saving)) := by
      apply mul_le_mul_of_nonneg_left hsum
      positivity
    _ ≤ P * κ * P *
        (q₀ * κ * (P * P * P) * (9 * q₀ * (9 * P))) *
          (P * (v₀ ^ 2 * N ^ 2 * saving)) := by
      gcongr
    _ = _ := by ring

theorem incidenceTaylorMain_collect (J : ℕ) (E : ℕ → ℝ)
    (x ε P scale : ℝ) (hx : 1 ≤ x) (hε : 0 < ε)
    (hP : 1 ≤ P) (hPs : P ≤ x ^ (ε / 100)) (hscale : 0 ≤ scale)
    (hJ : 162 * (J + 1 : ℕ) ^ 2 ≤ P)
    (hE : ∀ j ≤ J, E j ≤ scale * (81 * P ^ 7 * x ^ (-49 * ε))) :
    2 * (J + 1 : ℕ) * (∑ j ∈ Finset.range (J + 1), E j) ≤
      scale * x ^ (-48 * ε) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hsum : (∑ j ∈ Finset.range (J + 1), E j) ≤
      (J + 1 : ℕ) * (scale * (81 * P ^ 7 * x ^ (-49 * ε))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (J + 1), scale * (81 * P ^ 7 * x ^ (-49 * ε)) :=
        Finset.sum_le_sum (fun j hj => hE j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hp : P ^ 8 * x ^ (-49 * ε) ≤ x ^ (-48 * ε) := by
    calc
      _ ≤ (x ^ (ε / 100)) ^ 8 * x ^ (-49 * ε) := by gcongr
      _ = x ^ (8 * (ε / 100) - 49 * ε) := by
        rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc
    _ ≤ 2 * (J + 1 : ℕ) *
        ((J + 1 : ℕ) * (scale * (81 * P ^ 7 * x ^ (-49 * ε)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = scale * ((162 * (J + 1 : ℕ) ^ 2) * P ^ 7 * x ^ (-49 * ε)) := by ring
    _ ≤ scale * (P * P ^ 7 * x ^ (-49 * ε)) := by gcongr
    _ = scale * (P ^ 8 * x ^ (-49 * ε)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hscale

theorem incidenceRawTaylor_collect (x ε scale E Main Err : ℝ)
    (hx : 1 ≤ x) (hε : 0 < ε) (hscale : 1 ≤ scale) (hxlarge : 2 ≤ x ^ ε)
    (hE : E ≤ Main + Err) (hMain : Main ≤ scale * x ^ (-48 * ε))
    (hErr : Err ≤ x ^ (-48 * ε)) :
    E ≤ scale * x ^ (-40 * ε) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hscale0 : 0 ≤ scale := zero_le_one.trans hscale
  have hErr' : Err ≤ scale * x ^ (-48 * ε) :=
    hErr.trans (le_mul_of_one_le_left (by positivity) hscale)
  calc
    E ≤ scale * (2 * x ^ (-48 * ε)) := by linarith only [hE, hMain, hErr']
    _ ≤ scale * (x ^ ε * x ^ (-48 * ε)) := by gcongr
    _ = scale * x ^ (-47 * ε) := by rw [← Real.rpow_add hx0]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hscale0

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceMaskedMain_collect
#print axioms PrimeGap182Audit.incidenceTaylorMain_collect
#print axioms PrimeGap182Audit.incidenceRawTaylor_collect
