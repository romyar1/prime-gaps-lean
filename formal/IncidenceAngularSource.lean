import IncidenceNumeratorSupport

/-!
# The full angular sum of an actual reduced source response

The numerator index is summed over all integers. Compact support proves
the cell-dependent Farey interval, and exact floor cells partition all
original γ rows. Summing the proved window estimates cancels J from
the area term. Only the nonzero-mode terms pay the cell count.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators ContDiff

def incidenceUnrestrictedSourceResponse {q : ℕ} [NeZero q]
    (AQ : ZMod q) (u : (ZMod q)ˣ) (d : ℕ) (r₀ : ℤ) (A : Finset ℤ) (B : ℤ)
    (coeff : ℤ → ℂ) (β : ℤ → ℤ → ℂ) (ψ : ℝ → ℝ)
    (N c q₀ ζ : ℝ) (erow : ℤ × ℤ → ℝ) (ell : ℤ → ℝ) (z : ℤ × ℤ) : ℂ :=
  ∑ a ∈ A, coeff a * ∑' k : ℤ,
    β a k * incidenceMatrixMod AQ
      ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
      ((u : ZMod q) * incidenceFareyResidue q B a k) *
      (ψ (c * (ζ * erow z + q₀ * ((z.2 : ℝ) * ell a + erow z * (k : ℝ))) / N) : ℂ)

set_option maxHeartbeats 1600000 in
theorem incidenceAngularSource_bound (hK4 : AllIncidenceRankFourBounds)
    (η c₀ R : ℝ) (hη : 0 < η) (hc₀ : 0 < c₀) (hR : 0 ≤ R)
    (Ap Ep : ℕ → ℝ) (hAp : ∀ j, 0 ≤ Ap j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ j y, |iteratedDeriv j ψ y| ≤ Ap j * (Real.log x) ^ Ep j) →
      ∀ q : ℕ, ∀ [NeZero q], Squarefree q → ∀ AQ : ZMod q, IsUnit AQ →
      ∀ u : (ZMod q)ˣ, ∀ d : ℕ, Nat.Coprime d q → ∀ r₀ : ℤ,
      ∀ N c q₀ esc Λ t ζ E₁ e₀ L : ℝ,
      0 < N → 0 < c → 0 < q₀ → 0 < esc → 0 < Λ → 0 < E₁ → 0 ≤ L →
      ∀ J : ℕ, 0 < J → Λ ≤ (J : ℝ) * (N / (c * q₀ * esc)) →
      ∀ w : ℤ × ℤ → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 →
        |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        c₀ * esc ≤ t * ((d : ℝ) * (z.1 : ℝ) + (r₀ : ℝ)) ∧
        t * ((d : ℝ) * (z.1 : ℝ) + (r₀ : ℝ)) ≤ 2 * esc ∧
        0 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) < t * ((d : ℝ) * (z.1 : ℝ) + (r₀ : ℝ))) →
      ∀ A : Finset ℤ, ∀ B : ℤ, ∀ U τD : ℝ, 0 < U → 0 ≤ τD →
      (∀ a ∈ A, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U ∧ IsUnit (a : ZMod q)) →
      (∀ a ∈ A, (a.natAbs.divisors.card : ℝ) ≤ τD) →
      ∀ ell : ℤ → ℝ, (∀ a ∈ A, |ell a / Λ| ≤ 2) →
      ∀ coeff : ℤ → ℂ, ∀ β : ℤ → ℤ → ℂ, (∀ a ∈ A, ∀ k : ℤ, ‖β a k‖ ≤ 1) →
      let V₀ := (R / c₀ + 2) * (N / (c * q₀ * esc))
      let erow : ℤ × ℤ → ℝ := fun z => t * ((d : ℝ) * (z.1 : ℝ) + (r₀ : ℝ))
      (∑' z : ℤ × ℤ, w z *
        ‖incidenceUnrestrictedSourceResponse AQ u d r₀ A B coeff β ψ N c q₀ ζ erow ell z‖ ^ 2) ≤
      (1 + x ^ (2 * η)) * K * L *
        (2 * E₁ * esc + (J : ℝ) * (q : ℝ) ^ (3 / 2 + η) +
          (q : ℝ) ^ (1 / 2 + η) * ((J : ℝ) * E₁ + 2 * esc)) *
        ((1 + 8 * U * V₀ / (q : ℝ)) * ((A.card : ℝ) + 8 * V₀ * τD)) *
          ∑ a ∈ A, ‖coeff a‖ ^ 2 := by
  obtain ⟨K, hK, hwindow⟩ := incidenceNormalizedSourceWindow_bound hK4 η c₀ 2 R
    hη hc₀ (by norm_num) hR Ap Ep hAp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hwindow] with x hx
  intro ψ hψ hsψ hder q _ hq AQ hAQ u d hd r₀ N c q₀ esc Λ t ζ E₁ e₀ L
    hN hc hq₀ hesc hΛ hE₁ hL J hJ hJscale w hw0 hwL hwbox A B U τD hU hτD
    hA hτ ell hell coeff β hβ V₀ erow
  let V := N / (c * q₀ * esc)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hV₀ : 0 < V₀ := by dsimp only [V₀]; positivity
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  let E₂ := 2 * esc / (J : ℝ)
  have hE₂ : 0 < E₂ := by dsimp only [E₂]; positivity
  let τ : ℕ → ℝ := fun j => (j : ℝ) / (J : ℝ)
  let I : ℕ → ℤ → Finset ℤ := fun j a =>
    incidenceIntegerInterval (-τ j * ell a - ζ / q₀) V₀
  let Resp : ℤ × ℤ → ℂ := incidenceUnrestrictedSourceResponse AQ u d r₀ A B coeff β ψ
    N c q₀ ζ erow ell
  have hepos (z : ℤ × ℤ) (hz : w z ≠ 0) : 0 < erow z :=
    (mul_pos hc₀ hesc).trans_le (hwbox z hz).2.1
  have hnorme (z : ℤ × ℤ) (hz : w z ≠ 0) :
      c₀ ≤ |erow z / esc| ∧ |erow z / esc| ≤ 2 := by
    rw [abs_of_pos (div_pos (hepos z hz) hesc)]
    exact ⟨(le_div_iff₀ hesc).mpr (hwbox z hz).2.1,
      (div_le_iff₀ hesc).mpr (hwbox z hz).2.2.1⟩
  have hangular (z : ℤ × ℤ) (hz : w z ≠ 0) :
      let j := incidenceAngularIndex J (erow z) (z.2 : ℝ)
      |((z.2 : ℝ) / erow z - τ j) * Λ / V| ≤ 1 ∧
        |(z.2 : ℝ) - τ j * erow z| ≤ E₂ := by
    simpa only [one_mul, mul_one, div_one] using
      incidenceAngularWindow_spec J hJ Λ V esc 1 (erow z) (z.2 : ℝ)
        hΛ hV hJscale zero_lt_one (hepos z hz) (hwbox z hz).2.2.1
        (hwbox z hz).2.2.2.1 (hwbox z hz).2.2.2.2
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (hw0 z) (sq_nonneg _))
  intro S
  let W : ℕ → ℤ × ℤ → ℝ := fun j z =>
    if z ∈ S ∧ incidenceAngularIndex J (erow z) (z.2 : ℝ) = j then w z else 0
  have hactive (j : ℕ) (z : ℤ × ℤ) (hz : W j z ≠ 0) :
      w z ≠ 0 ∧ incidenceAngularIndex J (erow z) (z.2 : ℝ) = j := by
    by_cases h : z ∈ S ∧ incidenceAngularIndex J (erow z) (z.2 : ℝ) = j
    · exact ⟨fun hzero => hz (by simp only [W, ite_eq_left h, hzero]), h.2⟩
    · exact False.elim (hz (by simp only [W, ite_eq_right h]))
  have hW0 (j : ℕ) (z : ℤ × ℤ) : 0 ≤ W j z := by
    dsimp only [W]
    split_ifs
    · exact hw0 z
    · rfl
  have hWL (j : ℕ) (z : ℤ × ℤ) : W j z ≤ L := by
    dsimp only [W]
    split_ifs
    · exact hwL z
    · exact hL
  have hWbox (j : ℕ) (z : ℤ × ℤ) (hz : W j z ≠ 0) :
      |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - (τ j * t * (d : ℝ)) * (z.1 : ℝ) - τ j * t * (r₀ : ℝ)| ≤ E₂ := by
    obtain ⟨hwz, hj⟩ := hactive j z hz
    refine ⟨(hwbox z hwz).1, ?_⟩
    have h := (hangular z hwz).2
    rw [hj] at h
    convert h using 2
    dsimp only [erow]
    ring
  have hnorm (j : ℕ) (z : ℤ × ℤ) (hz : W j z ≠ 0) :
      c₀ ≤ |erow z / esc| ∧ |erow z / esc| ≤ 2 ∧
        |((z.2 : ℝ) / erow z - τ j) * Λ / V| ≤ 1 := by
    obtain ⟨hwz, hj⟩ := hactive j z hz
    have h := (hangular z hwz).1
    rw [hj] at h
    exact ⟨(hnorme z hwz).1, (hnorme z hwz).2, h⟩
  have hresp (j : ℕ) (z : ℤ × ℤ) (hz : W j z ≠ 0) :
      Resp z = ∑ a ∈ A, coeff a * ∑ k ∈ I j a,
        β a k * incidenceMatrixMod AQ
          ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
          ((u : ZMod q) * incidenceFareyResidue q B a k) *
          (ψ (c * (ζ * erow z + q₀ * ((z.2 : ℝ) * ell a + erow z * (k : ℝ))) / N) : ℂ) := by
    dsimp only [Resp, incidenceUnrestrictedSourceResponse]
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    apply tsum_eq_sum
    intro k hk
    have hzero : ψ (c * (ζ * erow z + q₀ * ((z.2 : ℝ) * ell a + erow z * (k : ℝ))) / N) = 0 := by
      by_contra hne
      apply hk
      change k ∈ incidenceIntegerInterval (-τ j * ell a - ζ / q₀) V₀
      rw [incidenceIntegerInterval_mem]
      exact incidencePhysicalNumerator_support ψ R c₀ hc₀ hsψ N c q₀ esc Λ (τ j) ζ (erow z)
        (z.2 : ℝ) (ell a) (k : ℝ) hN.ne' hc.ne' hq₀.ne' hesc.ne' hΛ.ne' hV
        (hnorm j z hz).1 (hnorm j z hz).2.2 (hell a ha) hne
    rw [hzero, Complex.ofReal_zero, mul_zero]
  let CellBound := (1 + x ^ (2 * η)) * K * L * incidenceWindowScale η q E₁ E₂ *
    ((1 + 8 * U * V₀ / (q : ℝ)) * ((A.card : ℝ) + 8 * V₀ * τD)) *
      ∑ a ∈ A, ‖coeff a‖ ^ 2
  have hjbound (j : ℕ) : (∑ z ∈ S, W j z * ‖Resp z‖ ^ 2) ≤ CellBound := by
    have hb := hx ψ hψ hsψ hder q hq AQ hAQ u d hd r₀ E₁ E₂ e₀
      (τ j * t * (r₀ : ℝ)) (τ j * t * (d : ℝ)) L hE₁ hE₂ hL
      (W j) (hW0 j) (hWL j) (hWbox j) A (I j) B U V₀ τD hU hV₀.le hτD hA hτ
      (fun a => -τ j * ell a - ζ / q₀)
      (fun a _ k hk => (incidenceIntegerInterval_mem _ _ k).mp hk)
      coeff β (fun a ha k _ => hβ a ha k) N c q₀ esc Λ (τ j) ζ
      hN.ne' hc.ne' hq₀.ne' hesc.ne' hΛ.ne' erow ell (hnorm j) hell
    rw [tsum_eq_sum (s := S) (fun z hz => by simp [W, hz])] at hb
    apply le_trans _ hb
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : W j z = 0
    · simp only [hz, zero_mul, le_refl]
    · rw [hresp j z hz]
  have hsplit : (∑ z ∈ S, w z * ‖Resp z‖ ^ 2) =
      ∑ j ∈ Finset.range J, ∑ z ∈ S, W j z * ‖Resp z‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hwz : w z = 0
    · simp only [W, hwz, ite_self, zero_mul, Finset.sum_const_zero]
    · have hi := (incidenceAngularIndex_spec J hJ (erow z) (z.2 : ℝ)
        (hepos z hwz) (hwbox z hwz).2.2.2.1 (hwbox z hwz).2.2.2.2).1
      simp [W, hz, hi, ite_mul]
  change (∑ z ∈ S, w z * ‖Resp z‖ ^ 2) ≤ _
  rw [hsplit]
  calc
    _ ≤ ∑ _j ∈ Finset.range J, CellBound := Finset.sum_le_sum (fun j _ => hjbound j)
    _ = (J : ℝ) * CellBound := by simp
    _ = _ := by
      dsimp only [CellBound, E₂, incidenceWindowScale]
      field_simp

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceAngularSource_bound
