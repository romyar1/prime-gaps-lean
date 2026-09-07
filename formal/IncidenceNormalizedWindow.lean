import IncidenceNormalizedProfile

/-!
# The actual normalized source weight in an incidence window

The profile is the original real smooth function evaluated at
c(ζe+q₀(γλ+ek))/N. Its separated representation and uniform Fourier cost
are derived here. No row/input factorization is supplied as a premise.
-/

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform ContDiff

set_option maxHeartbeats 1000000 in
theorem incidenceNormalizedSourceWindow_bound (hK4 : AllIncidenceRankFourBounds)
    (η c₀ C₀ R : ℝ) (hη : 0 < η) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hR : 0 ≤ R)
    (Ap Ep : ℕ → ℝ) (hAp : ∀ j, 0 ≤ Ap j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ j y, |iteratedDeriv j ψ y| ≤ Ap j * (Real.log x) ^ Ep j) →
      ∀ q : ℕ, ∀ [NeZero q], Squarefree q → ∀ AQ : ZMod q, IsUnit AQ →
      ∀ u : (ZMod q)ˣ, ∀ d : ℕ, Nat.Coprime d q → ∀ r₀ : ℤ,
      ∀ E₁ E₂ e₀ γ₀ shear L : ℝ, 0 < E₁ → 0 < E₂ → 0 ≤ L →
      ∀ w : ℤ × ℤ → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - shear * (z.1 : ℝ) - γ₀| ≤ E₂) →
      ∀ A : Finset ℤ, ∀ I : ℤ → Finset ℤ, ∀ B : ℤ,
      ∀ U V₀ τD : ℝ, 0 < U → 0 ≤ V₀ → 0 ≤ τD →
      (∀ a ∈ A, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U ∧ IsUnit (a : ZMod q)) →
      (∀ a ∈ A, (a.natAbs.divisors.card : ℝ) ≤ τD) →
      ∀ center : ℤ → ℝ,
      (∀ a ∈ A, ∀ k ∈ I a, |(k : ℝ) - center a| ≤ V₀) →
      ∀ coeff : ℤ → ℂ, ∀ β : ℤ → ℤ → ℂ,
      (∀ a ∈ A, ∀ k ∈ I a, ‖β a k‖ ≤ 1) →
      ∀ N c q₀ esc Λ τ ζ : ℝ, N ≠ 0 → c ≠ 0 → q₀ ≠ 0 → esc ≠ 0 → Λ ≠ 0 →
      ∀ erow : ℤ × ℤ → ℝ, ∀ ell : ℤ → ℝ,
      (∀ z, w z ≠ 0 → c₀ ≤ |erow z / esc| ∧ |erow z / esc| ≤ C₀ ∧
        |((z.2 : ℝ) / erow z - τ) * Λ / (N / (c * q₀ * esc))| ≤ 1) →
      (∀ a ∈ A, |ell a / Λ| ≤ 2) →
      (∑' z : ℤ × ℤ, w z * ‖∑ a ∈ A, coeff a * ∑ k ∈ I a,
        β a k * incidenceMatrixMod AQ
          ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
          ((u : ZMod q) * incidenceFareyResidue q B a k) *
          (ψ (c * (ζ * erow z + q₀ * ((z.2 : ℝ) * ell a + erow z * (k : ℝ))) / N) : ℂ)‖ ^ 2) ≤
        (1 + x ^ (2 * η)) * K * L * incidenceWindowScale η q E₁ E₂ *
          ((1 + 8 * U * V₀ / (q : ℝ)) * ((A.card : ℝ) + 8 * V₀ * τD)) *
            ∑ a ∈ A, ‖coeff a‖ ^ 2 := by
  obtain ⟨K, hK, hwin⟩ := incidenceSmoothSourceWindow_uniform_bound
    (V := IncidenceSourceCoordinates) hK4 η hη
  refine ⟨K, hK, ?_⟩
  filter_upwards [incidenceNormalizedProfile_uniform_subpower c₀ C₀ R hc₀ hC₀ hR Ap Ep hAp η hη,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro ψ hψ hsψ hder q _ hq AQ hAQ u d hd r₀
    E₁ E₂ e₀ γ₀ shear L hE₁ hE₂ hL w hw0 hwL hwbox A I B U V₀ τD hU hV₀ hτD
    hA hτ center hI coeff β hβ N c q₀ esc Λ τ ζ hN hc hq₀ hesc hΛ erow ell hrow hell
  obtain ⟨F, hF, hFourier⟩ := hx ψ hψ hsψ hder
  let xr : ℤ × ℤ → IncidenceSourceCoordinates := fun z =>
    incidenceSourceRowCoordinates esc Λ (N / (c * q₀ * esc)) τ (erow z) (z.2 : ℝ)
  let yi : ℤ → ℤ → IncidenceSourceCoordinates := fun a k =>
    incidenceSourceInputCoordinates Λ (N / (c * q₀ * esc)) τ ζ q₀ (ell a) (k : ℝ)
  have hprofile (z : ℤ × ℤ) (hz : w z ≠ 0) (a : ℤ) (ha : a ∈ A) (k : ℤ) :
      F (xr z + yi a k) =
        (ψ (c * (ζ * erow z + q₀ * ((z.2 : ℝ) * ell a + erow z * (k : ℝ))) / N) : ℂ) := by
    have he : erow z ≠ 0 := by
      intro he
      have hh := (hrow z hz).1
      rw [he, zero_div, abs_zero] at hh
      exact hc₀.not_ge hh
    have hh := hF (xr z + yi a k)
    have hcoords :
        c₀ ≤ |(xr z + yi a k) 0| ∧ |(xr z + yi a k) 0| ≤ C₀ ∧
        |(xr z + yi a k) 1| ≤ 1 ∧ |(xr z + yi a k) 2| ≤ 2 := by
      simpa only [xr, yi, incidenceSourceRowCoordinates, incidenceSourceInputCoordinates,
        PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        add_zero, zero_add] using
          And.intro (hrow z hz).1 (And.intro (hrow z hz).2.1
            (And.intro (hrow z hz).2.2 (hell a ha)))
    rw [hh hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2]
    congr 1
    exact congrArg ψ (incidenceSourceCoordinatePolynomial_identity N c q₀ esc Λ τ ζ (erow z)
      (z.2 : ℝ) (ell a) (k : ℝ) hN hc hq₀ hesc hΛ he)
  have hbound := hwin F q hq AQ hAQ u d hd r₀ E₁ E₂ e₀ γ₀ shear L
    hE₁ hE₂ hL w hw0 hwL hwbox A I B U V₀ τD hU hV₀ hτD hA hτ
    center hI coeff β hβ xr yi
  have heq : (∑' z : ℤ × ℤ, w z * ‖∑ a ∈ A, coeff a * ∑ k ∈ I a,
      β a k * incidenceMatrixMod AQ
        ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
        ((u : ZMod q) * incidenceFareyResidue q B a k) * F (xr z + yi a k)‖ ^ 2) =
      ∑' z : ℤ × ℤ, w z * ‖∑ a ∈ A, coeff a * ∑ k ∈ I a,
        β a k * incidenceMatrixMod AQ
          ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
          ((u : ZMod q) * incidenceFareyResidue q B a k) *
          (ψ (c * (ζ * erow z + q₀ * ((z.2 : ℝ) * ell a + erow z * (k : ℝ))) / N) : ℂ)‖ ^ 2 := by
    apply tsum_congr
    intro z
    by_cases hz : w z = 0
    · simp only [hz, zero_mul]
    · congr 3
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [hprofile z hz a ha k]
  rw [heq] at hbound
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hcost : 1 + (∫ ξ : IncidenceSourceCoordinates,
      ‖(𝓕 F : 𝓢(IncidenceSourceCoordinates, ℂ)) ξ‖) ^ 2 ≤ 1 + x ^ (2 * η) := by
    apply add_le_add le_rfl
    calc
      _ ≤ (x ^ η) ^ 2 := pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) hFourier _
      _ = x ^ (2 * η) := by
        rw [pow_two, ← Real.rpow_add hx0]
        congr 1
        ring
  let Bnd := K * L * incidenceWindowScale η q E₁ E₂ *
    ((1 + 8 * U * V₀ / (q : ℝ)) * ((A.card : ℝ) + 8 * V₀ * τD)) *
      ∑ a ∈ A, ‖coeff a‖ ^ 2
  have hBnd : 0 ≤ Bnd := by dsimp only [Bnd, incidenceWindowScale]; positivity
  apply hbound.trans
  calc
    _ = (1 + (∫ ξ : IncidenceSourceCoordinates,
        ‖(𝓕 F : 𝓢(IncidenceSourceCoordinates, ℂ)) ξ‖) ^ 2) * Bnd := by dsimp only [Bnd]; ring
    _ ≤ (1 + x ^ (2 * η)) * Bnd := mul_le_mul_of_nonneg_right hcost hBnd
    _ = _ := by dsimp only [Bnd]; ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceNormalizedSourceWindow_bound
