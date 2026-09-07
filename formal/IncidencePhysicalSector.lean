import IncidenceReducedResponse
import IncidenceSourceRowReindex

/-!
# The actual physical t-sector satisfies the incidence window estimate

The left side retains the original progression response and its γ
coordinate. The q₀ coefficient phase, g input pole mask, and affine
row substitution are all derived from the literal phase identity.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators ContDiff

set_option maxHeartbeats 2200000 in
set_option backward.isDefEq.respectTransparency false in
theorem incidencePhysicalSector_window_bound (hK4 : AllIncidenceRankFourBounds)
    (η c₀ R : ℝ) (hη : 0 < η) (hc₀ : 0 < c₀) (hR : 0 ≤ R)
    (Ap Ep : ℕ → ℝ) (hAp : ∀ j, 0 ≤ Ap j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ j y, |iteratedDeriv j ψ y| ≤ Ap j * (Real.log x) ^ Ep j) →
      ∀ q₀ g q : ℕ, ∀ [NeZero q₀] [NeZero g] [NeZero q],
      Nat.Coprime q₀ (g * q) → Nat.Coprime g q → Squarefree q →
      ∀ A B ζ r₀ Bhat : ℤ, IsUnit (A : ZMod q) →
      (Bhat : ZMod (g * q)) =
        (q₀ : ZMod (g * q))⁻¹ * ((B : ZMod (g * q)) + (ζ : ZMod (g * q))) →
      ∀ t w₂ : ℕ, Nat.Coprime t q → Nat.Coprime w₂ q → g ∣ w₂ →
      ∀ e₀ : ZMod q₀, ∀ N c esc Λ E₁ eCenter L : ℝ,
      0 < N → 0 < c → 0 < esc → 0 < Λ → 0 < E₁ → 0 ≤ L →
      ∀ J : ℕ, 0 < J → Λ ≤ (J : ℝ) * (N / (c * (q₀ : ℝ) * esc)) →
      ∀ Rows : Finset (ℕ × ℤ), ∀ ρ : ℕ × ℤ → ℝ,
      (∀ p ∈ Rows, 0 ≤ ρ p ∧ ρ p ≤ L) →
      (∀ p ∈ Rows, (t : ℤ) ∣ (p.1 : ℤ) ∧
        Int.ModEq (q₀ : ℤ) r₀ ((p.1 : ℤ) / (t : ℤ)) ∧
        (p.1 : ZMod q₀) = e₀ ∧ Nat.Coprime p.1 g ∧
        |((incidenceSourceRowLabel t q₀ r₀ p).1 : ℝ) - eCenter| ≤ E₁ ∧
        c₀ * esc ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * esc ∧
        0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < (p.1 : ℝ)) →
      ∀ S : Finset ℤ, ∀ U τD : ℝ, 0 < U → 0 ≤ τD →
      (∀ a ∈ S, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U ∧ IsUnit (a : ZMod q)) →
      (∀ a ∈ S, (a.natAbs.divisors.card : ℝ) ≤ τD) →
      (∀ a ∈ S, |((((t * w₂ : ℕ) : ℤ) * a : ℤ) : ℝ) / Λ| ≤ 2) →
      ∀ coeff : ℤ → ℂ,
      let V₀ := (R / c₀ + 2) * (N / (c * (q₀ : ℝ) * esc))
      (∑ p ∈ Rows, ρ p *
        ‖∑ a ∈ S, coeff (((t * w₂ : ℕ) : ℤ) * a) *
          incidenceProgressionResponse (m := q₀ * (g * q)) (A : ZMod _) B q₀ p.1 ζ p.2
            (fun n => (ψ (c * (n : ℝ) / N) : ℂ)) (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2) ≤
        (1 + x ^ (2 * η)) * K * L *
          (2 * E₁ * esc + (J : ℝ) * (q : ℝ) ^ (3 / 2 + η) +
            (q : ℝ) ^ (1 / 2 + η) * ((J : ℝ) * E₁ + 2 * esc)) *
          ((1 + 8 * U * V₀ / (q : ℝ)) * ((S.card : ℝ) + 8 * V₀ * τD)) *
            ∑ a ∈ S, ‖coeff (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2 := by
  obtain ⟨K, hK, hwindow⟩ := incidenceAngularSource_bound hK4 η c₀ R hη hc₀ hR Ap Ep hAp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hwindow, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro ψ hψ hsψ hder q₀ g q _ _ _ h0 hg hq A B ζ r₀ Bhat hA hBhat
    t w₂ ht hw hgw e₀ N c esc Λ E₁ eCenter L hN hc hesc hΛ hE₁ hL J hJ hJscale
    Rows ρ hρ hRows S U τD hU hτD hS hτ hell coeff V₀
  have hq₀q : Nat.Coprime q₀ q := (Nat.coprime_mul_iff_right.mp h0).2
  have hq₀R : 0 < (q₀ : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q₀))
  let st : (ZMod q)ˣ := ZMod.unitOfCoprime t ht
  let u : (ZMod q)ˣ := (ZMod.unitOfCoprime w₂ hw)⁻¹
  let AQ := incidenceReducedSourceCoefficient q₀ g A 1 st
  have hAQ : IsUnit AQ := incidenceReducedSourceCoefficient_isUnit q₀ g A 1 st hq₀q hg hA
  let erow : ℤ × ℤ → ℝ := fun z => (t : ℝ) * ((q₀ : ℝ) * (z.1 : ℝ) + (r₀ : ℝ))
  let ell : ℤ → ℝ := fun a => ((((t * w₂ : ℕ) : ℤ) * a : ℤ) : ℝ)
  let ca : ℤ → ℂ := fun a => coeff (((t * w₂ : ℕ) : ℤ) * a) *
    incidenceSourceCoefficientPhase q₀ g q A B ζ (t : ℤ) ((w₂ : ℤ) * a) e₀
  let β : ℤ → ℤ → ℂ := fun _ k => incidenceReducedInputMask g Bhat k
  let W := incidenceSourceRowWeight t q₀ r₀ Rows ρ
  have htd : ∀ p ∈ Rows, (t : ℤ) ∣ (p.1 : ℤ) := fun p hp => (hRows p hp).1
  have hpr : ∀ p ∈ Rows, Int.ModEq (q₀ : ℤ) r₀ ((p.1 : ℤ) / (t : ℤ)) :=
    fun p hp => (hRows p hp).2.1
  have hW0 (z : ℤ × ℤ) : 0 ≤ W z :=
    incidenceSourceRowWeight_nonneg t q₀ r₀ Rows ρ (fun p hp => (hρ p hp).1) z
  have hWL (z : ℤ × ℤ) : W z ≤ L :=
    incidenceSourceRowWeight_le t q₀ r₀ Rows htd hpr ρ L hL (fun p hp => (hρ p hp).2) z
  have hWbox (z : ℤ × ℤ) (hz : W z ≠ 0) :
      |(z.1 : ℝ) - eCenter| ≤ E₁ ∧ c₀ * esc ≤ erow z ∧ erow z ≤ 2 * esc ∧
        0 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) < erow z := by
    obtain ⟨p, hp, heq, _⟩ := incidenceSourceRowWeight_support t q₀ r₀ Rows ρ z hz
    have heI := incidenceSourceRowLabel_spec t q₀ r₀ p (htd p hp) (hpr p hp)
    have heR : (p.1 : ℝ) = erow z := by
      rw [heq] at heI
      simpa only [erow, Int.cast_natCast, Int.cast_mul, Int.cast_add] using
        congrArg (fun n : ℤ => (n : ℝ)) heI
    have hγ : p.2 = z.2 := congrArg (fun z : ℤ × ℤ => z.2) heq
    simpa only [heq, heR, hγ] using (hRows p hp).2.2.2.2
  have hb := hx ψ hψ hsψ hder q hq AQ hAQ u q₀ hq₀q r₀ N c (q₀ : ℝ) esc Λ
    (t : ℝ) (ζ : ℝ) E₁ eCenter L hN hc hq₀R hesc hΛ hE₁ hL J hJ hJscale
    W hW0 hWL hWbox S Bhat U τD hU hτD hS hτ ell hell ca β
    (fun _ _ k => incidenceReducedInputMask_norm g Bhat k)
  let Resp := incidenceUnrestrictedSourceResponse AQ u q₀ r₀ S Bhat ca β ψ
    N c (q₀ : ℝ) (ζ : ℝ) erow ell
  have hid : (∑ p ∈ Rows, ρ p *
      ‖∑ a ∈ S, coeff (((t * w₂ : ℕ) : ℤ) * a) *
        incidenceProgressionResponse (m := q₀ * (g * q)) (A : ZMod _) B q₀ p.1 ζ p.2
          (fun n => (ψ (c * (n : ℝ) / N) : ℂ)) (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2) =
      ∑' z : ℤ × ℤ, W z * ‖Resp z‖ ^ 2 := by
    rw [incidenceSourceRowWeight_sum t q₀ r₀ Rows htd hpr ρ (fun z => ‖Resp z‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro p hp
    congr 2
    apply congrArg norm
    exact incidenceSourceSector_eq_response h0 hg A B ζ r₀ Bhat t w₂ p.1 ht hw hgw
      (hRows p hp).2.2.2.1 e₀ (hRows p hp).2.2.1 hBhat
      (incidenceSourceRowLabel t q₀ r₀ p) (incidenceSourceRowLabel_spec t q₀ r₀ p (htd p hp) (hpr p hp))
      S (fun a ha => (hS a ha).2.2) coeff ψ N c
  rw [hid]
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro a _
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (incidenceSourceCoefficientPhase_norm q₀ g q A B ζ (t : ℤ) ((w₂ : ℤ) * a) e₀)
      (norm_nonneg _)).trans_eq (mul_one _)
  · have hx0 : 0 ≤ x := zero_le_one.trans hx1
    positivity

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePhysicalSector_window_bound
