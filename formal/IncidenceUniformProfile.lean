import IncidenceCompactPullback

/-!
# Uniform Fourier separation cost for actual compact source families

The constants here depend on a fixed compact pullback map and the fixed
derivative envelopes, and not on the member of the source family. All
Fourier integrals are those of actual Schwartz functions.
-/

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem incidenceSchwartzFourierL1_seminorm_bound
    (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(V, ℂ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ℝ, ℂ),
      (∫ ξ : V, ‖(𝓕 (T f) : 𝓢(V, ℂ)) ξ‖) ≤
        C * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  let L : 𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ 1 (volume : Measure V) :=
    (SchwartzMap.toLpCLM ℂ ℂ 1 volume).comp
      ((SchwartzMap.fourierTransformCLM ℂ).comp T)
  let q : Seminorm ℂ 𝓢(ℝ, ℂ) := (normSeminorm ℂ (Lp ℂ 1 (volume : Measure V))).comp
    L.toLinearMap
  have hq : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  refine ⟨s, C, by exact_mod_cast (pos_iff_ne_zero.mpr hC), ?_⟩
  intro f
  have hh := hbound f
  change ‖((𝓕 (T f) : 𝓢(V, ℂ)).toLp 1 volume)‖ ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f at hh
  rwa [SchwartzMap.norm_toLp_one] at hh

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem incidenceCompactSupport_seminorm_bound (f : 𝓢(ℝ, ℂ))
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hf : tsupport f ⊆ Set.Icc (-R) R) (k n : ℕ)
    (hder : ∀ x : ℝ, ‖iteratedDeriv n f x‖ ≤ L) :
    SchwartzMap.seminorm ℂ k n f ≤ R ^ k * L := by
  apply SchwartzMap.seminorm_le_bound ℂ k n f (mul_nonneg (pow_nonneg hR _) hL)
  intro x
  by_cases hx : x ∈ tsupport f
  · have habs : ‖x‖ ≤ R := by
      rw [Real.norm_eq_abs, abs_le]
      exact hf hx
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) habs k)
      (by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hder x)
      (norm_nonneg _) (pow_nonneg hR _)
  · have hz : iteratedFDeriv ℝ n f x = 0 := by
      apply Function.notMem_support.mp
      exact fun hi => hx ((support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := (f : ℝ → ℂ)) n) hi)
    simp only [hz, norm_zero, mul_zero]
    exact mul_nonneg (pow_nonneg hR _) hL

set_option maxHeartbeats 1000000 in
theorem incidenceSchwartzFourierL1_log_bound
    (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(V, ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (A E : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ (x : ℝ) (f : 𝓢(ℝ, ℂ)),
      1 ≤ Real.log x → tsupport f ⊆ Set.Icc (-R) R →
      (∀ n y, ‖iteratedDeriv n f y‖ ≤ A n * (Real.log x) ^ E n) →
      (∫ ξ : V, ‖(𝓕 (T f) : 𝓢(V, ℂ)) ξ‖) ≤ C * (Real.log x) ^ D := by
  classical
  obtain ⟨s, C₀, hC₀, hT⟩ := incidenceSchwartzFourierL1_seminorm_bound T
  let D : ℝ := ∑ p ∈ s, |E p.2|
  let B : ℝ := 1 + ∑ p ∈ s, R ^ p.1 * A p.2
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun p _ => mul_nonneg (pow_nonneg hR _) (hA p.2)))
  refine ⟨C₀ * B, D, mul_pos hC₀ hB, hD, ?_⟩
  intro x f hx hf hder
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hx
  have hsemi : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f ≤ B * (Real.log x) ^ D := by
    apply Seminorm.finset_sup_apply_le (mul_nonneg hB.le (Real.rpow_nonneg hlog.le _))
    intro p hp
    have hED : E p.2 ≤ D := (le_abs_self _).trans
      (Finset.single_le_sum (s := s) (a := p) (fun z _ => abs_nonneg (E z.2)) hp)
    have hAB : R ^ p.1 * A p.2 ≤ B := by
      have hh := Finset.single_le_sum (s := s) (a := p)
        (fun z _ => mul_nonneg (pow_nonneg hR z.1) (hA z.2)) hp
      dsimp only [B]
      linarith
    have hb := incidenceCompactSupport_seminorm_bound f R
      (A p.2 * (Real.log x) ^ E p.2) hR
      (mul_nonneg (hA _) (Real.rpow_nonneg hlog.le _)) hf p.1 p.2 (hder p.2)
    change SchwartzMap.seminorm ℂ p.1 p.2 f ≤ _
    calc
      _ ≤ R ^ p.1 * (A p.2 * (Real.log x) ^ E p.2) := hb
      _ = (R ^ p.1 * A p.2) * (Real.log x) ^ E p.2 := by ring
      _ ≤ B * (Real.log x) ^ D := mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hx hED)
        (Real.rpow_nonneg hlog.le _) hB.le
  exact (hT f).trans ((mul_le_mul_of_nonneg_left hsemi hC₀.le).trans_eq (by ring))

theorem incidenceSchwartzFourierL1_subpower
    (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(V, ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (A E : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ f : 𝓢(ℝ, ℂ),
      tsupport f ⊆ Set.Icc (-R) R →
      (∀ n y, ‖iteratedDeriv n f y‖ ≤ A n * (Real.log x) ^ E n) →
      (∫ ξ : V, ‖(𝓕 (T f) : 𝓢(V, ℂ)) ξ‖) ≤ x ^ η := by
  obtain ⟨C, D, hC, _, hbound⟩ := incidenceSchwartzFourierL1_log_bound T R hR A E hA
  filter_upwards [((isLittleO_log_rpow_rpow_atTop D hη).const_mul_left C).eventuallyLE,
    Filter.eventually_ge_atTop (Real.exp 1)] with x hx hxe
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hxe
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
  intro f hf hder
  apply (hbound x f hlog hf hder).trans
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le η)] using hx)

#print axioms incidenceSchwartzFourierL1_seminorm_bound
#print axioms incidenceCompactSupport_seminorm_bound
#print axioms incidenceSchwartzFourierL1_log_bound
#print axioms incidenceSchwartzFourierL1_subpower

end PrimeGap182Audit
