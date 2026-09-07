import IncidenceAngularWindow

/-!
# Uniform normalized source profiles

For the actual real compact profiles in the source theorem, a single
compact pullback map gives exact equality on every permitted normalized
row/input coordinate and a uniform subpower Fourier separation cost.
-/

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform ContDiff

theorem incidenceRealProfile_schwartz (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (R : ℝ) (hs : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ y, f y = (ψ y : ℂ)) ∧ tsupport f ⊆ Set.Icc (-R) R ∧
      ∀ n y, ‖iteratedDeriv n f y‖ = |iteratedDeriv n ψ y| := by
  have hψc : HasCompactSupport ψ := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  have hc : HasCompactSupport (fun y => (ψ y : ℂ)) :=
    hψc.comp_left Complex.ofReal_zero
  let f : 𝓢(ℝ, ℂ) := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hψ)
  refine ⟨f, fun _ => rfl, ?_, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro y hy
    apply hs
    change (ψ y : ℂ) ≠ 0 at hy
    exact fun h => hy (by rw [h, Complex.ofReal_zero])
  · intro n y
    change ‖iteratedDeriv n (fun t => (ψ t : ℂ)) y‖ = |iteratedDeriv n ψ y|
    have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (x := y) (i := n) hψ.contDiffAt (by simp)
    simpa only [Function.comp_def,
      Complex.ofRealLI_apply, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs] using h

theorem incidenceNormalizedProfile_map (c C R : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    ∃ T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(IncidenceSourceCoordinates, ℂ),
      ∀ f : 𝓢(ℝ, ℂ), tsupport f ⊆ Set.Icc (-R) R →
      ∀ z : IncidenceSourceCoordinates,
        c ≤ |z 0| → |z 0| ≤ C → |z 1| ≤ 1 → |z 2| ≤ 2 →
        T f z = f (incidenceSourceCoordinatePolynomial z) := by
  let B : ℝ := 2 * (C + R / c + 5)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let b : ContDiffBump (0 : IncidenceSourceCoordinates) :=
    ⟨B + 1, B + 2, by positivity, by linarith⟩
  have hb : HasCompactSupport (fun z => (b z : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let bS : 𝓢(IncidenceSourceCoordinates, ℂ) := hb.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hbS : HasCompactSupport bS := hb
  let T := incidenceCompactPullbackCLM bS hbS incidenceSourceCoordinatePolynomial
    incidenceSourceCoordinatePolynomial_smooth
  refine ⟨T, ?_⟩
  intro f hf z hz0 hz0' hz1 hz2
  change (b z : ℂ) * f (incidenceSourceCoordinatePolynomial z) = _
  by_cases hp : f (incidenceSourceCoordinatePolynomial z) = 0
  · rw [hp, mul_zero]
  · have hP : |incidenceSourceCoordinatePolynomial z| ≤ R := by
      rw [abs_le]
      exact hf (subset_tsupport f hp)
    have hzB := incidenceSourceCoordinate_norm_bound z c C R hc hC hR hz0 hz0' hz1 hz2 hP
    have hb1 : b z = 1 := b.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact hzB.trans (by change B ≤ B + 1; linarith))
    rw [hb1, Complex.ofReal_one, one_mul]

theorem incidenceNormalizedProfile_uniform_subpower (c C R : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (A E : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ n y, |iteratedDeriv n ψ y| ≤ A n * (Real.log x) ^ E n) →
      ∃ F : 𝓢(IncidenceSourceCoordinates, ℂ),
        (∀ z : IncidenceSourceCoordinates,
          c ≤ |z 0| → |z 0| ≤ C → |z 1| ≤ 1 → |z 2| ≤ 2 →
          F z = (ψ (incidenceSourceCoordinatePolynomial z) : ℂ)) ∧
        (∫ ξ : IncidenceSourceCoordinates, ‖(𝓕 F : 𝓢(IncidenceSourceCoordinates, ℂ)) ξ‖) ≤
          x ^ η := by
  obtain ⟨T, hT⟩ := incidenceNormalizedProfile_map c C R hc hC hR
  filter_upwards [incidenceSchwartzFourierL1_subpower T R hR A E hA η hη] with x hx
  intro ψ hψ hs hder
  obtain ⟨f, hf, hfs, hfn⟩ := incidenceRealProfile_schwartz ψ hψ R hs
  refine ⟨T f, ?_, hx f hfs (fun n y => (hfn n y).trans_le (hder n y))⟩
  intro z hz0 hz0' hz1 hz2
  exact (hT f hfs z hz0 hz0' hz1 hz2).trans (hf _)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceRealProfile_schwartz
#print axioms PrimeGap182Audit.incidenceNormalizedProfile_map
#print axioms PrimeGap182Audit.incidenceNormalizedProfile_uniform_subpower
