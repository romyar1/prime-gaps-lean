import SelbergPolarization182

/-!
Vanishing mixed harmonic moments for orthogonal radial profiles. The
auxiliary arrays may have different cutoffs; only their individual bounded
diagonal energies are needed.
-/

noncomputable section
open scoped Topology
open Filter

namespace PrimeGap182Analytic

theorem tendsto_zero_of_eventually_abs_le_every
    {β : Type*} (f : Filter β) (g : β → ℝ)
    (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in f, |g x| ≤ ε) :
    Tendsto g f (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hg (ε / 2) (half_pos hε)] with x hx
  simpa only [dist_zero_right, Real.norm_eq_abs] using hx.trans_lt (half_lt_self hε)

theorem bounded_mul_tendsto_zero
    {β : Type*} (f : Filter β) (a b : β → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ᶠ x in f, |a x| ≤ K) (hb : Tendsto b f (nhds 0)) :
    Tendsto (fun x => a x * b x) f (nhds 0) := by
  have hK1 : 0 < K + 1 := by linarith
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ x in f, |b x| < ε / (K + 1) :=
    (hb.abs).eventually_lt_const (by simpa only [abs_zero] using div_pos hε hK1)
  filter_upwards [ha, hsmall] with x hax hbx
  have hab : |a x * b x| < ε := by
    rw [abs_mul]
    calc
      _ ≤ (K + 1) * |b x| := mul_le_mul_of_nonneg_right (hax.trans (by linarith)) (abs_nonneg _)
      _ < ε := by
        have ht := (lt_div_iff₀ hK1).mp hbx
        simpa only [mul_comm] using ht
  simpa only [dist_zero_right, Real.norm_eq_abs] using hab

theorem mixed_harmonic_scaled_tendsto_zero
    {α γ β : Type*} (f : Filter β) (denU : α → ℝ) (denZ : γ → ℝ)
    (hdenU : ∀ r, 0 ≤ denU r)
    (u₁ u₂ : β → α →₀ ℝ) (z₁ z₂ : β → γ →₀ ℝ)
    (A B : β → ℝ) (hA : ∀ᶠ x in f, 0 ≤ A x) (E₁ E₂ : ℝ)
    (hU₁ : Tendsto (fun x => A x * diagonalHarmonic denU (u₁ x)) f (nhds E₁))
    (hU₂ : Tendsto (fun x => A x * diagonalHarmonic denU (u₂ x)) f (nhds E₂))
    (hZ : Tendsto (fun x => B x * mixedHarmonic denZ (z₁ x) (z₂ x)) f (nhds 0)) :
    Tendsto (fun x => (A x * B x) *
      (mixedHarmonic denU (u₁ x) (u₂ x) * mixedHarmonic denZ (z₁ x) (z₂ x)))
      f (nhds 0) := by
  let K : ℝ := (|E₁| + |E₂| + 2) / 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have h₁ := hU₁.eventually_le_const (show E₁ < |E₁| + 1 from
    (le_abs_self E₁).trans_lt (lt_add_one _))
  have h₂ := hU₂.eventually_le_const (show E₂ < |E₂| + 1 from
    (le_abs_self E₂).trans_lt (lt_add_one _))
  have hbound : ∀ᶠ x in f, |A x * mixedHarmonic denU (u₁ x) (u₂ x)| ≤ K := by
    filter_upwards [hA, h₁, h₂] with x hAx h1 h2
    rw [abs_mul, abs_of_nonneg hAx]
    calc
      _ ≤ A x * ((diagonalHarmonic denU (u₁ x) + diagonalHarmonic denU (u₂ x)) / 2) :=
        mul_le_mul_of_nonneg_left (mixedHarmonic_abs_le denU hdenU (u₁ x) (u₂ x)) hAx
      _ ≤ K := by dsimp only [K]; linarith
  have ht := bounded_mul_tendsto_zero f
    (fun x => A x * mixedHarmonic denU (u₁ x) (u₂ x))
    (fun x => B x * mixedHarmonic denZ (z₁ x) (z₂ x)) K hK hbound hZ
  convert ht using 1
  funext x
  ring

#print axioms mixed_harmonic_scaled_tendsto_zero

end PrimeGap182Analytic
