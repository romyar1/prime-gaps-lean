import IncidenceSmoothSourceWindow

/-!
# The actual normalized source profile

After the integer substitutions n=c(ζe+q₀(γλ+ek)), the smooth numerator
weight is the fixed polynomial pullback ψ(z₀(z₁z₂+z₃)) of four normalized
coordinates. A genuine compact Schwartz extension is constructed here.
The normalization identity is proved with all denominators explicit.
-/

noncomputable section

namespace PrimeGap182Audit

open WithLp
open scoped SchwartzMap ContDiff

abbrev IncidenceSourceCoordinates := EuclideanSpace ℝ (Fin 4)

def incidenceSourceCoordinatePolynomial (z : IncidenceSourceCoordinates) : ℝ :=
  z 0 * (z 1 * z 2 + z 3)

theorem incidenceSourceCoordinatePolynomial_smooth :
    ContDiff ℝ ∞ incidenceSourceCoordinatePolynomial := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 0).contDiff.mul
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 1).contDiff.mul
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 2).contDiff).add
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 3).contDiff)

theorem incidenceSourceProfile_exists (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ F : 𝓢(IncidenceSourceCoordinates, ℂ),
      ∀ z, ‖z‖ ≤ B → F z = (ψ (incidenceSourceCoordinatePolynomial z) : ℂ) := by
  let b : ContDiffBump (0 : IncidenceSourceCoordinates) :=
    ⟨B + 1, B + 2, by positivity, by linarith⟩
  let f : IncidenceSourceCoordinates → ℂ := fun z =>
    (b z : ℂ) * (ψ (incidenceSourceCoordinatePolynomial z) : ℂ)
  have hc : HasCompactSupport f :=
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hs : ContDiff ℝ ∞ f :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul
      (Complex.ofRealCLM.contDiff.comp (hψ.comp incidenceSourceCoordinatePolynomial_smooth))
  refine ⟨hc.toSchwartzMap hs, ?_⟩
  intro z hz
  change (b z : ℂ) * (ψ (incidenceSourceCoordinatePolynomial z) : ℂ) = _
  have hb : b z = 1 := b.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hz.trans (by dsimp only [b]; linarith))
  rw [hb, Complex.ofReal_one, one_mul]

def incidenceSourceRowCoordinates (esc Λ V τ e γ : ℝ) : IncidenceSourceCoordinates :=
  toLp 2 ![e / esc, (γ / e - τ) * Λ / V, 0, 0]

def incidenceSourceInputCoordinates (Λ V τ ζ q ell k : ℝ) : IncidenceSourceCoordinates :=
  toLp 2 ![0, 0, ell / Λ, (k + τ * ell + ζ / q) / V]

set_option maxHeartbeats 400000 in
/-- The smooth joint weight is the same fixed polynomial profile after
normalization; it is not an assumed row/input decomposition. -/
theorem incidenceSourceCoordinatePolynomial_identity
    (N c q esc Λ τ ζ e γ ell k : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hq : q ≠ 0) (hesc : esc ≠ 0)
    (hΛ : Λ ≠ 0) (he : e ≠ 0) :
    incidenceSourceCoordinatePolynomial
      (incidenceSourceRowCoordinates esc Λ (N / (c * q * esc)) τ e γ +
        incidenceSourceInputCoordinates Λ (N / (c * q * esc)) τ ζ q ell k) =
      c * (ζ * e + q * (γ * ell + e * k)) / N := by
  simp only [incidenceSourceCoordinatePolynomial, incidenceSourceRowCoordinates,
    incidenceSourceInputCoordinates, PiLp.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    add_zero, zero_add]
  field_simp
  ring

#print axioms incidenceSourceCoordinatePolynomial_smooth
#print axioms incidenceSourceProfile_exists
#print axioms incidenceSourceCoordinatePolynomial_identity

end PrimeGap182Audit
