import TypeIIIExactPullback

/-!
# Explicit convolution spectrum before the Type III torus substitution

The spectrum here is computed from ordinary rank-two Kloosterman sums.
These are exact identities, without a character-sum bound or a geometric
realization hypothesis.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- The normalized convolution appropriate to the positive two-variable
transform and its unnormalized counting measure. -/
def exactSpectrumConvolution (F G : ZMod p → ZMod p → ℂ) (h k : ZMod p) : ℂ :=
  ((p : ℂ) ^ 2)⁻¹ * ∑ a : ZMod p, ∑ b : ZMod p, F a b * G (h - a) (k - b)

/-- Transforming a pointwise product gives the exact normalized convolution. -/
theorem exact_fourier₂_product (f g : ZMod p → ZMod p → ℂ) (h k : ZMod p) :
    fourier₂ p (fun x y => f x y * g x y) h k =
      exactSpectrumConvolution p (fourier₂ p f) (fourier₂ p g) h k := by
  classical
  unfold exactSpectrumConvolution
  conv_lhs =>
    unfold fourier₂
    arg 2
    ext x
    arg 2
    ext y
    dsimp only
    rw [← exact_fourier₂_inversion p f]
  have hg (a b : ZMod p) : fourier₂ p g a b =
      ∑ x : ZMod p, ∑ y : ZMod p, g x y * ZMod.stdAddChar (a * x + b * y) := rfl
  simp_rw [hg]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have he : ZMod.stdAddChar (-(a * x + b * y)) *
      ZMod.stdAddChar (h * x + k * y) =
      ZMod.stdAddChar ((h - a) * x + (k - b) * y) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    _ = ((p : ℂ) ^ 2)⁻¹ * fourier₂ p f a b * g x y *
        (ZMod.stdAddChar (-(a * x + b * y)) *
          ZMod.stdAddChar (h * x + k * y)) := by ring
    _ = _ := by rw [he]; ring

theorem exact_fourier₂_product_function (f g : ZMod p → ZMod p → ℂ) :
    fourier₂ p (fun x y => f x y * g x y) =
      exactSpectrumConvolution p (fourier₂ p f) (fourier₂ p g) := by
  funext h k
  exact exact_fourier₂_product p f g h k

/-- Conjugation reflects the frequencies. -/
theorem exact_fourier₂_star (f : ZMod p → ZMod p → ℂ) (h k : ZMod p) :
    fourier₂ p (fun x y => star (f x y)) h k = star (fourier₂ p f (-h) (-k)) := by
  simp only [fourier₂, star_sum, star_mul, PrimeGap186.star_stdAddChar]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [neg_mul, neg_add, neg_neg]
  exact mul_comm _ _

/-- Separate nonzero dilations in the two physical variables rescale the
frequencies by the reciprocal factors. -/
theorem exact_fourier₂_scale (f : ZMod p → ZMod p → ℂ) (c d h k : ZMod p)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    fourier₂ p (fun x y => f (c * x) (d * y)) h k =
      fourier₂ p f (h / c) (k / d) := by
  classical
  unfold fourier₂
  refine Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ ?_
  intro x
  refine Fintype.sum_equiv (Equiv.mulLeft₀ d hd) _ _ ?_
  intro y
  change f (c * x) (d * y) * ZMod.stdAddChar (h * x + k * y) =
    f (c * x) (d * y) * ZMod.stdAddChar ((h / c) * (c * x) + (k / d) * (d * y))
  congr 1
  congr 1
  field_simp

/-- The previously computed exact correlation spectrum as an explicit
function, including both zero-frequency axes. -/
def exactCorrelationSpectrum (a b : ZMod p) : ℂ :=
  if a = 0 ∨ b = 0 then 0 else
    (p : ℂ) * ZMod.stdAddChar ((1 : ZMod p) / a - 1 / b) *
      PrimeGap186.unnormalizedKloosterman2 p (-1 / (a * b)) - p - 1

/-- Exact spectrum of a scaled correlation. -/
def exactScaledCorrelationSpectrum (α m n a b : ZMod p) : ℂ :=
  exactCorrelationSpectrum p (a / (α / m)) (b / (α / n))

theorem exact_scaled_correlation_fourier (α m n : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    fourier₂ p (fun u v => correlation p (α * u / m) (α * v / n) 1) =
      exactScaledCorrelationSpectrum p α m n := by
  funext a b
  have he : (fun u v => correlation p (α * u / m) (α * v / n) 1) =
      (fun u v => correlation p ((α / m) * u) ((α / n) * v) 1) := by
    funext u v
    congr 1 <;> ring
  rw [he, exact_fourier₂_scale p (fun A B => correlation p A B 1)
      _ _ _ _ (div_ne_zero hα hm) (div_ne_zero hα hn),
    correlation_two_variable_fourier]
  rfl

/-- The spectral involution corresponding to complex conjugation. -/
def exactSpectrumStar (F : ZMod p → ZMod p → ℂ) (a b : ZMod p) : ℂ :=
  star (F (-a) (-b))

/-- This explicit rectangle spectrum uses only normalized finite convolution,
rank-two Kloosterman sums, and complex conjugation. -/
def exactRectangleSpectrum (α m m' n n' : ZMod p) : ZMod p → ZMod p → ℂ :=
  exactSpectrumConvolution p
    (exactSpectrumConvolution p
      (exactSpectrumConvolution p
        (exactScaledCorrelationSpectrum p α m n)
        (exactSpectrumStar p (exactScaledCorrelationSpectrum p α m' n)))
      (exactScaledCorrelationSpectrum p α m' n'))
    (exactSpectrumStar p (exactScaledCorrelationSpectrum p α m n'))

/-- The explicit convolution formula equals the actual rectangle spectrum. -/
theorem exact_rectangle_spectrum (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourier₂ p (exactCorrelationRectangle p α m m' n n') =
      exactRectangleSpectrum p α m m' n n' := by
  funext a b
  unfold exactCorrelationRectangle
  rw [exact_fourier₂_product_function, exact_fourier₂_product_function,
    exact_fourier₂_product_function]
  have hs (c d : ZMod p) :
      fourier₂ p (fun u v => star (correlation p (α * u / c) (α * v / d) 1)) =
      exactSpectrumStar p (fourier₂ p (fun u v => correlation p (α * u / c) (α * v / d) 1)) := by
    funext x y
    exact exact_fourier₂_star p _ x y
  rw [hs, hs, exact_scaled_correlation_fourier p α m n hα hm hn,
    exact_scaled_correlation_fourier p α m' n hα hm' hn,
    exact_scaled_correlation_fourier p α m' n' hα hm' hn',
    exact_scaled_correlation_fourier p α m n' hα hm hn']
  rfl

/-- A completely explicit finite-sum evaluation of the actual target
transform.  The remaining task is cancellation in this finite sum. -/
theorem exact_fourCycle_fourier_explicit (α m m' n n' h k : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourier₂ p (fourCycle p α m m' n n') h k =
      ((p : ℂ) ^ 2)⁻¹ * ∑ a : ZMod p, ∑ b : ZMod p,
        exactRectangleSpectrum p α m m' n n' a b *
          toricPhaseFourier p (-a) (-b) h k := by
  rw [exact_fourCycle_fourier, exact_rectangle_spectrum p α m m' n n' hα hm hm' hn hn']

#print axioms exact_fourier₂_product
#print axioms exact_fourier₂_star
#print axioms exact_fourier₂_scale
#print axioms exact_scaled_correlation_fourier
#print axioms exact_rectangle_spectrum
#print axioms exact_fourCycle_fourier_explicit

end PrimeGap182.TypeIII
