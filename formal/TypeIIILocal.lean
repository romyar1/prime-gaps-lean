import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The actual local sums in the finite-exceptional Type III estimate

The propositions at the end of this file are explicit **hypotheses**, not axioms or proved
finite-field estimates. Their definitions spell out the additional input beyond the two
Kloosterman bounds in the public 186 development. In particular, they do not assume a global
Type III distribution theorem.

The Fourier transform here is unnormalized and uses a positive additive-character phase.
Exceptional curves are represented by a nonzero polynomial over an algebraic closure, with
bounded total degree. Only its values at prime-field frequency pairs enter the estimate.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The paper's normalized two-unit rank-three Kloosterman sum. -/
def kl3 (t : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
    ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) + t / ((u : ZMod p) * (v : ZMod p)))

/-- The actual unit-indexed pair correlation, with its additive frequency. -/
def correlation (A B c : ZMod p) : ℂ :=
  ∑ h : (ZMod p)ˣ,
    kl3 p (A * (h : ZMod p)) * star (kl3 p (B * (h : ZMod p))) *
      ZMod.stdAddChar (c * (h : ZMod p))

/-- The matrix kernel, extended by zero away from the two-dimensional torus. -/
def kernel (α m n r₁ r₂ : ZMod p) : ℂ :=
  if r₁ = 0 ∨ r₂ = 0 then 0 else
    correlation p (α * r₂ / (m * r₁ ^ 2)) (α * r₁ / (n * r₂ ^ 2)) 1

/-- The four-cycle occurring in `tr ((K K*)²)`. -/
def fourCycle (α m m' n n' r₁ r₂ : ZMod p) : ℂ :=
  kernel p α m n r₁ r₂ * star (kernel p α m' n r₁ r₂) *
    kernel p α m' n' r₁ r₂ * star (kernel p α m n' r₁ r₂)

/-- Unnormalized two-dimensional additive Fourier transform on the actual residue space. -/
def fourier₂ (s : ℕ) [NeZero s] (f : ZMod s → ZMod s → ℂ) (h k : ZMod s) : ℂ :=
  ∑ r₁ : ZMod s, ∑ r₂ : ZMod s,
    f r₁ r₂ * ZMod.stdAddChar (h * r₁ + k * r₂)

@[simp] theorem kernel_zero_left (α m n r₂ : ZMod p) :
    kernel p α m n 0 r₂ = 0 := by
  simp [kernel]

@[simp] theorem kernel_zero_right (α m n r₁ : ZMod p) :
    kernel p α m n r₁ 0 = 0 := by
  simp [kernel]

@[simp] theorem fourCycle_zero_left (α m m' n n' r₂ : ZMod p) :
    fourCycle p α m m' n n' 0 r₂ = 0 := by
  simp [fourCycle]

@[simp] theorem fourCycle_zero_right (α m m' n n' r₁ : ZMod p) :
    fourCycle p α m m' n n' r₁ 0 = 0 := by
  simp [fourCycle]

/-- The old pair-correlation bound suffices for the entrywise estimate, without any new
exceptional-Fourier hypothesis. A baseline bridge must provide `hcorrelation` for `kl3`. -/
theorem kernel_norm_le_of_correlation
    (hcorrelation : ∀ A B : ZMod p, A ≠ 0 → B ≠ 0 →
      ‖correlation p A B 1‖ ≤ 9 * Real.sqrt (p : ℝ))
    (α m n r₁ r₂ : ZMod p) (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    ‖kernel p α m n r₁ r₂‖ ≤ 9 * Real.sqrt (p : ℝ) := by
  classical
  by_cases hr : r₁ = 0 ∨ r₂ = 0
  · simp only [kernel, ite_eq_left hr, norm_zero]
    positivity
  · rw [kernel, ite_eq_right hr]
    have hr₁ : r₁ ≠ 0 := fun h => hr (Or.inl h)
    have hr₂ : r₂ ≠ 0 := fun h => hr (Or.inr h)
    exact hcorrelation _ _
      (div_ne_zero (mul_ne_zero hα hr₂) (mul_ne_zero hm (pow_ne_zero _ hr₁)))
      (div_ne_zero (mul_ne_zero hα hr₁) (mul_ne_zero hn (pow_ne_zero _ hr₂)))

/-- Entrywise bounds imply the elementary fourth-power bound on the actual four-cycle. -/
theorem fourCycle_norm_le_of_kernel
    (L : ℝ) (hL : 0 ≤ L) (α m m' n n' r₁ r₂ : ZMod p)
    (h₁ : ‖kernel p α m n r₁ r₂‖ ≤ L)
    (h₂ : ‖kernel p α m' n r₁ r₂‖ ≤ L)
    (h₃ : ‖kernel p α m' n' r₁ r₂‖ ≤ L)
    (h₄ : ‖kernel p α m n' r₁ r₂‖ ≤ L) :
    ‖fourCycle p α m m' n n' r₁ r₂‖ ≤ L ^ 4 := by
  simp only [fourCycle, norm_mul, norm_star]
  calc
    _ ≤ ((L * L) * L) * L :=
      mul_le_mul
        (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) hL) h₃
          (norm_nonneg _) (mul_nonneg hL hL)) h₄ (norm_nonneg _)
        (mul_nonneg (mul_nonneg hL hL) hL)
    _ = L ^ 4 := by ring

/-- Evaluation of a geometric plane polynomial at an actual prime-field frequency pair. -/
def planeEval (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (h k : ZMod p) : AlgebraicClosure (ZMod p) :=
  MvPolynomial.eval ![algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) h,
    algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) k] P

/-- The distinct-index finite-exceptional Fourier inequality. This definition is not a proof
that the exceptional set or the bound exists. -/
def FiniteExceptionalFourierBound (C : ℝ) (D : ℕ) (α m m' n n' : ZMod p) : Prop :=
  ∃ Z : Finset (ZMod p × ZMod p), Z.card ≤ D ∧
    ∀ h k : ZMod p,
      ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
        C * (p : ℝ) ^ 3 *
          (1 + Real.sqrt (p : ℝ) * if (h, k) ∈ Z then 1 else 0)

/-- The repeated-index Fourier inequality with a genuinely algebraic exceptional curve.
The extra contribution at the origin has size `C*p^4`. -/
def CurveExceptionalFourierBound (C : ℝ) (D : ℕ) (α m m' n n' : ZMod p) : Prop :=
  ∃ P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)),
    P ≠ 0 ∧ P.totalDegree ≤ D ∧
    ∀ h k : ZMod p,
      ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
        C * (p : ℝ) ^ 3 *
          (1 + Real.sqrt (p : ℝ) * (if planeEval p P h k = 0 then 1 else 0) +
            (p : ℝ) * if h = 0 ∧ k = 0 then 1 else 0)

variable {p}

/-- Equality/repetition of row or column indices is exactly the vanishing discriminant
condition used in the paper. -/
theorem discriminant_eq_zero_iff (m m' n n' : ZMod p) :
    (m - m') * (n - n') = 0 ↔ m = m' ∨ n = n' := by
  simp only [mul_eq_zero, sub_eq_zero]

variable (p)

/-- The additional prime-local hypothesis, with fixed constants and a fixed small-prime
cutoff. It has no asymptotic distribution or averaging conclusion hidden in its fields. -/
def LocalFourierHypothesis (C : ℝ) (D p₀ : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p₀ < p →
    ∀ α m m' n n' : ZMod p,
      α ≠ 0 → m ≠ 0 → m' ≠ 0 → n ≠ 0 → n' ≠ 0 →
      ((m ≠ m' ∧ n ≠ n') → FiniteExceptionalFourierBound p C D α m m' n n') ∧
      ((m = m' ∨ n = n') → CurveExceptionalFourierBound p C D α m m' n n')

/-- The local proposition's uniform quantifier pattern. This remains an explicit hypothesis
until the finite-field geometric argument is formalized. -/
def HasFiniteExceptionalTypeIIIInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D p₀ : ℕ, LocalFourierHypothesis C D p₀

#print axioms kernel_norm_le_of_correlation
#print axioms fourCycle_norm_le_of_kernel
#print axioms discriminant_eq_zero_iff

end

end PrimeGap182.TypeIII
