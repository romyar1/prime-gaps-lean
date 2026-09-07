import TypeIIISquarefreeMaskMass
import TypeIIIFiniteFourierCRT
import TypeIIIExceptionalData

/-!
# The finite-exceptional local input implies squarefree incomplete-cycle completion

This combines the exact CRT Fourier identity, polynomial fiber counting, invertible
frequency rescaling, positive exceptional-mask expansion, and interval coset estimates.
The additional finite-field input is an explicit argument.  No global Type III theorem is
postulated.  All constants in the finite-modulus conclusion are displayed.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Completion for an actual CRT product whose local transforms have the proved mask form. -/
theorem crtProduct_interval_bound_of_localMasks
    (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (C : ℝ) (hC : 0 ≤ C) (D : ℕ)
    (F : ∀ i, ZMod (q i) → ZMod (q i) → ℂ) (E : ∀ i, LocalMaskData (q i) D)
    (hF : ∀ i h k,
      ‖fourier₂ (q i) (F i) ((crtFrequencyUnit q hcp i : ZMod (q i)) * h)
        ((crtFrequencyUnit q hcp i : ZMod (q i)) * k)‖ ≤
          C * (q i : ℝ) ^ 3 * localExceptionalEnvelope (E i) h k)
    (Ah Ak : ℤ) (Nh Nk : ℕ) :
    ‖intervalRectangleSum (∏ i, q i) Ah Ak Nh Nk (crtProduct q F)‖ ≤
      C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) *
        squarefreeCompletionShape (∏ i, q i) (repeatedFactor q E) Nh Nk := by
  let s := ∏ i, q i
  let V (h k : ZMod s) :=
    ∏ i, localExceptionalEnvelope (E i) (h.val : ZMod (q i)) (k.val : ZMod (q i))
  have hhat (h k : ZMod s) :
      ‖fourier₂ s (crtProduct q F) h k‖ ≤ C ^ Fintype.card ι * (s : ℝ) ^ 3 * V h k := by
    rw [norm_fourier₂_crtProduct q hcp]
    calc
      _ ≤ ∏ i, C * (q i : ℝ) ^ 3 *
          localExceptionalEnvelope (E i) (h.val : ZMod (q i)) (k.val : ZMod (q i)) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro i hi
        exact hF i _ _
      _ = _ := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Finset.prod_pow, ← Nat.cast_prod]
        rfl
  have hmass := squarefree_exceptional_mask_mass q hcp D E Ah Ak Nh Nk
  calc
    _ ≤ ((s : ℝ)⁻¹) ^ 2 * (∑ h : ZMod s, ∑ k : ZMod s,
        (C ^ Fintype.card ι * (s : ℝ) ^ 3 * V h k) *
          ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) :=
      intervalRectangleSum_norm_le_majorant s Ah Ak Nh Nk (crtProduct q F) _ hhat
    _ = C ^ Fintype.card ι * ((s : ℝ) * (∑ h : ZMod s, ∑ k : ZMod s,
        V h k * ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖)) := by
      have hsum : (∑ h : ZMod s, ∑ k : ZMod s,
          (C ^ Fintype.card ι * (s : ℝ) ^ 3 * V h k) *
            ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) =
          (C ^ Fintype.card ι * (s : ℝ) ^ 3) *
            (∑ h : ZMod s, ∑ k : ZMod s,
              V h k * ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hsum]
      have hs : (s : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne s)
      field_simp
    _ ≤ C ^ Fintype.card ι *
        (maskComplexity D (Fintype.card ι) *
          squarefreeCompletionShape (∏ i, q i) (repeatedFactor q E) Nh Nk) :=
      mul_le_mul_of_nonneg_left hmass (pow_nonneg hC _)
    _ = _ := by ring

variable (q : ι → ℕ) [∀ i, Fact (q i).Prime] [NeZero (∏ i, q i)]

/-- The actual product of the prime Kloosterman matrix kernels. -/
def squarefreeKernel (α m n : ∀ i, ZMod (q i)) (x y : ZMod (∏ i, q i)) : ℂ :=
  ∏ i, kernel (q i) (α i) (m i) (n i) (x.val : ZMod (q i)) (y.val : ZMod (q i))

def squarefreeFourCycle (α m m' n n' : ∀ i, ZMod (q i))
    (x y : ZMod (∏ i, q i)) : ℂ :=
  squarefreeKernel q α m n x y * star (squarefreeKernel q α m' n x y) *
    squarefreeKernel q α m' n' x y * star (squarefreeKernel q α m n' x y)

omit [DecidableEq ι] in
theorem squarefreeFourCycle_eq_crtProduct (α m m' n n' : ∀ i, ZMod (q i)) :
    squarefreeFourCycle q α m m' n n' =
      crtProduct q (fun i => fourCycle (q i) (α i) (m i) (m' i) (n i) (n' i)) := by
  funext x y
  simp only [squarefreeFourCycle, squarefreeKernel, crtProduct, fourCycle,
    star_prod, Finset.prod_mul_distrib]

/-- The repeated-index factor is specified directly by the local row and column residues. -/
def repeatedResidueFactor (m m' n n' : ∀ i, ZMod (q i)) : ℕ :=
  ∏ i, if m i = m' i ∨ n i = n' i then q i else 1

/-- Exact finite-modulus completion from the two cases of the new local proposition. -/
theorem squarefree_fourCycle_interval_bound
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (C : ℝ) (hC : 0 ≤ C) (D : ℕ)
    (α m m' n n' : ∀ i, ZMod (q i))
    (hinput : ∀ i,
      ((m i ≠ m' i ∧ n i ≠ n' i) →
        FiniteExceptionalFourierBound (q i) C D (α i) (m i) (m' i) (n i) (n' i)) ∧
      ((m i = m' i ∨ n i = n' i) →
        CurveExceptionalFourierBound (q i) C D (α i) (m i) (m' i) (n i) (n' i)))
    (Ah Ak : ℤ) (Nh Nk : ℕ) :
    ‖intervalRectangleSum (∏ i, q i) Ah Ak Nh Nk (squarefreeFourCycle q α m m' n n')‖ ≤
      C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) *
        squarefreeCompletionShape (∏ i, q i) (repeatedResidueFactor q m m' n n') Nh Nk := by
  choose E hE hF using fun i => localMaskData_of_localFourier (q i)
    (α i) (m i) (m' i) (n i) (n' i) (crtFrequencyUnit q hcp i) (hinput i)
  have hrep : repeatedFactor q E = repeatedResidueFactor q m m' n n' := by
    unfold repeatedFactor repeatedResidueFactor
    apply Finset.prod_congr rfl
    intro i hi
    rw [hE i]
    by_cases hh : m i = m' i ∨ n i = n' i <;> simp [hh]
  rw [squarefreeFourCycle_eq_crtProduct]
  simpa only [hrep] using crtProduct_interval_bound_of_localMasks q hcp C hC D
    (fun i => fourCycle (q i) (α i) (m i) (m' i) (n i) (n' i)) E hF Ah Ak Nh Nk

/-- The uniform local hypothesis supplies the concrete finite-modulus completion theorem
for factors above its fixed small-prime cutoff. -/
theorem LocalFourierHypothesis.squarefree_interval_bound
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (hlarge : ∀ i, p₀ < q i)
    (α m m' n n' : ∀ i, ZMod (q i))
    (hα : ∀ i, α i ≠ 0) (hm : ∀ i, m i ≠ 0) (hm' : ∀ i, m' i ≠ 0)
    (hn : ∀ i, n i ≠ 0) (hn' : ∀ i, n' i ≠ 0)
    (Ah Ak : ℤ) (Nh Nk : ℕ) :
    ‖intervalRectangleSum (∏ i, q i) Ah Ak Nh Nk (squarefreeFourCycle q α m m' n n')‖ ≤
      C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) *
        squarefreeCompletionShape (∏ i, q i) (repeatedResidueFactor q m m' n n') Nh Nk := by
  apply squarefree_fourCycle_interval_bound q hcp C hC D α m m' n n'
  intro i
  exact hlocal (q i) (hlarge i) (α i) (m i) (m' i) (n i) (n' i)
    (hα i) (hm i) (hm' i) (hn i) (hn' i)

#print axioms crtProduct_interval_bound_of_localMasks
#print axioms squarefreeFourCycle_eq_crtProduct
#print axioms squarefree_fourCycle_interval_bound
#print axioms LocalFourierHypothesis.squarefree_interval_bound

end

end PrimeGap182.TypeIII
