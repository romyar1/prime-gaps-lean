import MixedAuxiliary182

/-!
Exact linearity and polarization of actual finite Selberg arrays. These
lemmas apply before limits; supports of sums may shrink through cancellation.
-/

noncomputable section
open scoped BigOperators
open PrimeGap182.Selberg

namespace PrimeGap182Analytic

def diagonalHarmonic {α : Type*} (den : α → ℝ) (u : α →₀ ℝ) : ℝ :=
  u.sum (fun r ur => ur ^ 2 / den r)

def mixedHarmonic {α : Type*} (den : α → ℝ) (u v : α →₀ ℝ) : ℝ :=
  u.sum (fun r ur => ur * v r / den r)

theorem diagonalHarmonic_nonneg {α : Type*} (den : α → ℝ) (hden : ∀ r, 0 ≤ den r)
    (u : α →₀ ℝ) : 0 ≤ diagonalHarmonic den u := by
  classical
  exact Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (hden r)

theorem diagonalHarmonic_polarization {α : Type*} (den : α → ℝ) (u v : α →₀ ℝ) :
    diagonalHarmonic den (u + v) - diagonalHarmonic den (u - v) =
      4 * mixedHarmonic den u v := by
  classical
  let K := u.support ∪ v.support
  have hQ (w : α →₀ ℝ) (hw : w.support ⊆ K) :
      diagonalHarmonic den w = ∑ r ∈ K, w r ^ 2 / den r :=
    w.sum_of_support_subset hw _ (by intro r _; simp)
  have hC : mixedHarmonic den u v = ∑ r ∈ K, u r * v r / den r :=
    u.sum_of_support_subset Finset.subset_union_left _ (by intro r _; simp)
  rw [hQ (u + v) Finsupp.support_add, hQ (u - v) Finsupp.support_sub, hC,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finsupp.add_apply, Finsupp.sub_apply]
  ring

theorem diagonalHarmonic_parallelogram {α : Type*} (den : α → ℝ) (u v : α →₀ ℝ) :
    diagonalHarmonic den (u + v) + diagonalHarmonic den (u - v) =
      2 * diagonalHarmonic den u + 2 * diagonalHarmonic den v := by
  classical
  let K := u.support ∪ v.support
  have hQ (w : α →₀ ℝ) (hw : w.support ⊆ K) :
      diagonalHarmonic den w = ∑ r ∈ K, w r ^ 2 / den r :=
    w.sum_of_support_subset hw _ (by intro r _; simp)
  rw [hQ (u + v) Finsupp.support_add, hQ (u - v) Finsupp.support_sub,
    hQ u Finset.subset_union_left, hQ v Finset.subset_union_right,
    ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finsupp.add_apply, Finsupp.sub_apply]
  ring

/-- Bounded diagonal energies already bound the mixed auxiliary energy.
An explicit limit for nested sharp cutoffs is unnecessary for orthogonality. -/
theorem mixedHarmonic_abs_le {α : Type*} (den : α → ℝ) (hden : ∀ r, 0 ≤ den r)
    (u v : α →₀ ℝ) :
    |mixedHarmonic den u v| ≤
      (diagonalHarmonic den u + diagonalHarmonic den v) / 2 := by
  have hp := diagonalHarmonic_polarization den u v
  have hq := diagonalHarmonic_parallelogram den u v
  have hplus := diagonalHarmonic_nonneg den hden (u + v)
  have hminus := diagonalHarmonic_nonneg den hden (u - v)
  apply abs_le.mpr
  constructor <;> linarith

def sampledSelbergRoot {ι : Type*} [Fintype ι]
    (y : (ι → ℕ) →₀ ℝ) (v : ι → ℕ) : ℝ := by
  classical
  exact ∑ d ∈ y.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors)),
    if ∀ j, d j ∣ v j then PrimeGap182.Selberg.selbergCoefficient y d else 0

theorem sampledSelbergRoot_add {ι : Type*} [Fintype ι]
    (u z : (ι → ℕ) →₀ ℝ) (v : ι → ℕ) :
    sampledSelbergRoot (u + z) v = sampledSelbergRoot u v + sampledSelbergRoot z v := by
  classical
  have hc := selberg_divisor_root_finset_combination (Finset.univ : Finset (Fin 2))
    (fun _ => (1 : ℝ)) ![u, z] v
  simpa only [Fin.sum_univ_two, one_mul, one_smul, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sampledSelbergRoot] using hc

theorem sampledSelbergRoot_sub {ι : Type*} [Fintype ι]
    (u z : (ι → ℕ) →₀ ℝ) (v : ι → ℕ) :
    sampledSelbergRoot (u - z) v = sampledSelbergRoot u v - sampledSelbergRoot z v := by
  classical
  have hc := selberg_divisor_root_finset_combination (Finset.univ : Finset (Fin 2))
    ![(1 : ℝ), -1] ![u, z] v
  simpa only [Fin.sum_univ_two, one_mul, one_smul, neg_one_smul, neg_mul,
    sub_eq_add_neg, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sampledSelbergRoot] using hc

open Classical in
theorem sampledSelbergRoot_fin {k : ℕ}
    (u : (Fin k → ℕ) →₀ ℝ) (v : Fin k → ℕ) :
    sampledSelbergRoot u v =
      ∑ d ∈ u.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors)),
        if ∀ j, d j ∣ v j then PrimeGap182.Selberg.selbergCoefficient u d else 0 := by
  dsimp only [sampledSelbergRoot]
  refine Finset.sum_congr ?_ ?_
  · ext d
    simp only [Finset.mem_biUnion, Fintype.mem_piFinset]
  · intro d _
    by_cases hd : ∀ j, d j ∣ v j <;> simp only [hd, ite_false]

open Classical in
theorem sampledSelbergRoot_one
    (u : (Fin 1 → ℕ) →₀ ℝ) (t : ℕ) :
    sampledSelbergRoot u (fun _ => t) =
      ∑ d ∈ u.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors)),
        if d 0 ∣ t then PrimeGap182.Selberg.selbergCoefficient u d else 0 := by
  rw [sampledSelbergRoot_fin]
  simp only [Fin.forall_fin_one]

def selbergL1 {ι : Type*} [Fintype ι] (u : (ι → ℕ) →₀ ℝ) : ℝ := by
  classical
  exact ∑ d ∈ u.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors)),
    |PrimeGap182.Selberg.selbergCoefficient u d|

theorem selbergL1_nonneg {ι : Type*} [Fintype ι] (u : (ι → ℕ) →₀ ℝ) :
    0 ≤ selbergL1 u := by
  classical
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

def auxiliaryPeriodSquare (q : ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ) : ℝ :=
  (1 / (q : ℝ)) * ∑ n ∈ Finset.range q,
    (sampledSelbergRoot u (fun _ => n + h i) *
      sampledSelbergRoot z (fun j => n + h (i.succAbove j))) ^ 2

def auxiliaryPeriodCross (q : ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (u₁ u₂ : (Fin 1 → ℕ) →₀ ℝ) (z₁ z₂ : (Fin 38 → ℕ) →₀ ℝ) : ℝ :=
  (1 / (q : ℝ)) * ∑ n ∈ Finset.range q,
    sampledSelbergRoot u₁ (fun _ => n + h i) *
      sampledSelbergRoot u₂ (fun _ => n + h i) *
      sampledSelbergRoot z₁ (fun j => n + h (i.succAbove j)) *
      sampledSelbergRoot z₂ (fun j => n + h (i.succAbove j))

theorem auxiliaryPeriod_polarization (q : ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (u₁ u₂ : (Fin 1 → ℕ) →₀ ℝ) (z₁ z₂ : (Fin 38 → ℕ) →₀ ℝ) :
    16 * auxiliaryPeriodCross q h i u₁ u₂ z₁ z₂ =
      auxiliaryPeriodSquare q h i (u₁ + u₂) (z₁ + z₂) -
      auxiliaryPeriodSquare q h i (u₁ - u₂) (z₁ + z₂) -
      auxiliaryPeriodSquare q h i (u₁ + u₂) (z₁ - z₂) +
      auxiliaryPeriodSquare q h i (u₁ - u₂) (z₁ - z₂) := by
  have hc := mixed_auxiliary_polarization (Finset.range q) (fun _ => 1)
    (fun n => sampledSelbergRoot u₁ (fun _ => n + h i))
    (fun n => sampledSelbergRoot u₂ (fun _ => n + h i))
    (fun n => sampledSelbergRoot z₁ (fun j => n + h (i.succAbove j)))
    (fun n => sampledSelbergRoot z₂ (fun j => n + h (i.succAbove j))) (1 / (q : ℝ))
  simp only [normalizedProductCross, normalizedProductSquare, one_mul,
    Pi.add_apply, Pi.sub_apply] at hc
  simp only [auxiliaryPeriodCross, auxiliaryPeriodSquare,
    sampledSelbergRoot_add, sampledSelbergRoot_sub]
  linarith only [hc]

theorem mixed_harmonic_product_polarization {α β : Type*}
    (denU : α → ℝ) (denZ : β → ℝ) (u₁ u₂ : α →₀ ℝ) (z₁ z₂ : β →₀ ℝ) :
    16 * (mixedHarmonic denU u₁ u₂ * mixedHarmonic denZ z₁ z₂) =
      diagonalHarmonic denU (u₁ + u₂) * diagonalHarmonic denZ (z₁ + z₂) -
      diagonalHarmonic denU (u₁ - u₂) * diagonalHarmonic denZ (z₁ + z₂) -
      diagonalHarmonic denU (u₁ + u₂) * diagonalHarmonic denZ (z₁ - z₂) +
      diagonalHarmonic denU (u₁ - u₂) * diagonalHarmonic denZ (z₁ - z₂) := by
  have hU := diagonalHarmonic_polarization denU u₁ u₂
  have hZ := diagonalHarmonic_polarization denZ z₁ z₂
  nlinarith only [congrArg (fun t : ℝ => t *
    (diagonalHarmonic denZ (z₁ + z₂) - diagonalHarmonic denZ (z₁ - z₂))) hU,
    congrArg (fun t : ℝ => 4 * mixedHarmonic denU u₁ u₂ * t) hZ]

#print axioms sampledSelbergRoot_add
#print axioms sampledSelbergRoot_sub
#print axioms auxiliaryPeriod_polarization
#print axioms mixedHarmonic_abs_le
#print axioms mixed_harmonic_product_polarization

end PrimeGap182Analytic
