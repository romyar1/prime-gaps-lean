import TypeIIISelectedEstimate

/-!
# Actual finite dyadic localization of selected modulus factors

The original complex modulus sums are partitioned first. Triangle inequalities are
then applied to complete sub-sums; no signed cycle or individual matrix entry is
replaced. The two dyadic labels include the factor 1.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

def weightedKernelL1 (D : Finset ℕ+) (L : Finset ℤ) (τ : ℤ → ℝ)
    (k : ℕ+ → ℤ → ℂ) : ℝ := ∑ ℓ ∈ L, τ ℓ * ‖∑ d ∈ D, k d ℓ‖

theorem weightedKernelL1_partition_le {ι : Type*} [DecidableEq ι]
    (D : Finset ℕ+) (L : Finset ℤ) (τ : ℤ → ℝ) (hτ : ∀ ℓ ∈ L, 0 ≤ τ ℓ)
    (k : ℕ+ → ℤ → ℂ) (label : ℕ+ → ι) :
    weightedKernelL1 D L τ k ≤
      ∑ j ∈ D.image label, weightedKernelL1 (D.filter (fun d => label d = j)) L τ k := by
  have hpartition (ℓ : ℤ) : (∑ d ∈ D, k d ℓ) =
      ∑ j ∈ D.image label, ∑ d ∈ D.filter (fun d => label d = j), k d ℓ :=
    (Finset.sum_fiberwise_of_maps_to (fun d hd => Finset.mem_image_of_mem label hd)
      (fun d => k d ℓ)).symm
  unfold weightedKernelL1
  calc
    _ ≤ ∑ ℓ ∈ L, ∑ j ∈ D.image label,
        τ ℓ * ‖∑ d ∈ D.filter (fun d => label d = j), k d ℓ‖ := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      rw [hpartition, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hτ ℓ hℓ)
    _ = _ := Finset.sum_comm

def dyadicFactorLabel (ρ σ : ℕ+ → ℕ+) (d : ℕ+) : ℕ × ℕ :=
  (Nat.log 2 (ρ d : ℕ), Nat.log 2 (σ d : ℕ))

def dyadicFactorBlock (D : Finset ℕ+) (ρ σ : ℕ+ → ℕ+) (j : ℕ × ℕ) : Finset ℕ+ :=
  D.filter (fun d => dyadicFactorLabel ρ σ d = j)

def dyadicFactorCells (D : Finset ℕ+) (ρ σ : ℕ+ → ℕ+) : Finset (ℕ × ℕ) :=
  D.image (dyadicFactorLabel ρ σ)

theorem weightedKernelL1_dyadic_le (D : Finset ℕ+) (L : Finset ℤ)
    (τ : ℤ → ℝ) (hτ : ∀ ℓ ∈ L, 0 ≤ τ ℓ) (k : ℕ+ → ℤ → ℂ) (ρ σ : ℕ+ → ℕ+) :
    weightedKernelL1 D L τ k ≤
      ∑ j ∈ dyadicFactorCells D ρ σ, weightedKernelL1 (dyadicFactorBlock D ρ σ j) L τ k :=
  weightedKernelL1_partition_le D L τ hτ k (dyadicFactorLabel ρ σ)

theorem dyadicFactorBlock_bounds (D : Finset ℕ+) (ρ σ : ℕ+ → ℕ+)
    (j : ℕ × ℕ) (d : ℕ+) (hd : d ∈ dyadicFactorBlock D ρ σ j) :
    2 ^ j.1 ≤ (ρ d : ℕ) ∧ (ρ d : ℕ) < 2 * 2 ^ j.1 ∧
      2 ^ j.2 ≤ (σ d : ℕ) ∧ (σ d : ℕ) < 2 * 2 ^ j.2 := by
  have hj := (Finset.mem_filter.mp hd).2
  have hj' : (Nat.log 2 (ρ d : ℕ), Nat.log 2 (σ d : ℕ)) = j := hj
  have h₁ : Nat.log 2 (ρ d : ℕ) = j.1 := by
    simpa only using congrArg (Prod.fst : ℕ × ℕ → ℕ) hj'
  have h₂ : Nat.log 2 (σ d : ℕ) = j.2 := by
    simpa only using congrArg (Prod.snd : ℕ × ℕ → ℕ) hj'
  have hrlo := Nat.pow_log_le_self 2 (ρ d).pos.ne'
  have hslo := Nat.pow_log_le_self 2 (σ d).pos.ne'
  have hrhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (ρ d : ℕ)
  have hshi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (σ d : ℕ)
  rw [h₁] at hrlo hrhi
  rw [h₂] at hslo hshi
  exact ⟨hrlo, by simpa only [pow_succ, Nat.mul_comm] using hrhi,
    hslo, by simpa only [pow_succ, Nat.mul_comm] using hshi⟩

/-- The actual number of two-factor cells is bounded by the product of logarithmic counts. -/
theorem dyadicFactorCells_card_le (D : Finset ℕ+) (ρ σ : ℕ+ → ℕ+) (U V : ℕ)
    (hU : ∀ d ∈ D, (ρ d : ℕ) ≤ U) (hV : ∀ d ∈ D, (σ d : ℕ) ≤ V) :
    (dyadicFactorCells D ρ σ).card ≤ (Nat.log 2 U + 1) * (Nat.log 2 V + 1) := by
  have hsub : dyadicFactorCells D ρ σ ⊆
      Finset.range (Nat.log 2 U + 1) ×ˢ Finset.range (Nat.log 2 V + 1) := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_product.mpr
    change Nat.log 2 (ρ d : ℕ) ∈ Finset.range (Nat.log 2 U + 1) ∧
      Nat.log 2 (σ d : ℕ) ∈ Finset.range (Nat.log 2 V + 1)
    exact ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_mono_right (hU d hd))), Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_mono_right (hV d hd)))⟩
  simpa only [Finset.card_product, Finset.card_range] using Finset.card_le_card hsub

/-- Nonempty selected cells retain the original product scale and extraction width. -/
theorem dyadicFactorBlock_scale_bounds (D : Finset ℕ+) (ρ σ : ℕ+ → ℕ+)
    (hfactor : ∀ d ∈ D, d = ρ d * σ d) (j : ℕ × ℕ)
    (hne : (dyadicFactorBlock D ρ σ j).Nonempty)
    (Qupper Slower Supper : ℝ)
    (hQ : ∀ d ∈ D, (d : ℝ) ≤ Qupper)
    (hSlo : ∀ d ∈ D, Slower ≤ (σ d : ℝ))
    (hShi : ∀ d ∈ D, (σ d : ℝ) ≤ Supper) :
    ((2 ^ j.1 : ℕ) : ℝ) * ((2 * 2 ^ j.2 : ℕ) : ℝ) ≤ 2 * Qupper ∧
      Slower ≤ ((2 * 2 ^ j.2 : ℕ) : ℝ) ∧
      ((2 * 2 ^ j.2 : ℕ) : ℝ) ≤ 2 * Supper := by
  obtain ⟨d, hd⟩ := hne
  have hdD := (Finset.mem_filter.mp hd).1
  obtain ⟨hrlo, _, hslo, hshi⟩ := dyadicFactorBlock_bounds D ρ σ j d hd
  have hrlo' : ((2 ^ j.1 : ℕ) : ℝ) ≤ (ρ d : ℝ) := by exact_mod_cast hrlo
  have hslo' : ((2 ^ j.2 : ℕ) : ℝ) ≤ (σ d : ℝ) := by exact_mod_cast hslo
  have hshi' : (σ d : ℝ) ≤ ((2 * 2 ^ j.2 : ℕ) : ℝ) := by exact_mod_cast hshi.le
  have hdprod : (d : ℝ) = (ρ d : ℝ) * (σ d : ℝ) := by
    exact_mod_cast congrArg PNat.val (hfactor d hdD)
  refine ⟨?_, (hSlo d hdD).trans hshi', ?_⟩
  · have hh := mul_le_mul hrlo' hslo' (by positivity) (by positivity)
    rw [← hdprod] at hh
    have hh' := mul_le_mul_of_nonneg_left (hh.trans (hQ d hdD)) (by norm_num : (0 : ℝ) ≤ 2)
    push_cast at hh' ⊢
    nlinarith only [hh']
  · have hh := mul_le_mul_of_nonneg_left (hslo'.trans (hShi d hdD)) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh

#print axioms weightedKernelL1_dyadic_le
#print axioms dyadicFactorCells_card_le
#print axioms dyadicFactorBlock_scale_bounds

end

end PrimeGap182.TypeIII
