import TypeIIILocal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Exact reconstruction of the actual Type III four-cycle

The geometric argument studies products of corrected entries. This file
proves their exact expansion back to the actual arithmetic four-cycle and
the coefficient bounds used in that expansion. Its final Fourier estimate
has explicit hypotheses about the fifteen actual corrected subproducts.
Those hypotheses are not established here, and this is not a proof of
`LocalFourierHypothesis`.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- The fifteen nonempty subsets of the four positions in the cycle. -/
def nonemptyCoreSubsets : Finset (Finset (Fin 4)) := Finset.univ.erase ∅

@[simp] theorem mem_nonemptyCoreSubsets (S : Finset (Fin 4)) :
    S ∈ nonemptyCoreSubsets ↔ S ≠ ∅ := by
  simp [nonemptyCoreSubsets]

@[simp] theorem card_nonemptyCoreSubsets : nonemptyCoreSubsets.card = 15 := by
  norm_num [nonemptyCoreSubsets, Fintype.card_finset]

/-- The signed correction coefficient accompanying the factors indexed by `S`. -/
def coreExpansionCoeff (κ : ℂ) (S : Finset (Fin 4)) : ℂ := (-κ) ^ (4 - S.card)

/-- Exact expansion with the empty product explicitly separated. -/
theorem four_core_expansion (F : Fin 4 → ℂ) (κ : ℂ) :
    (∏ i, (F i - κ)) = κ ^ 4 +
      ∑ S ∈ nonemptyCoreSubsets, coreExpansionCoeff κ S * ∏ i ∈ S, F i := by
  have hexpand : (∏ i, (F i - κ)) =
      ∑ S : Finset (Fin 4), coreExpansionCoeff κ S * ∏ i ∈ S, F i := by
    simpa [sub_eq_add_neg, coreExpansionCoeff, Finset.prod_const,
      Finset.card_compl, mul_comm] using Fintype.prod_add F (fun _ => -κ)
  rw [hexpand]
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 4))))
    (f := fun S => coreExpansionCoeff κ S * ∏ i ∈ S, F i)
    (a := ∅) (Finset.mem_univ _)
  have hneg : (-κ) ^ 4 = κ ^ 4 := by ring
  simpa only [nonemptyCoreSubsets, coreExpansionCoeff, Finset.card_empty,
    Nat.sub_zero, Finset.prod_empty, mul_one, hneg, add_comm] using hsplit.symm

/-- The sum of the nonempty coefficient norms is an exact polynomial in `‖κ‖`. -/
theorem nonempty_core_coefficient_mass (κ : ℂ) :
    (∑ S ∈ nonemptyCoreSubsets, ‖coreExpansionCoeff κ S‖) =
      4 * ‖κ‖ ^ 3 + 6 * ‖κ‖ ^ 2 + 4 * ‖κ‖ + 1 := by
  have htotal : (∑ S : Finset (Fin 4), ‖coreExpansionCoeff κ S‖) =
      (1 + ‖κ‖) ^ 4 := by
    simpa [coreExpansionCoeff] using
      Fintype.sum_pow_mul_eq_add_pow (Fin 4) (1 : ℝ) ‖κ‖
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 4))))
    (f := fun S => ‖coreExpansionCoeff κ S‖)
    (a := ∅) (Finset.mem_univ _)
  have heq : (∑ S ∈ nonemptyCoreSubsets, ‖coreExpansionCoeff κ S‖) +
      ‖κ‖ ^ 4 = (1 + ‖κ‖) ^ 4 := by
    rw [← htotal]
    simpa only [nonemptyCoreSubsets, coreExpansionCoeff, Finset.card_empty,
      Nat.sub_zero, norm_pow, norm_neg] using hsplit
  nlinarith [heq]

/-- The numerical coefficient mass required in the manuscript. -/
theorem nonempty_core_coefficient_mass_le (κ : ℂ) (hκ : ‖κ‖ ≤ 3) :
    (∑ S ∈ nonemptyCoreSubsets, ‖coreExpansionCoeff κ S‖) ≤ 175 := by
  rw [nonempty_core_coefficient_mass]
  have h₂ : ‖κ‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg κ]
  have h₃ : ‖κ‖ ^ 3 ≤ 27 := by nlinarith [mul_le_mul h₂ hκ (norm_nonneg κ) (by norm_num : (0 : ℝ) ≤ 9)]
  nlinarith

/-- The coefficient of the empty core product has norm at most 81. -/
theorem empty_core_coefficient_le (κ : ℂ) (hκ : ‖κ‖ ≤ 3) :
    ‖κ ^ 4‖ ≤ 81 := by
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg κ) hκ 4).trans (by norm_num)

/-- The actual real correction `1 + p⁻¹ + p⁻²`. -/
def coreCorrection (p : ℕ) : ℝ := 1 + (p : ℝ)⁻¹ + ((p : ℝ)⁻¹) ^ 2

theorem coreCorrection_nonneg (p : ℕ) : 0 ≤ coreCorrection p := by
  unfold coreCorrection
  positivity

theorem coreCorrection_le_three (p : ℕ) [NeZero p] : coreCorrection p ≤ 3 := by
  have hp : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (NeZero.one_le : 1 ≤ p)
  have hi : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hi₀ : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  unfold coreCorrection
  nlinarith

theorem coreCorrection_complex_norm_le (p : ℕ) [NeZero p] :
    ‖(coreCorrection p : ℂ)‖ ≤ 3 := by
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coreCorrection_nonneg p)]
    using coreCorrection_le_three p

section FourierAssembly

variable (s : ℕ) [NeZero s]

/-- Restriction by zero to a chosen finite set of physical points. -/
def assemblyRestrict (U : Finset (ZMod s × ZMod s))
    (f : ZMod s → ZMod s → ℂ) (x y : ZMod s) : ℂ :=
  if (x, y) ∈ U then f x y else 0

/-- The chosen core subproduct, restricted by zero to the common open set. -/
def restrictedCoreSubproduct (U : Finset (ZMod s × ZMod s))
    (F : Fin 4 → ZMod s → ZMod s → ℂ) (S : Finset (Fin 4)) :
    ZMod s → ZMod s → ℂ :=
  assemblyRestrict s U (fun x y => ∏ i ∈ S, F i x y)

private theorem assembly_fourier_add (f g : ZMod s → ZMod s → ℂ) (h k : ZMod s) :
    fourier₂ s (fun x y => f x y + g x y) h k =
      fourier₂ s f h k + fourier₂ s g h k := by
  simp only [fourier₂, add_mul, Finset.sum_add_distrib]

private theorem assembly_fourier_const_mul (c : ℂ) (f : ZMod s → ZMod s → ℂ)
    (h k : ZMod s) :
    fourier₂ s (fun x y => c * f x y) h k = c * fourier₂ s f h k := by
  simp only [fourier₂, mul_assoc, Finset.mul_sum]

private theorem assembly_fourier_sum {ι : Type*} (T : Finset ι)
    (f : ι → ZMod s → ZMod s → ℂ) (h k : ZMod s) :
    fourier₂ s (fun x y => ∑ i ∈ T, f i x y) h k =
      ∑ i ∈ T, fourier₂ s (f i) h k := by
  induction T using Finset.induction_on with
  | empty => simp [fourier₂]
  | @insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    rw [assembly_fourier_add, ih]

/-- Exact reconstruction after restriction and the actual unnormalized Fourier transform. -/
theorem fourier_restricted_core_expansion (U : Finset (ZMod s × ZMod s))
    (F : Fin 4 → ZMod s → ZMod s → ℂ) (κ : ℂ) (h k : ZMod s) :
    fourier₂ s (assemblyRestrict s U (fun x y => ∏ i, (F i x y - κ))) h k =
      κ ^ 4 * fourier₂ s (assemblyRestrict s U (fun _ _ => 1)) h k +
      ∑ S ∈ nonemptyCoreSubsets, coreExpansionCoeff κ S *
        fourier₂ s (restrictedCoreSubproduct s U F S) h k := by
  have heq : assemblyRestrict s U (fun x y => ∏ i, (F i x y - κ)) =
      fun x y => κ ^ 4 * assemblyRestrict s U (fun _ _ => 1) x y +
        ∑ S ∈ nonemptyCoreSubsets, coreExpansionCoeff κ S *
          restrictedCoreSubproduct s U F S x y := by
    funext x y
    by_cases hxy : (x, y) ∈ U
    · simpa only [assemblyRestrict, restrictedCoreSubproduct, ite_eq_left hxy, mul_one]
        using four_core_expansion (fun i => F i x y) κ
    · simp [assemblyRestrict, restrictedCoreSubproduct, hxy]
  rw [heq, assembly_fourier_add, assembly_fourier_const_mul, assembly_fourier_sum]
  congr 1
  exact Finset.sum_congr rfl (fun S hS => assembly_fourier_const_mul s _ _ h k)

/-- The empty product requires only the elementary cardinality bound `s²`. -/
theorem fourier_restricted_one_norm_le (U : Finset (ZMod s × ZMod s)) (h k : ZMod s) :
    ‖fourier₂ s (assemblyRestrict s U (fun _ _ => 1)) h k‖ ≤ (s : ℝ) ^ 2 := by
  unfold fourier₂
  calc
    _ ≤ ∑ _x : ZMod s, ∑ _y : ZMod s, (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro x hx
      apply norm_sum_le_of_le
      intro y hy
      by_cases hxy : (x, y) ∈ U <;>
        simp [assemblyRestrict, hxy, ZMod.stdAddChar_apply, Circle.norm_coe]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      ring

/-- Quantitative reconstruction. The premise is about the fifteen explicitly
defined corrected subproducts, not about an unspecified auxiliary function. -/
theorem fourier_restricted_core_bound (U : Finset (ZMod s × ZMod s))
    (F : Fin 4 → ZMod s → ZMod s → ℂ) (κ : ℂ) (hκ : ‖κ‖ ≤ 3)
    (M : ℝ) (hM : 0 ≤ M) (h k : ZMod s)
    (hcore : ∀ S ∈ nonemptyCoreSubsets,
      ‖fourier₂ s (restrictedCoreSubproduct s U F S) h k‖ ≤ M) :
    ‖fourier₂ s (assemblyRestrict s U (fun x y => ∏ i, (F i x y - κ))) h k‖ ≤
      81 * (s : ℝ) ^ 2 + 175 * M := by
  rw [fourier_restricted_core_expansion]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    exact mul_le_mul (empty_core_coefficient_le κ hκ)
      (fourier_restricted_one_norm_le s U h k) (norm_nonneg _) (by norm_num)
  · calc
      _ ≤ ∑ S ∈ nonemptyCoreSubsets, ‖coreExpansionCoeff κ S‖ *
          ‖fourier₂ s (restrictedCoreSubproduct s U F S) h k‖ := by
        simpa only [norm_mul] using
          norm_sum_le nonemptyCoreSubsets (fun S => coreExpansionCoeff κ S *
            fourier₂ s (restrictedCoreSubproduct s U F S) h k)
      _ ≤ ∑ S ∈ nonemptyCoreSubsets, ‖coreExpansionCoeff κ S‖ * M := by
        exact Finset.sum_le_sum fun S hS =>
          mul_le_mul_of_nonneg_left (hcore S hS) (norm_nonneg _)
      _ = (∑ S ∈ nonemptyCoreSubsets, ‖coreExpansionCoeff κ S‖) * M := by
        rw [Finset.sum_mul]
      _ ≤ 175 * M := mul_le_mul_of_nonneg_right (nonempty_core_coefficient_mass_le κ hκ) hM

/-- The arithmetic union of the fifteen core exceptional sets. -/
def assembledCoreExceptionalSet
    (Z : Finset (Fin 4) → Finset (ZMod s × ZMod s)) : Finset (ZMod s × ZMod s) :=
  nonemptyCoreSubsets.biUnion Z

omit [NeZero s] in
theorem core_exceptional_subset_assembled
    (Z : Finset (Fin 4) → Finset (ZMod s × ZMod s))
    (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) :
    Z S ⊆ assembledCoreExceptionalSet s Z :=
  Finset.subset_biUnion_of_mem Z hS

omit [NeZero s] in
theorem assembledCoreExceptionalSet_card_le
    (Z : Finset (Fin 4) → Finset (ZMod s × ZMod s)) (D : ℕ)
    (hZ : ∀ S ∈ nonemptyCoreSubsets, (Z S).card ≤ D) :
    (assembledCoreExceptionalSet s Z).card ≤ 15 * D := by
  simpa only [assembledCoreExceptionalSet, card_nonemptyCoreSubsets] using
    Finset.card_biUnion_le_card_mul nonemptyCoreSubsets Z D hZ

end FourierAssembly

section ActualCycle

variable (p : ℕ) [Fact p.Prime]

/-- The arithmetic kernel plus the manuscript's exact real stalk correction.
No sheaf realization or purity theorem is asserted by this definition. -/
def correctedKernel (α m n x y : ZMod p) : ℂ :=
  kernel p α m n x y + (coreCorrection p : ℂ)

/-- The four corrected factors with precisely the original conjugation pattern. -/
def correctedCycleFactors (α m m' n n' : ZMod p) (i : Fin 4)
    (x y : ZMod p) : ℂ :=
  ![correctedKernel p α m n x y,
    star (correctedKernel p α m' n x y),
    correctedKernel p α m' n' x y,
    star (correctedKernel p α m n' x y)] i

/-- Subtracting the real correction recovers the actual raw cycle at every point. -/
theorem fourCycle_eq_corrected_product (α m m' n n' x y : ZMod p) :
    fourCycle p α m m' n n' x y =
      ∏ i : Fin 4, (correctedCycleFactors p α m m' n n' i x y -
        (coreCorrection p : ℂ)) := by
  simp [Fin.prod_univ_four, correctedCycleFactors, correctedKernel, fourCycle]

private theorem fourCycle_eq_corrected_function (α m m' n n' : ZMod p) :
    fourCycle p α m m' n n' = fun x y =>
      ∏ i : Fin 4, (correctedCycleFactors p α m m' n n' i x y -
        (coreCorrection p : ℂ)) := by
  funext x y
  exact fourCycle_eq_corrected_product p α m m' n n' x y

/-- The exact correction expansion of the original arithmetic four-cycle. -/
theorem actual_fourCycle_core_expansion (α m m' n n' x y : ZMod p) :
    fourCycle p α m m' n n' x y = (coreCorrection p : ℂ) ^ 4 +
      ∑ S ∈ nonemptyCoreSubsets, coreExpansionCoeff (coreCorrection p : ℂ) S *
        ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y := by
  rw [fourCycle_eq_corrected_product]
  exact four_core_expansion _ _

/-- The fifteen concrete finite sums to which the remaining geometry must apply. -/
def actualRestrictedCoreSubproduct (U : Finset (ZMod p × ZMod p))
    (α m m' n n' : ZMod p) (S : Finset (Fin 4)) : ZMod p → ZMod p → ℂ :=
  restrictedCoreSubproduct p U (correctedCycleFactors p α m m' n n') S

/-- Exact Fourier identity, including the empty core term and all signs. -/
theorem actual_fourCycle_fourier_core_expansion (U : Finset (ZMod p × ZMod p))
    (α m m' n n' h k : ZMod p) :
    fourier₂ p (assemblyRestrict p U (fourCycle p α m m' n n')) h k =
      (coreCorrection p : ℂ) ^ 4 *
        fourier₂ p (assemblyRestrict p U (fun _ _ => 1)) h k +
      ∑ S ∈ nonemptyCoreSubsets, coreExpansionCoeff (coreCorrection p : ℂ) S *
        fourier₂ p (actualRestrictedCoreSubproduct p U α m m' n n' S) h k := by
  rw [fourCycle_eq_corrected_function]
  exact fourier_restricted_core_expansion p U _ _ h k

/-- The raw restricted Fourier estimate from explicit estimates of the actual
corrected subproducts. The premise remains a mathematical obligation. -/
theorem actual_fourCycle_fourier_le_of_core_bounds (U : Finset (ZMod p × ZMod p))
    (α m m' n n' h k : ZMod p) (M : ℝ) (hM : 0 ≤ M)
    (hcore : ∀ S ∈ nonemptyCoreSubsets,
      ‖fourier₂ p (actualRestrictedCoreSubproduct p U α m m' n n' S) h k‖ ≤ M) :
    ‖fourier₂ p (assemblyRestrict p U (fourCycle p α m m' n n')) h k‖ ≤
      81 * (p : ℝ) ^ 2 + 175 * M := by
  rw [fourCycle_eq_corrected_function]
  exact fourier_restricted_core_bound p U _ _ (coreCorrection_complex_norm_le p)
    M hM h k hcore

end ActualCycle

#print axioms card_nonemptyCoreSubsets
#print axioms four_core_expansion
#print axioms nonempty_core_coefficient_mass
#print axioms nonempty_core_coefficient_mass_le
#print axioms empty_core_coefficient_le
#print axioms coreCorrection_le_three
#print axioms coreCorrection_complex_norm_le
#print axioms fourier_restricted_core_expansion
#print axioms fourier_restricted_one_norm_le
#print axioms fourier_restricted_core_bound
#print axioms core_exceptional_subset_assembled
#print axioms assembledCoreExceptionalSet_card_le
#print axioms fourCycle_eq_corrected_product
#print axioms actual_fourCycle_core_expansion
#print axioms actual_fourCycle_fourier_core_expansion
#print axioms actual_fourCycle_fourier_le_of_core_bounds

end

end PrimeGap182.TypeIII
