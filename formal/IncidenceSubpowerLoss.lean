import IncidenceUniformProfile
import PrimeGaps186

/-!
# Uniform losses for all integers of polynomial height

The divisor estimate applies to arbitrary positive integers, including
the nonsquarefree row divisors. The harmonic estimate is the actual
finite reciprocal sum. Its elementary proof is adapted from the local
harmonic calculation in the public sourceSecondary_uniform_loss_packet.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

theorem incidenceLog_subpower (C D η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in Filter.atTop, C * (Real.log x) ^ D ≤ x ^ η := by
  filter_upwards [((isLittleO_log_rpow_rpow_atTop D hη).const_mul_left C).eventuallyLE,
    Filter.eventually_ge_atTop (0 : ℝ)] with x hx hx0
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 η)] using hx)

theorem incidenceDivisors_subpower (η B : ℝ) (hη : 0 < η) (hB : 0 < B) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ n : ℕ,
      n ≠ 0 → (n : ℝ) ≤ x ^ B → (n.divisors.card : ℝ) ≤ x ^ η := by
  obtain ⟨C, hC, hbound⟩ := PrimeGap186.exists_card_divisors_bound
    (show 0 < η / (2 * B) by positivity)
  filter_upwards [(tendsto_rpow_atTop (by positivity : 0 < η / 2)).eventually_ge_atTop C,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hCx hx
  intro n hn hnheight
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hnsmall : (n : ℝ) ^ (η / (2 * B)) ≤ x ^ (η / 2) := by
    calc
      _ ≤ (x ^ B) ^ (η / (2 * B)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hnheight (by positivity)
      _ = _ := by rw [← Real.rpow_mul hx0.le]; congr 1; field_simp
  calc
    _ ≤ C * (n : ℝ) ^ (η / (2 * B)) := hbound n hn
    _ ≤ x ^ (η / 2) * x ^ (η / 2) :=
      mul_le_mul hCx hnsmall (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

theorem incidenceHarmonic_height_bound (x B : ℝ) (hx : 1 ≤ x) (hB : 0 ≤ B)
    (Dmax : ℕ) (W : Finset ℕ) (hW : W ⊆ Finset.Icc 1 Dmax)
    (hD : (Dmax : ℝ) ≤ x ^ B) :
    (∑ w ∈ W, (w : ℝ)⁻¹) ≤ 1 + B * Real.log x := by
  have hsum : (∑ w ∈ W, (w : ℝ)⁻¹) ≤ (harmonic Dmax : ℝ) := by
    calc
      _ ≤ ∑ w ∈ Finset.Icc 1 Dmax, (w : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hW (fun w _ _ => by positivity)
      _ = _ := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hlog : Real.log (Dmax : ℝ) ≤ B * Real.log x := by
    by_cases hzero : Dmax = 0
    · simp only [hzero, Nat.cast_zero, Real.log_zero]
      exact mul_nonneg hB (Real.log_nonneg hx)
    · simpa only [Real.log_rpow (zero_lt_one.trans_le hx)] using
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hzero) hD
  exact hsum.trans ((harmonic_le_one_add_log Dmax).trans (add_le_add_right hlog 1))

theorem incidenceHarmonic_subpower (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ (Dmax : ℕ) (W : Finset ℕ),
      W ⊆ Finset.Icc 1 Dmax → (Dmax : ℝ) ≤ x ^ B →
        (∑ w ∈ W, (w : ℝ)⁻¹) ≤ x ^ η := by
  filter_upwards [incidenceLog_subpower (1 + B) 1 η hη,
    Filter.eventually_ge_atTop (Real.exp 1)] with x hlog hxe
  have hx : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxe
  have hlogx : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
  intro Dmax W hW hD
  apply (incidenceHarmonic_height_bound x B hx hB Dmax W hW hD).trans
  calc
    1 + B * Real.log x ≤ (1 + B) * Real.log x := by linarith only [hlogx]
    _ ≤ _ := by simpa only [Real.rpow_one] using hlog

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceLog_subpower
#print axioms PrimeGap182Audit.incidenceDivisors_subpower
#print axioms PrimeGap182Audit.incidenceHarmonic_height_bound
#print axioms PrimeGap182Audit.incidenceHarmonic_subpower
