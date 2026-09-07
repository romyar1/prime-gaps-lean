import IncidenceMaskedOriginal

/-!
# Original finite physical rows as linear functions of the amplitude

This representation preserves all original masks. It lets the actual
Taylor expansion act on the amplitude before squaring, and gives the
literal finite row mass needed for the remainder estimate.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def incidencePhysicalFeature {m w : ℕ} [NeZero m] [NeZero w]
    (e : ℕ) (A B : ℤ) (I : Finset ℤ) (χ : ℤ → ℂ) (γ l : ℤ) : ℂ :=
  if IsUnit (l : ZMod e) then
    ∑ n ∈ I, if IsUnit (n : ZMod w) ∧ (n : ZMod e) = (γ : ZMod e) * (l : ZMod e) then
      χ n * PrimeGap186.reciprocalUnitPhase m ((A : ZMod m) * (l : ZMod m))
        ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m)))
      else 0
  else 0

theorem incidencePhysicalRow_features {ι : Type*} [DecidableEq ι]
    {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (F : Finset ι) (I : Finset ℤ) (ell : ι → ℤ)
    (a : ι → ℂ) (χ : ℤ → ℂ) (γ : ℤ) :
    incidencePhysicalRow (m := m) (w := w) (e := e) A B (F.image ell) I
      (incidenceGroupedCoefficient F ell a) χ (γ : ZMod e) =
      ∑ h ∈ F, incidencePhysicalFeature (m := m) (w := w) e A B I χ γ (ell h) * a h := by
  unfold incidencePhysicalRow
  rw [incidenceGroupedCoefficient_sum]
  apply Finset.sum_congr rfl
  intro h _
  unfold incidencePhysicalFeature
  by_cases hl : IsUnit (ell h : ZMod e)
  · simp only [ite_eq_left hl]
    rw [mul_comm]
  · simp only [ite_eq_right hl, mul_zero, zero_mul]

theorem incidencePhysicalFeature_norm {m w : ℕ} [NeZero m] [NeZero w]
    (e : ℕ) (A B : ℤ) (I : Finset ℤ) (χ : ℤ → ℂ) (γ l : ℤ)
    (L : ℝ) (hL : 0 ≤ L) (hχ : ∀ n ∈ I, ‖χ n‖ ≤ L) :
    ‖incidencePhysicalFeature (m := m) (w := w) e A B I χ γ l‖ ≤ I.card * L := by
  unfold incidencePhysicalFeature
  by_cases hl : IsUnit (l : ZMod e)
  · rw [ite_eq_left hl]
    calc
      _ ≤ ∑ n ∈ I, L := by
        apply norm_sum_le_of_le
        intro n hn
        by_cases hnu : IsUnit (n : ZMod w) ∧ (n : ZMod e) = (γ : ZMod e) * (l : ZMod e)
        · rw [ite_eq_left hnu, norm_mul]
          exact (mul_le_mul (hχ n hn) (incidenceReciprocalPhase_norm_le_one _ _)
            (norm_nonneg _) hL).trans_eq (mul_one _)
        · simpa only [ite_eq_right hnu, norm_zero] using hL
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  · simp only [ite_eq_right hl, norm_zero]
    positivity

theorem incidenceWeightedPhysicalEnergy_features {ι : Type*} [DecidableEq ι]
    {m w : ℕ} [NeZero m] [NeZero w]
    (A B : ℤ) (D : Finset ℕ) (ρ : ℕ → ℝ) (F : Finset ι) (I : Finset ℤ)
    (ell : ι → ℤ) (a : ℕ → ι → ℂ) (χ : ℕ → ℤ → ℂ) :
    (∑ e ∈ D, ρ e * incidencePhysicalEnergyOrZero (m := m) (w := w) e A B
      (F.image ell) I (incidenceGroupedCoefficient F ell (a e)) (χ e)) =
      ∑ p ∈ incidenceOriginalRows D, ρ p.1 *
        ‖∑ h ∈ F, incidencePhysicalFeature (m := m) (w := w) p.1 A B I (χ p.1) p.2 (ell h) *
          a p.1 h‖ ^ 2 := by
  rw [incidenceOriginalRows_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e = 0
  · subst e
    simp only [incidencePhysicalEnergyOrZero, dite_true, mul_zero, Nat.cast_zero,
      Finset.Ico_self, Finset.sum_empty]
  · have : NeZero e := ⟨he⟩
    rw [incidencePhysicalEnergyOrZero_of_ne, incidencePhysicalEnergy,
      incidenceSumZMod_eq_Ico, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    rw [incidencePhysicalRow_features]

theorem incidenceOriginalRows_mass (D : Finset ℕ) (ρ : ℕ → ℝ) :
    (∑ p ∈ incidenceOriginalRows D, ρ p.1) = ∑ e ∈ D, ρ e * (e : ℝ) := by
  rw [incidenceOriginalRows_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.sum_const, nsmul_eq_mul, Int.card_Ico, sub_zero,
    Int.toNat_natCast, mul_comm]

theorem incidencePhysicalFeature_remainder_mass {ι : Type*}
    {m w : ℕ} [NeZero m] [NeZero w]
    (A B : ℤ) (D : Finset ℕ) (ρ : ℕ → ℝ) (hρ : ∀ e ∈ D, 0 ≤ ρ e)
    (F : Finset ι) (I : Finset ℤ) (ell : ι → ℤ) (χ : ℕ → ℤ → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hχ : ∀ e ∈ D, ∀ n ∈ I, ‖χ e n‖ ≤ L) :
    (∑ p ∈ incidenceOriginalRows D, ρ p.1 *
      (∑ h ∈ F, ‖incidencePhysicalFeature (m := m) (w := w) p.1 A B I (χ p.1) p.2 (ell h)‖) ^ 2) ≤
      ((F.card : ℝ) * (I.card : ℝ) * L) ^ 2 * ∑ e ∈ D, ρ e * (e : ℝ) := by
  rw [← incidenceOriginalRows_mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpD := (incidenceOriginalRows_mem D p).mp hp |>.1
  have hm : (∑ h ∈ F,
      ‖incidencePhysicalFeature (m := m) (w := w) p.1 A B I (χ p.1) p.2 (ell h)‖) ≤
      (F.card : ℝ) * (I.card : ℝ) * L := by
    calc
      _ ≤ ∑ _h ∈ F, (I.card : ℝ) * L := Finset.sum_le_sum (fun h _ =>
        incidencePhysicalFeature_norm p.1 A B I (χ p.1) p.2 (ell h) L hL (hχ p.1 hpD))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2) (hρ p.1 hpD)
  exact hh.trans_eq (mul_comm _ _)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePhysicalRow_features
#print axioms PrimeGap182Audit.incidencePhysicalFeature_norm
#print axioms PrimeGap182Audit.incidenceWeightedPhysicalEnergy_features
#print axioms PrimeGap182Audit.incidenceOriginalRows_mass
#print axioms PrimeGap182Audit.incidencePhysicalFeature_remainder_mass
