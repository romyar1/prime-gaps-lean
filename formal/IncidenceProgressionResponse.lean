import IncidenceFrequencySectors

/-!
# Exact source progression responses, including the full frequency mask

The finite numerator interval is replaced by an unrestricted integer sum
only after proving its support is unchanged. The resulting identity
expands every coprimality sign before any positive energy estimate.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

set_option maxHeartbeats 1200000

def incidenceProgressionResponse {m : ℕ} [NeZero m]
    (A : ZMod m) (B : ℤ) (q₀ e : ℕ) (ζ γ : ℤ) (χ : ℤ → ℂ) (l : ℤ) : ℂ :=
  ∑' k : ℤ,
    χ (ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k)) *
      PrimeGap186.reciprocalUnitPhase m (A * (l : ZMod m))
        ((e : ZMod m) *
          (((ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k) : ℤ) : ZMod m) +
            (B : ZMod m) * (e : ZMod m)))

theorem incidenceTwoModulus_tsum_reindex (q₀ e : ℕ) (hq : 0 < q₀) (he : 0 < e)
    (hqe : Nat.Coprime q₀ e) (ζ γ l : ℤ) (I : Finset ℤ) (χ G : ℤ → ℂ)
    (hχ : ∀ n, χ n ≠ 0 → n ∈ I) :
    (∑ n ∈ I, if (n : ZMod q₀) = (ζ : ZMod q₀) * (e : ZMod q₀) ∧
        (n : ZMod e) = (q₀ : ZMod e) * (γ : ZMod e) * (l : ZMod e)
      then χ n * G n else 0) =
      ∑' k : ℤ,
        χ (ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k)) *
          G (ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k)) := by
  rw [incidenceTwoModulus_sum_reindex q₀ e hqe]
  symm
  apply tsum_eq_sum
  intro k hk
  have ha : ((q₀ * e : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (mul_pos hq he).ne'
  have hn : χ (ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k)) = 0 := by
    by_contra hn
    apply hk
    rw [incidenceProgressionIndex_mem _ _ ha]
    convert hχ _ hn using 1
    push_cast
    ring
  rw [hn, zero_mul]

theorem incidenceUnmaskedPhysicalRow_progression
    {m e q₀ : ℕ} [NeZero m] [NeZero e] [NeZero q₀]
    (hqe : Nat.Coprime q₀ e) (A : ZMod m) (B ζ γ : ℤ)
    (Λ I : Finset ℤ) (a χ : ℤ → ℂ) (hχ : ∀ n, χ n ≠ 0 → n ∈ I) :
    incidenceUnmaskedPhysicalRow A B Λ I a
        (fun n => if (n : ZMod q₀) = (ζ : ZMod q₀) * (e : ZMod q₀) then χ n else 0)
        ((q₀ : ZMod e) * (γ : ZMod e)) =
      ∑ l ∈ Λ, if IsUnit (l : ZMod e) then
        a l * incidenceProgressionResponse A B q₀ e ζ γ χ l else 0 := by
  unfold incidenceUnmaskedPhysicalRow
  apply Finset.sum_congr rfl
  intro l _
  by_cases hu : IsUnit (l : ZMod e)
  · simp only [ite_eq_left hu]
    congr 1
    let G : ℤ → ℂ := fun n => PrimeGap186.reciprocalUnitPhase m (A * (l : ZMod m))
      ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * (e : ZMod m)))
    have hr := incidenceTwoModulus_tsum_reindex q₀ e
      (Nat.pos_of_ne_zero (NeZero.ne q₀)) (Nat.pos_of_ne_zero (NeZero.ne e))
      hqe ζ γ l I χ G hχ
    change _ = ∑' k : ℤ,
      χ (ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k)) *
        G (ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k))
    rw [← hr]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [G]
    split_ifs <;> simp_all
  · simp only [ite_eq_right hu, mul_zero]

theorem incidenceUnmaskedPhysicalRow_progression_sectors
    {m e q₀ : ℕ} [NeZero m] [NeZero e] [NeZero q₀]
    (hqe : Nat.Coprime q₀ e) (w₂ : ℕ) (hwe : Nat.Coprime w₂ e)
    (A : ZMod m) (B ζ γ : ℤ) (Λ I : Finset ℤ)
    (hΛ : ∀ l ∈ Λ, (w₂ : ℤ) ∣ l)
    (a χ : ℤ → ℂ) (hχ : ∀ n, χ n ≠ 0 → n ∈ I) :
    incidenceUnmaskedPhysicalRow A B Λ I a
        (fun n => if (n : ZMod q₀) = (ζ : ZMod q₀) * (e : ZMod q₀) then χ n else 0)
        ((q₀ : ZMod e) * (γ : ZMod e)) =
      ∑ t ∈ e.divisors, ((ArithmeticFunction.moebius t : ℤ) : ℂ) *
        ∑ b ∈ incidenceDividedCoefficientSet Λ (t * w₂),
          a (((t * w₂ : ℕ) : ℤ) * b) *
            incidenceProgressionResponse A B q₀ e ζ γ χ (((t * w₂ : ℕ) : ℤ) * b) := by
  rw [incidenceUnmaskedPhysicalRow_progression hqe A B ζ γ Λ I a χ hχ]
  simpa only using incidenceFrequencySectors_moebius e w₂ (Nat.pos_of_ne_zero (NeZero.ne e))
    hwe Λ hΛ (fun l => a l * incidenceProgressionResponse A B q₀ e ζ γ χ l)

theorem incidenceUnmaskedPhysicalRow_sector_energy
    {m e q₀ : ℕ} [NeZero m] [NeZero e] [NeZero q₀]
    (hqe : Nat.Coprime q₀ e) (w₂ : ℕ) (hwe : Nat.Coprime w₂ e)
    (A : ZMod m) (B ζ γ : ℤ) (Λ I : Finset ℤ)
    (hΛ : ∀ l ∈ Λ, (w₂ : ℤ) ∣ l)
    (a χ : ℤ → ℂ) (hχ : ∀ n, χ n ≠ 0 → n ∈ I) :
    ‖incidenceUnmaskedPhysicalRow A B Λ I a
        (fun n => if (n : ZMod q₀) = (ζ : ZMod q₀) * (e : ZMod q₀) then χ n else 0)
        ((q₀ : ZMod e) * (γ : ZMod e))‖ ^ 2 ≤
      (e.divisors.card : ℝ) * ∑ t ∈ e.divisors,
        ‖∑ b ∈ incidenceDividedCoefficientSet Λ (t * w₂),
          a (((t * w₂ : ℕ) : ℤ) * b) *
            incidenceProgressionResponse A B q₀ e ζ γ χ (((t * w₂ : ℕ) : ℤ) * b)‖ ^ 2 := by
  rw [incidenceUnmaskedPhysicalRow_progression hqe A B ζ γ Λ I a χ hχ]
  simpa only using incidenceFrequencySectors_energy e w₂ (Nat.pos_of_ne_zero (NeZero.ne e))
    hwe Λ hΛ (fun l => a l * incidenceProgressionResponse A B q₀ e ζ γ χ l)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceTwoModulus_tsum_reindex
#print axioms PrimeGap182Audit.incidenceUnmaskedPhysicalRow_progression
#print axioms PrimeGap182Audit.incidenceUnmaskedPhysicalRow_progression_sectors
#print axioms PrimeGap182Audit.incidenceUnmaskedPhysicalRow_sector_energy
