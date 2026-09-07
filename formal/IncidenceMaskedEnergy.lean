import IncidenceSourceRowEnergy

/-!
# The original source masks reduce to explicit signed sectors

Both original numerator coprimality masks are absorbed only against
the actual zero-extended phase. The outside divisor and compatibility
reductions are then composed with the frequency-divisor energy bound.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem incidencePhysicalEnergy_absorb_source
    (r₁ q₀ u₁ v₁ v₂ q₂ w e b₁ b₂ : ℕ)
    [NeZero (r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂)] [NeZero w] [NeZero e]
    (A B ℓ : ℤ) (E : ZMod q₀ → Finset (ZMod q₀)) (ψN : ℝ → ℝ) (N : ℝ)
    (hBr : (B : ZMod r₁) = 0)
    (hBW : (B : ZMod (q₀ * u₁ * Nat.lcm v₁ v₂)) = 0)
    (hBq : (B : ZMod q₂) = ((ℓ * (r₁ : ℤ) : ℤ) : ZMod q₂))
    (hE : ∀ n : ℤ, PrimeGap186.sourceCompatibility ((w * e) * r₁) q₀ b₁ b₂ ℓ n =
      if (n : ZMod q₀) ∈ E ((w * e : ℕ) : ZMod q₀) then 1 else 0)
    (Λ I : Finset ℤ) (coeff : ℤ → ℂ) :
    incidencePhysicalEnergy (m := r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂) (w := w) (e := e)
      A B Λ I coeff (incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N) =
    incidencePhysicalEnergy (m := r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂) (w := w) (e := e)
      A B Λ I coeff
      (fun n => if (n : ZMod q₀) ∈ E ((w * e : ℕ) : ZMod q₀)
        then (ψN ((n : ℝ) / N) : ℂ) else 0) := by
  unfold incidencePhysicalEnergy
  apply Finset.sum_congr rfl
  intro γ _
  congr 2
  unfold incidencePhysicalRow
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  by_cases hl : IsUnit (l : ZMod e)
  · simp only [ite_eq_left hl]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : IsUnit (n : ZMod w) ∧ (n : ZMod e) = γ * (l : ZMod e)
    · simp only [ite_eq_left hn]
      exact incidenceSourceNumerator_absorb_phase r₁ q₀ u₁ v₁ v₂ q₂ (w * e) e b₁ b₂
        B ℓ E ψN N hBr hBW hBq hE
        ((A : ZMod (r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂)) *
          (l : ZMod (r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂))) n
    · simp only [ite_eq_right hn]
  · simp only [ite_eq_right hl]

def incidenceOutsideSectorEnergy {m w e q₀ : ℕ}
    [NeZero m] [NeZero w] [NeZero e] [NeZero q₀]
    (hwm : Nat.Coprime w m) (hq₀m : q₀ ∣ m) (hqe : Nat.Coprime q₀ e)
    (w₂ c : ℕ) (hc : c ∣ w) (A B : ℤ) (Λ : Finset ℤ)
    (S : Finset (ZMod q₀)) (coeff χ : ℤ → ℂ) : ℝ :=
  let uc : (ZMod m)ˣ := ZMod.unitOfCoprime c (hwm.of_dvd_left hc)
  let vc : (ZMod q₀)ˣ := ZMod.unitOfCoprime c ((hwm.of_dvd_left hc).of_dvd_right hq₀m)
  ∑ ζ ∈ incidenceCompatibilityLines vc (ZMod.unitOfCoprime e hqe.symm) S,
    ∑ t ∈ e.divisors, ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ),
      ‖∑ a ∈ incidenceDividedCoefficientSet Λ (t * w₂),
        coeff (((t * w₂ : ℕ) : ℤ) * a) *
          incidenceProgressionResponse ((A : ZMod m) * ((uc⁻¹ : (ZMod m)ˣ) : ZMod m))
            (B * ((w / c : ℕ) : ℤ)) q₀ e (ζ.val : ℤ) γ
            (fun n => χ ((c : ℤ) * n)) (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2

theorem incidencePhysicalEnergy_masked_sector_bound {m w e q₀ : ℕ}
    [NeZero m] [NeZero w] [NeZero e] [NeZero q₀]
    (hwm : Nat.Coprime w m) (hwe : Nat.Coprime w e)
    (hq₀m : q₀ ∣ m) (hqe : Nat.Coprime q₀ e)
    (w₂ : ℕ) (hw₂e : Nat.Coprime w₂ e)
    (A B : ℤ) (Λ I : Finset ℤ) (hΛ : ∀ l ∈ Λ, (w₂ : ℤ) ∣ l)
    (S : Finset (ZMod q₀)) (κ : ℝ) (hκ : (S.card : ℝ) ≤ κ)
    (coeff χ : ℤ → ℂ) (hχ : ∀ n, χ n ≠ 0 → n ∈ I) :
    incidencePhysicalEnergy (m := m) (w := w) (e := e) A B Λ I coeff
        (fun n => if (n : ZMod q₀) ∈ S then χ n else 0) ≤
      (w.divisors.card : ℝ) * κ * (e.divisors.card : ℝ) *
        ∑ c ∈ w.divisors.attach,
          incidenceOutsideSectorEnergy hwm hq₀m hqe w₂ c.1 (Nat.dvd_of_mem_divisors c.2)
            A B Λ S coeff χ := by
  apply (incidencePhysicalEnergy_divisor_bound hwm hwe A B Λ I coeff
    (fun n => if (n : ZMod q₀) ∈ S then χ n else 0)).trans
  calc
    _ ≤ (w.divisors.card : ℝ) * ∑ c ∈ w.divisors.attach,
        κ * (e.divisors.card : ℝ) *
          incidenceOutsideSectorEnergy hwm hq₀m hqe w₂ c.1 (Nat.dvd_of_mem_divisors c.2)
            A B Λ S coeff χ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro c _
      have hcw : c.1 ∣ w := Nat.dvd_of_mem_divisors c.2
      have hc0 : c.1 ≠ 0 := (Nat.pos_of_dvd_of_pos hcw
        (Nat.pos_of_ne_zero (NeZero.ne w))).ne'
      let uc : (ZMod m)ˣ := ZMod.unitOfCoprime c.1 (hwm.of_dvd_left hcw)
      let vc : (ZMod q₀)ˣ := ZMod.unitOfCoprime c.1 ((hwm.of_dvd_left hcw).of_dvd_right hq₀m)
      have hχc : ∀ n : ℤ, χ ((c.1 : ℤ) * n) ≠ 0 → n ∈ incidenceDividedCoefficientSet I c.1 := by
        intro n hn
        rw [incidenceDividedCoefficientSet_mem I c.1 hc0]
        exact hχ _ hn
      have hb := incidenceSourceRow_compatibility_sector_energy hqe w₂ hw₂e vc S κ hκ
        ((A : ZMod m) * ((uc⁻¹ : (ZMod m)ˣ) : ZMod m))
        (B * ((w / c.1 : ℕ) : ℤ)) Λ (incidenceDividedCoefficientSet I c.1) hΛ coeff
        (fun n => χ ((c.1 : ℤ) * n)) hχc
      simpa only [incidenceOutsideSectorEnergy, incidenceDividedCoefficientSet,
        vc, uc, ZMod.coe_unitOfCoprime, Int.cast_mul, Int.cast_natCast] using hb
    _ = _ := by rw [← Finset.mul_sum]; ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePhysicalEnergy_absorb_source
#print axioms PrimeGap182Audit.incidencePhysicalEnergy_masked_sector_bound
