import IncidenceMaskedEnergy
import IncidenceOriginalSector

/-!
# All original masked rows reduce to the actual progression sum

The definition at e=0 is zero only to avoid a varying nonzero typeclass.
The source row set excludes zero explicitly. Every remaining mask is
then handled by the previously proved identities, before summation.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def incidencePhysicalEnergyOrZero {m w : ℕ} [NeZero m] [NeZero w]
    (e : ℕ) (A B : ℤ) (Λ I : Finset ℤ) (coeff χ : ℤ → ℂ) : ℝ :=
  if he : e = 0 then 0 else
    letI : NeZero e := ⟨he⟩
    incidencePhysicalEnergy (m := m) (w := w) (e := e) A B Λ I coeff χ

theorem incidencePhysicalEnergyOrZero_of_ne {m w e : ℕ}
    [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (Λ I : Finset ℤ) (coeff χ : ℤ → ℂ) :
    incidencePhysicalEnergyOrZero (m := m) (w := w) e A B Λ I coeff χ =
      incidencePhysicalEnergy (m := m) (w := w) (e := e) A B Λ I coeff χ := by
  exact dite_eq_right (NeZero.ne e)

def incidenceOriginalProgressionEnergy {m q₀ : ℕ} [NeZero m] [NeZero q₀]
    (A : ZMod m) (B : ℤ) (D : Finset ℕ) (ρ : ℕ → ℝ) (w₂ : ℕ)
    (Λ : Finset ℤ) (Lines : ZMod q₀ → Finset (ZMod q₀)) (coeff χ : ℤ → ℂ) : ℝ :=
  ∑ e ∈ D, ρ e * ∑ t ∈ e.divisors, ∑ ζ ∈ Lines (e : ZMod q₀),
    ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ),
      ‖∑ a ∈ incidenceDividedCoefficientSet Λ (t * w₂),
        coeff (((t * w₂ : ℕ) : ℤ) * a) *
          incidenceProgressionResponse A B q₀ e (ζ.val : ℤ) γ χ
            (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2

theorem incidenceOriginalProgressionEnergy_nonneg {m q₀ : ℕ} [NeZero m] [NeZero q₀]
    (A : ZMod m) (B : ℤ) (D : Finset ℕ) (ρ : ℕ → ℝ)
    (hρ : ∀ e ∈ D, 0 ≤ ρ e) (w₂ : ℕ) (Λ : Finset ℤ)
    (Lines : ZMod q₀ → Finset (ZMod q₀)) (coeff χ : ℤ → ℂ) :
    0 ≤ incidenceOriginalProgressionEnergy A B D ρ w₂ Λ Lines coeff χ := by
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (hρ e he) (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

theorem incidencePhysicalWeighted_masked_to_progression {m w q₀ : ℕ}
    [NeZero m] [NeZero w] [NeZero q₀]
    (hwm : Nat.Coprime w m) (hq₀m : q₀ ∣ m) (w₂ : ℕ)
    (A B : ℤ) (Λ I : Finset ℤ) (hΛ : ∀ l ∈ Λ, (w₂ : ℤ) ∣ l)
    (S : ZMod q₀ → Finset (ZMod q₀)) (κ τ : ℝ) (hκ : 0 ≤ κ) (_hτ : 0 ≤ τ)
    (hS : ∀ r, IsUnit r → ((S r).card : ℝ) ≤ κ)
    (D : Finset ℕ) (ρ : ℕ → ℝ) (hρ : ∀ e ∈ D, 0 ≤ ρ e)
    (hD : ∀ e ∈ D, e ≠ 0 ∧ Nat.Coprime e m ∧ Nat.Coprime w e ∧
      Nat.Coprime w₂ e ∧ (e.divisors.card : ℝ) ≤ τ)
    (coeff χ : ℤ → ℂ) (hχ : ∀ n, χ n ≠ 0 → n ∈ I) :
    (∑ e ∈ D, ρ e * incidencePhysicalEnergyOrZero (m := m) (w := w) e A B Λ I coeff
      (fun n => if (n : ZMod q₀) ∈ S (e : ZMod q₀) then χ n else 0)) ≤
      (w.divisors.card : ℝ) * κ * τ *
        ∑ c ∈ w.divisors.attach,
          let hc := Nat.dvd_of_mem_divisors c.2
          let uc := ZMod.unitOfCoprime c.1 (hwm.of_dvd_left hc)
          let vc := ZMod.unitOfCoprime c.1 ((hwm.of_dvd_left hc).of_dvd_right hq₀m)
          incidenceOriginalProgressionEnergy
            ((A : ZMod m) * ((uc⁻¹ : (ZMod m)ˣ) : ZMod m))
            (B * ((w / c.1 : ℕ) : ℤ)) D ρ w₂ Λ
            (incidenceAllCompatibilityLines vc S) coeff (fun n => χ ((c.1 : ℤ) * n)) := by
  let F (e : ℕ) (c : {c // c ∈ w.divisors}) : ℝ :=
    let hc := Nat.dvd_of_mem_divisors c.2
    let uc := ZMod.unitOfCoprime c.1 (hwm.of_dvd_left hc)
    let vc := ZMod.unitOfCoprime c.1 ((hwm.of_dvd_left hc).of_dvd_right hq₀m)
    ∑ t ∈ e.divisors, ∑ ζ ∈ incidenceAllCompatibilityLines vc S (e : ZMod q₀),
      ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ),
        ‖∑ a ∈ incidenceDividedCoefficientSet Λ (t * w₂),
          coeff (((t * w₂ : ℕ) : ℤ) * a) *
            incidenceProgressionResponse ((A : ZMod m) * ((uc⁻¹ : (ZMod m)ˣ) : ZMod m))
              (B * ((w / c.1 : ℕ) : ℤ)) q₀ e (ζ.val : ℤ) γ
              (fun n => χ ((c.1 : ℤ) * n)) (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2
  have hF (e : ℕ) (c : {c // c ∈ w.divisors}) : 0 ≤ F e c :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hrow (e : ℕ) (he : e ∈ D) :
      incidencePhysicalEnergyOrZero (m := m) (w := w) e A B Λ I coeff
        (fun n => if (n : ZMod q₀) ∈ S (e : ZMod q₀) then χ n else 0) ≤
      (w.divisors.card : ℝ) * κ * τ * ∑ c ∈ w.divisors.attach, F e c := by
    obtain ⟨he0, hem, hwe, hw₂e, het⟩ := hD e he
    have : NeZero e := ⟨he0⟩
    have hqe : Nat.Coprime q₀ e := (hem.of_dvd_right hq₀m).symm
    have heu : IsUnit (e : ZMod q₀) := (ZMod.isUnit_iff_coprime e q₀).mpr hqe.symm
    rw [incidencePhysicalEnergyOrZero_of_ne]
    have hb := incidencePhysicalEnergy_masked_sector_bound hwm hwe hq₀m hqe w₂ hw₂e
      A B Λ I hΛ (S (e : ZMod q₀)) κ (hS _ heu) coeff χ hχ
    have hid (c : {c // c ∈ w.divisors}) :
        incidenceOutsideSectorEnergy hwm hq₀m hqe w₂ c.1 (Nat.dvd_of_mem_divisors c.2)
          A B Λ (S (e : ZMod q₀)) coeff χ = F e c := by
      dsimp only [incidenceOutsideSectorEnergy, F]
      let vc := ZMod.unitOfCoprime c.1
        ((hwm.of_dvd_left (Nat.dvd_of_mem_divisors c.2)).of_dvd_right hq₀m)
      have hl := incidenceAllCompatibilityLines_unit vc (ZMod.unitOfCoprime e hqe.symm) S
      simp only [ZMod.coe_unitOfCoprime] at hl
      rw [hl, Finset.sum_comm]
    apply hb.trans
    simp_rw [hid]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left het (mul_nonneg (Nat.cast_nonneg _) hκ))
      (Finset.sum_nonneg (fun c _ => hF e c))
  calc
    _ ≤ ∑ e ∈ D, ρ e * ((w.divisors.card : ℝ) * κ * τ *
        ∑ c ∈ w.divisors.attach, F e c) :=
      Finset.sum_le_sum (fun e he => mul_le_mul_of_nonneg_left (hrow e he) (hρ e he))
    _ = _ := by
      simp only [incidenceOriginalProgressionEnergy, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [F]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro ζ _
      apply Finset.sum_congr rfl
      intro γ _
      ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePhysicalEnergyOrZero_of_ne
#print axioms PrimeGap182Audit.incidenceOriginalProgressionEnergy_nonneg
#print axioms PrimeGap182Audit.incidencePhysicalWeighted_masked_to_progression
