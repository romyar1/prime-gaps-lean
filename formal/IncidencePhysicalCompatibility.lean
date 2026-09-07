import IncidencePhysicalDivisors

/-!
# Compatibility lines and the literal two-modulus source lattice

These identities keep the full finite source sum. The residue change
uses q₀ as a unit modulo e, and gives n=ζe+q₀(γλ+ek) without replacing
the γ-domain by a smaller residue ring.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

theorem incidenceUnmaskedPhysicalRow_sum {ι : Type*} {m e : ℕ} [NeZero m] [NeZero e]
    (F : Finset ι) (A : ZMod m) (B : ℤ) (Λ I : Finset ℤ)
    (a : ℤ → ℂ) (χ : ι → ℤ → ℂ) (γ : ZMod e) :
    incidenceUnmaskedPhysicalRow A B Λ I a (fun n => ∑ j ∈ F, χ j n) γ =
      ∑ j ∈ F, incidenceUnmaskedPhysicalRow A B Λ I a (χ j) γ := by
  unfold incidenceUnmaskedPhysicalRow
  simp only [Finset.sum_mul, Finset.ite_sum_zero, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := I) (t := F)]
  rw [Finset.sum_comm]

theorem incidenceUnmaskedPhysicalRow_compatibility
    {m e q₀ : ℕ} [NeZero m] [NeZero e] [NeZero q₀]
    (c e₀ : (ZMod q₀)ˣ) (S : Finset (ZMod q₀))
    (A : ZMod m) (B : ℤ) (Λ I : Finset ℤ) (a χ : ℤ → ℂ) (γ : ZMod e) :
    incidenceUnmaskedPhysicalRow A B Λ I a
        (fun n => if (c : ZMod q₀) * (n : ZMod q₀) ∈ S then χ n else 0) γ =
      ∑ ζ ∈ incidenceCompatibilityLines c e₀ S,
        incidenceUnmaskedPhysicalRow A B Λ I a
          (fun n => if (n : ZMod q₀) = ζ * (e₀ : ZMod q₀) then χ n else 0) γ := by
  rw [← incidenceUnmaskedPhysicalRow_sum]
  congr 1
  funext n
  exact (incidenceCompatibilityLines_sum c e₀ S (n : ZMod q₀) (χ n)).symm

theorem incidenceUnmaskedPhysicalRow_compatibility_bound
    {m e q₀ : ℕ} [NeZero m] [NeZero e] [NeZero q₀]
    (c e₀ : (ZMod q₀)ˣ) (S : Finset (ZMod q₀)) (κ : ℝ) (hκ : (S.card : ℝ) ≤ κ)
    (A : ZMod m) (B : ℤ) (Λ I : Finset ℤ) (a χ : ℤ → ℂ) (γ : ZMod e) :
    ‖incidenceUnmaskedPhysicalRow A B Λ I a
        (fun n => if (c : ZMod q₀) * (n : ZMod q₀) ∈ S then χ n else 0) γ‖ ^ 2 ≤
      κ * ∑ ζ ∈ incidenceCompatibilityLines c e₀ S,
        ‖incidenceUnmaskedPhysicalRow A B Λ I a
          (fun n => if (n : ZMod q₀) = ζ * (e₀ : ZMod q₀) then χ n else 0) γ‖ ^ 2 := by
  rw [incidenceUnmaskedPhysicalRow_compatibility]
  exact (incidenceNormSum_sq_le _ _).trans (mul_le_mul_of_nonneg_right
    ((Nat.cast_le.mpr (incidenceCompatibilityLines_card c e₀ S)).trans hκ)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem incidenceTwoModulusCongruence (q₀ e : ℕ) (hqe : Nat.Coprime q₀ e)
    (ζ γ l n : ℤ) :
    ((n : ZMod q₀) = (ζ : ZMod q₀) * (e : ZMod q₀) ∧
      (n : ZMod e) = (q₀ : ZMod e) * (γ : ZMod e) * (l : ZMod e)) ↔
      Int.ModEq ((q₀ * e : ℕ) : ℤ)
        (ζ * (e : ℤ) + (q₀ : ℤ) * γ * l) n := by
  let b : ℤ := ζ * (e : ℤ) + (q₀ : ℤ) * γ * l
  have hcop : IsCoprime (q₀ : ℤ) (e : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hqe.gcd_eq_one
  have hcrt : (Int.ModEq (q₀ : ℤ) b n ∧ Int.ModEq (e : ℤ) b n) ↔
      Int.ModEq ((q₀ * e : ℕ) : ℤ) b n := by
    simp only [Int.modEq_iff_dvd, Nat.cast_mul]
    constructor
    · rintro ⟨hq, he⟩
      exact hcop.mul_dvd hq he
    · intro h
      exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩
  have hcast : ((b : ZMod q₀) = (n : ZMod q₀) ∧
      (b : ZMod e) = (n : ZMod e)) ↔ Int.ModEq ((q₀ * e : ℕ) : ℤ) b n := by
    simpa only [ZMod.intCast_eq_intCast_iff] using hcrt
  simpa only [b, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, mul_zero, zero_add, add_zero, eq_comm] using hcast

theorem incidenceTwoModulus_sum_reindex (q₀ e : ℕ) (hqe : Nat.Coprime q₀ e)
    (ζ γ l : ℤ) (I : Finset ℤ) (f : ℤ → ℂ) :
    (∑ n ∈ I, if (n : ZMod q₀) = (ζ : ZMod q₀) * (e : ZMod q₀) ∧
        (n : ZMod e) = (q₀ : ZMod e) * (γ : ZMod e) * (l : ZMod e) then f n else 0) =
      ∑ k ∈ (I.filter (fun n => Int.ModEq ((q₀ * e : ℕ) : ℤ)
        (ζ * (e : ℤ) + (q₀ : ℤ) * γ * l) n)).image
          (fun n => (n - (ζ * (e : ℤ) + (q₀ : ℤ) * γ * l)) / ((q₀ * e : ℕ) : ℤ)),
        f (ζ * (e : ℤ) + (q₀ : ℤ) * (γ * l + (e : ℤ) * k)) := by
  simp only [incidenceTwoModulusCongruence q₀ e hqe]
  rw [incidenceProgression_sum_reindex]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  push_cast
  ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceUnmaskedPhysicalRow_sum
#print axioms PrimeGap182Audit.incidenceUnmaskedPhysicalRow_compatibility
#print axioms PrimeGap182Audit.incidenceUnmaskedPhysicalRow_compatibility_bound
#print axioms PrimeGap182Audit.incidenceTwoModulusCongruence
#print axioms PrimeGap182Audit.incidenceTwoModulus_sum_reindex
