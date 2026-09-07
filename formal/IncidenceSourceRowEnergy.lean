import IncidenceReducedResponse

/-!
# Every original residue class in the source-energy reduction

Compatibility and frequency Möbius expansions are composed here for
the actual physical row. The residue sum is exactly 0 ≤ γ < e, including
zero; it is never replaced by γ modulo a proper divisor of e.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

theorem incidenceSumZMod_eq_Ico {M : Type*} [AddCommMonoid M]
    (e : ℕ) [NeZero e] (f : ZMod e → M) :
    (∑ γ : ZMod e, f γ) = ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ), f (γ : ZMod e) := by
  apply Finset.sum_bij (fun γ _ => (γ.val : ℤ))
  · intro γ _
    exact Finset.mem_Ico.mpr ⟨by positivity, by exact_mod_cast γ.val_lt⟩
  · intro γ _ γ' _ h
    have heq := congrArg (fun n : ℤ => (n : ZMod e)) h
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using heq
  · intro γ hγ
    refine ⟨(γ : ZMod e), Finset.mem_univ _, ?_⟩
    exact (ZMod.val_intCast γ).trans (Int.emod_eq_of_lt
      (Finset.mem_Ico.mp hγ).1 (Finset.mem_Ico.mp hγ).2)
  · intro γ _
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem incidenceSourceRow_compatibility_sector_energy
    {m e q₀ : ℕ} [NeZero m] [NeZero e] [NeZero q₀]
    (hqe : Nat.Coprime q₀ e) (w₂ : ℕ) (hwe : Nat.Coprime w₂ e)
    (c : (ZMod q₀)ˣ) (S : Finset (ZMod q₀)) (κ : ℝ) (hκ : (S.card : ℝ) ≤ κ)
    (A : ZMod m) (B : ℤ) (Λ I : Finset ℤ)
    (hΛ : ∀ l ∈ Λ, (w₂ : ℤ) ∣ l)
    (a χ : ℤ → ℂ) (hχ : ∀ n, χ n ≠ 0 → n ∈ I) :
    (∑ γ : ZMod e, ‖incidenceUnmaskedPhysicalRow A B Λ I a
      (fun n => if (c : ZMod q₀) * (n : ZMod q₀) ∈ S then χ n else 0) γ‖ ^ 2) ≤
      κ * (e.divisors.card : ℝ) *
        ∑ ζ ∈ incidenceCompatibilityLines c (ZMod.unitOfCoprime e hqe.symm) S,
          ∑ t ∈ e.divisors, ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ),
            ‖∑ b ∈ incidenceDividedCoefficientSet Λ (t * w₂),
              a (((t * w₂ : ℕ) : ℤ) * b) *
                incidenceProgressionResponse A B q₀ e (ζ.val : ℤ) γ χ
                  (((t * w₂ : ℕ) : ℤ) * b)‖ ^ 2 := by
  let e₀ : (ZMod q₀)ˣ := ZMod.unitOfCoprime e hqe.symm
  let T := incidenceCompatibilityLines c e₀ S
  let line : ZMod q₀ → ZMod e → ℂ := fun ζ γ =>
    incidenceUnmaskedPhysicalRow A B Λ I a
      (fun n => if (n : ZMod q₀) = ζ * (e₀ : ZMod q₀) then χ n else 0) γ
  have hκ0 : 0 ≤ κ := (Nat.cast_nonneg S.card).trans hκ
  have hfirst : (∑ γ : ZMod e, ‖incidenceUnmaskedPhysicalRow A B Λ I a
      (fun n => if (c : ZMod q₀) * (n : ZMod q₀) ∈ S then χ n else 0) γ‖ ^ 2) ≤
      κ * ∑ ζ ∈ T, ∑ γ : ZMod e, ‖line ζ γ‖ ^ 2 := by
    calc
      _ ≤ ∑ γ : ZMod e, κ * ∑ ζ ∈ T, ‖line ζ γ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro γ _
        exact incidenceUnmaskedPhysicalRow_compatibility_bound c e₀ S κ hκ
          A B Λ I a χ γ
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  apply hfirst.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hκ0
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ζ _
  let uq : (ZMod e)ˣ := ZMod.unitOfCoprime q₀ hqe
  have hperm := (incidenceInputUnitEquiv uq).sum_comp (fun γ => ‖line ζ γ‖ ^ 2)
  rw [← hperm]
  change (∑ γ : ZMod e, ‖line ζ ((q₀ : ZMod e) * γ)‖ ^ 2) ≤ _
  rw [incidenceSumZMod_eq_Ico]
  calc
    _ ≤ ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ), (e.divisors.card : ℝ) *
        ∑ t ∈ e.divisors,
          ‖∑ b ∈ incidenceDividedCoefficientSet Λ (t * w₂),
            a (((t * w₂ : ℕ) : ℤ) * b) *
              incidenceProgressionResponse A B q₀ e (ζ.val : ℤ) γ χ
                (((t * w₂ : ℕ) : ℤ) * b)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro γ _
      have hh := incidenceUnmaskedPhysicalRow_sector_energy hqe w₂ hwe
        A B (ζ.val : ℤ) γ Λ I hΛ a χ hχ
      simpa only [line, e₀, ZMod.coe_unitOfCoprime, Int.cast_natCast,
        ZMod.natCast_zmod_val] using hh
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSumZMod_eq_Ico
#print axioms PrimeGap182Audit.incidenceSourceRow_compatibility_sector_energy
