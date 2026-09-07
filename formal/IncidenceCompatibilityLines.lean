import IncidenceMobiusMasks

/-!
# Exact compatibility-line extraction

On a fixed unit row residue, multiplication by the divisor and row
residue permutes the compatibility set. The number of permitted lines
does not increase, and their positive energy bound follows from the
exact disjoint line expansion.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

variable {q : ℕ} [NeZero q]

def incidenceCompatibilityLines (c e : (ZMod q)ˣ) (S : Finset (ZMod q)) : Finset (ZMod q) :=
  Finset.univ.filter (fun ζ => (c : ZMod q) * (ζ * (e : ZMod q)) ∈ S)

theorem incidenceCompatibilityLines_card (c e : (ZMod q)ˣ) (S : Finset (ZMod q)) :
    (incidenceCompatibilityLines c e S).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn (fun ζ => (c : ZMod q) * (ζ * (e : ZMod q)))
  · intro ζ hζ
    exact (Finset.mem_filter.mp hζ).2
  · intro ζ _ ξ _ h
    have h' : ζ * (e : ZMod q) = ξ * (e : ZMod q) :=
      (incidenceInputUnitEquiv c).injective h
    apply (incidenceInputUnitEquiv e).injective
    change (e : ZMod q) * ζ = (e : ZMod q) * ξ
    simpa only [mul_comm] using h'

theorem incidenceCompatibilityLines_isUnit (c e : (ZMod q)ˣ) (S : Finset (ZMod q))
    (hS : ∀ n ∈ S, IsUnit n) (ζ : ZMod q) (hζ : ζ ∈ incidenceCompatibilityLines c e S) :
    IsUnit ζ := by
  have h := hS _ (Finset.mem_filter.mp hζ).2
  simpa only [IsUnit.mul_iff, c.isUnit, e.isUnit, true_and, and_true] using h

theorem incidenceCompatibilityLines_sum (c e : (ZMod q)ˣ) (S : Finset (ZMod q))
    (n : ZMod q) (z : ℂ) :
    (∑ ζ ∈ incidenceCompatibilityLines c e S, if n = ζ * (e : ZMod q) then z else 0) =
      if (c : ZMod q) * n ∈ S then z else 0 := by
  have heq (ζ : ZMod q) : n = ζ * (e : ZMod q) ↔
      ζ = n * ((e⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    constructor
    · intro h
      have h' := congrArg (fun v : ZMod q => v * ((e⁻¹ : (ZMod q)ˣ) : ZMod q)) h
      simpa only [mul_assoc, Units.mul_inv, mul_one] using h'.symm
    · intro h
      rw [h, mul_assoc, Units.inv_mul, mul_one]
  simp only [heq]
  simp [incidenceCompatibilityLines, mul_assoc]

theorem incidenceCompatibility_mask_sum (c e : (ZMod q)ˣ) (S : Finset (ZMod q))
    (I : Finset ℤ) (f : ℤ → ℂ) :
    (∑ n ∈ I, if (c : ZMod q) * (n : ZMod q) ∈ S then f n else 0) =
      ∑ ζ ∈ incidenceCompatibilityLines c e S,
        ∑ n ∈ I, if (n : ZMod q) = ζ * (e : ZMod q) then f n else 0 := by
  simp_rw [← incidenceCompatibilityLines_sum c e S]
  rw [Finset.sum_comm]

theorem incidenceCompatibility_mask_energy (c e : (ZMod q)ˣ) (S : Finset (ZMod q))
    (I : Finset ℤ) (f : ℤ → ℂ) (κ : ℝ) (hκ : (S.card : ℝ) ≤ κ) :
    ‖∑ n ∈ I, if (c : ZMod q) * (n : ZMod q) ∈ S then f n else 0‖ ^ 2 ≤
      κ * ∑ ζ ∈ incidenceCompatibilityLines c e S,
        ‖∑ n ∈ I, if (n : ZMod q) = ζ * (e : ZMod q) then f n else 0‖ ^ 2 := by
  rw [incidenceCompatibility_mask_sum]
  exact (incidenceNormSum_sq_le _ _).trans (mul_le_mul_of_nonneg_right
    ((Nat.cast_le.mpr (incidenceCompatibilityLines_card c e S)).trans hκ)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Exact progression reindexing; it includes the zero modulus case. -/
theorem incidenceProgression_sum_reindex (m b : ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ n ∈ S, if Int.ModEq m b n then f n else 0) =
      ∑ k ∈ (S.filter (fun n => Int.ModEq m b n)).image (fun n => (n - b) / m),
        f (b + m * k) := by
  have hid (n : ℤ) (hn : Int.ModEq m b n) : b + m * ((n - b) / m) = n := by
    rw [Int.mul_ediv_cancel' (Int.modEq_iff_dvd.mp hn)]
    ring
  rw [← Finset.sum_filter, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [hid n (Finset.mem_filter.mp hn).2]
  · intro a ha d hd had
    exact (hid a (Finset.mem_filter.mp ha).2).symm.trans
      ((congrArg (fun k : ℤ => b + m * k) had).trans (hid d (Finset.mem_filter.mp hd).2))

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceCompatibilityLines_card
#print axioms PrimeGap182Audit.incidenceCompatibilityLines_isUnit
#print axioms PrimeGap182Audit.incidenceCompatibilityLines_sum
#print axioms PrimeGap182Audit.incidenceCompatibility_mask_sum
#print axioms PrimeGap182Audit.incidenceCompatibility_mask_energy
#print axioms PrimeGap182Audit.incidenceProgression_sum_reindex
