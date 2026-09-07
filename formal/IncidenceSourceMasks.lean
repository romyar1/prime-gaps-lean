import IncidenceBaselineEnergy
import IncidenceCompatibilityLines

/-!
# Absorbing the original source masks into the actual reciprocal phase

The CRT values of B are used explicitly. Compatibility supplies the
additional q₀ pole restriction. Consequently the original numerator
weight can be replaced by its compatibility and smooth factors only
while it multiplies the zero-extended reciprocal phase.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

theorem incidenceIntegerUnit_of_dvd {m q : ℕ} (hqm : q ∣ m) (n : ℤ)
    (hn : IsUnit (n : ZMod m)) : IsUnit (n : ZMod q) := by
  rw [incidenceIntegerUnit_iff] at hn ⊢
  exact hn.of_dvd_right hqm

theorem incidenceIntegerCast_zero_of_dvd {m q : ℕ} (hqm : q ∣ m) (n : ℤ)
    (hn : (n : ZMod m) = 0) : (n : ZMod q) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hn ⊢
  exact (show (q : ℤ) ∣ (m : ℤ) by exact_mod_cast hqm).trans hn

theorem incidenceCompatibility_source_units
    (r₁ q₀ b₁ b₂ d : ℕ) (ℓ : ℤ)
    (E : ZMod q₀ → Finset (ZMod q₀))
    (hE : ∀ n : ℤ, PrimeGap186.sourceCompatibility (d * r₁) q₀ b₁ b₂ ℓ n =
      if (n : ZMod q₀) ∈ E (d : ZMod q₀) then 1 else 0)
    (n : ℤ) (hn : (n : ZMod q₀) ∈ E (d : ZMod q₀)) :
    IsUnit (n : ZMod q₀) ∧ IsUnit ((n + ℓ * (d : ℤ) * (r₁ : ℤ) : ℤ) : ZMod q₀) := by
  have hC : PrimeGap186.sourceCompatibility (d * r₁) q₀ b₁ b₂ ℓ n ≠ 0 := by
    rw [hE, ite_eq_left hn]
    norm_num
  have hg : Int.gcd (n * (n + ℓ * ((d * r₁ : ℕ) : ℤ))) (q₀ : ℤ) = 1 := by
    by_contra hh
    apply hC
    unfold PrimeGap186.sourceCompatibility
    split_ifs with h
    · exact False.elim (hh (by simpa only [Nat.cast_mul] using h.1))
    · rfl
  have hu : IsUnit ((n * (n + ℓ * ((d * r₁ : ℕ) : ℤ)) : ℤ) : ZMod q₀) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hg).symm
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Nat.cast_mul,
    IsUnit.mul_iff, mul_assoc] using hu

set_option maxHeartbeats 800000 in
theorem incidenceSourceNumerator_absorb_phase
    (r₁ q₀ u₁ v₁ v₂ q₂ d e b₁ b₂ : ℕ) (B ℓ : ℤ)
    (E : ZMod q₀ → Finset (ZMod q₀)) (ψN : ℝ → ℝ) (N : ℝ)
    (hBr : (B : ZMod r₁) = 0)
    (hBW : (B : ZMod (q₀ * u₁ * Nat.lcm v₁ v₂)) = 0)
    (hBq : (B : ZMod q₂) = ((ℓ * (r₁ : ℤ) : ℤ) : ZMod q₂))
    (hE : ∀ n : ℤ, PrimeGap186.sourceCompatibility (d * r₁) q₀ b₁ b₂ ℓ n =
      if (n : ZMod q₀) ∈ E (d : ZMod q₀) then 1 else 0)
    [NeZero (r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂)]
    (AA : ZMod (r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂)) (n : ℤ) :
    incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ d ℓ E ψN N n *
        PrimeGap186.reciprocalUnitPhase _ AA
          ((e : ZMod _) * ((n : ZMod _) + (B : ZMod _) * (d : ZMod _))) =
      (if (n : ZMod q₀) ∈ E (d : ZMod q₀) then (ψN ((n : ℝ) / N) : ℂ) else 0) *
        PrimeGap186.reciprocalUnitPhase _ AA
          ((e : ZMod _) * ((n : ZMod _) + (B : ZMod _) * (d : ZMod _))) := by
  let m := r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂
  let W := q₀ * u₁ * Nat.lcm v₁ v₂
  let phase := PrimeGap186.reciprocalUnitPhase m AA
    ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * (d : ZMod m)))
  change incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ d ℓ E ψN N n * phase = _ * phase
  by_cases hp : phase = 0
  · simp only [hp, mul_zero]
  have hpole : IsUnit (((n + B * (d : ℤ) : ℤ) : ZMod m)) := by
    have hh : IsUnit ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * (d : ZMod m))) := by
      by_contra hh
      exact hp (by simp only [phase, PrimeGap186.reciprocalUnitPhase, ite_eq_right hh])
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using (IsUnit.mul_iff.mp hh).2
  have hrm : r₁ ∣ m := ⟨q₀ * u₁ * Nat.lcm v₁ v₂ * q₂, by dsimp only [m]; ring⟩
  have hWm : W ∣ m := ⟨r₁ * q₂, by dsimp only [m, W]; ring⟩
  have hqm : q₂ ∣ m := dvd_mul_left _ _
  have hnr : IsUnit (n : ZMod r₁) := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hBr, zero_mul, add_zero]
      using incidenceIntegerUnit_of_dvd hrm (n + B * (d : ℤ)) hpole
  have hnW : IsUnit (n : ZMod W) := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hBW, zero_mul, add_zero]
      using incidenceIntegerUnit_of_dvd hWm (n + B * (d : ℤ)) hpole
  have hnq₂ : IsUnit ((n + ℓ * (d : ℤ) * (r₁ : ℤ) : ℤ) : ZMod q₂) := by
    have hh := incidenceIntegerUnit_of_dvd hqm (n + B * (d : ℤ)) hpole
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hBq,
      mul_assoc, mul_comm, mul_left_comm] using hh
  have hnq : IsUnit (n : ZMod q₀) :=
    incidenceIntegerUnit_of_dvd (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) n hnW
  have hnu : IsUnit (n : ZMod u₁) :=
    incidenceIntegerUnit_of_dvd (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) n hnW
  have hnv₁ : IsUnit (n : ZMod v₁) :=
    incidenceIntegerUnit_of_dvd ((Nat.dvd_lcm_left v₁ v₂).trans (dvd_mul_left _ _)) n hnW
  have hnv₂ : IsUnit (n : ZMod v₂) :=
    incidenceIntegerUnit_of_dvd ((Nat.dvd_lcm_right v₁ v₂).trans (dvd_mul_left _ _)) n hnW
  by_cases hnE : (n : ZMod q₀) ∈ E (d : ZMod q₀)
  · have hshift := (incidenceCompatibility_source_units r₁ q₀ b₁ b₂ d ℓ E hE n hnE).2
    have hmask : Int.gcd n ((r₁ * q₀ * u₁ * v₁ * v₂ : ℕ) : ℤ) = 1 ∧
        Int.gcd (n + ℓ * (d : ℤ) * (r₁ : ℤ)) ((q₀ * q₂ : ℕ) : ℤ) = 1 := by
      have hunit (q : ℕ) (a : ℤ) (h : IsUnit (a : ZMod q)) : IsCoprime a (q : ℤ) :=
        (ZMod.coe_int_isUnit_iff_isCoprime a q).mp h |>.symm
      simp only [← Int.isCoprime_iff_gcd_eq_one, Nat.cast_mul, IsCoprime.mul_right_iff]
      constructor
      · exact ⟨⟨⟨⟨hunit _ _ hnr, hunit _ _ hnq⟩, hunit _ _ hnu⟩,
          hunit _ _ hnv₁⟩, hunit _ _ hnv₂⟩
      · exact ⟨hunit _ _ hshift, hunit _ _ hnq₂⟩
    simp only [incidenceSourceNumerator, ite_eq_left hmask, ite_eq_left hnE, one_mul]
  · simp only [incidenceSourceNumerator, ite_eq_right hnE, zero_mul, ite_self]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceIntegerUnit_of_dvd
#print axioms PrimeGap182Audit.incidenceIntegerCast_zero_of_dvd
#print axioms PrimeGap182Audit.incidenceCompatibility_source_units
#print axioms PrimeGap182Audit.incidenceSourceNumerator_absorb_phase
