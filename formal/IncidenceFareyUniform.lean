import IncidenceFarey

/-!
# Polynomial-height Farey bound with an actual subpower divisor loss

The local divisor-factor premise is discharged using the baseline's
elementary divisor bound. All constants are uniform in the arbitrary
centers of the numerator intervals and in the coefficient arrays.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

theorem incidenceFarey_uniform_bound (η D : ℝ) (hη : 0 < η) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ q : ℕ, ∀ [NeZero q],
      ∀ A : Finset ℤ, ∀ I : ℤ → Finset ℤ, ∀ B : ℤ,
      ∀ U V : ℝ, 0 < U → 0 ≤ V →
      (∀ a ∈ A, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U ∧ IsUnit (a : ZMod q)) →
      (∀ a ∈ A, (a.natAbs : ℝ) ≤ x ^ D) →
      ∀ center : ℤ → ℝ,
      (∀ a ∈ A, ∀ k ∈ I a, |(k : ℝ) - center a| ≤ V) →
      ∀ c : ℤ → ℂ, ∀ β : ℤ → ℤ → ℂ,
      (∀ a ∈ A, ∀ k ∈ I a, ‖β a k‖ ≤ 1) →
      incidenceVectorEnergy (incidenceFareyCoefficients (q := q) A I B c β) ≤
        C * x ^ η * (1 + U * V / (q : ℝ)) * (V + (A.card : ℝ)) *
          ∑ a ∈ A, ‖c a‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hdiv⟩ := PrimeGap186.exists_card_divisors_bound (div_pos hη hD)
  refine ⟨8 * (1 + 8 * C₀), by positivity, ?_⟩
  intro x hx q _ A I B U V hU hV hA hheight center hI c β hβ
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxη : 1 ≤ x ^ η := Real.one_le_rpow hx hη.le
  have hτ (a : ℤ) (ha : a ∈ A) : (a.natAbs.divisors.card : ℝ) ≤ C₀ * x ^ η := by
    have hane : a ≠ 0 := by
      intro hz
      have h := (hA a ha).1
      simp only [hz, Int.cast_zero, abs_zero] at h
      exact hU.not_ge h
    calc
      _ ≤ C₀ * (a.natAbs : ℝ) ^ (η / D) := hdiv a.natAbs (Int.natAbs_ne_zero.mpr hane)
      _ ≤ C₀ * (x ^ D) ^ (η / D) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hheight a ha) (div_pos hη hD).le) hC₀.le
      _ = C₀ * x ^ η := by
        rw [← Real.rpow_mul hx0.le, mul_div_cancel₀ η hD.ne']
  have hb := incidenceFarey_energy_le A I B U V (C₀ * x ^ η)
    hU hV hA hτ center hI c β hβ
  have hsize : (A.card : ℝ) + 8 * V * (C₀ * x ^ η) ≤
      (1 + 8 * C₀) * x ^ η * (V + (A.card : ℝ)) := by
    calc
      _ ≤ x ^ η * (A.card : ℝ) + 8 * V * (C₀ * x ^ η) :=
        add_le_add (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hxη (Nat.cast_nonneg A.card)) le_rfl
      _ = x ^ η * ((A.card : ℝ) + 8 * C₀ * V) := by ring
      _ ≤ x ^ η * ((1 + 8 * C₀) * (V + (A.card : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg hC₀.le (Nat.cast_nonneg A.card)]
      _ = _ := by ring
  have hscale : 1 + 8 * U * V / (q : ℝ) ≤ 8 * (1 + U * V / (q : ℝ)) := by
    have he : 1 + 8 * U * V / (q : ℝ) = 8 * (1 + U * V / (q : ℝ)) - 7 := by ring
    rw [he]
    linarith
  calc
    _ ≤ (1 + 8 * U * V / (q : ℝ)) * ((A.card : ℝ) + 8 * V * (C₀ * x ^ η)) *
        ∑ a ∈ A, ‖c a‖ ^ 2 := hb
    _ ≤ (8 * (1 + U * V / (q : ℝ))) *
        ((1 + 8 * C₀) * x ^ η * (V + (A.card : ℝ))) * ∑ a ∈ A, ‖c a‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul hscale hsize (by positivity) (by positivity)
    _ = _ := by ring

#print axioms incidenceFarey_uniform_bound

end PrimeGap182Audit
