import TypeIIIOriginalCompletion

/-!
# The actual zero-frequency coefficient and its cubic gcd weight

The zero mode is handled by the exact elementary correlation formula. No Deligne input
is used, and the inverse row indices are explicitly cleared by units modulo the shared
modulus.
-/

open scoped BigOperators Classical FourierTransform ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem integer_gcd_eq_of_zmod_eq (w : ℕ) (z t : ℤ)
    (h : (z : ZMod w) = (t : ZMod w)) : Int.gcd z (w : ℤ) = Int.gcd t (w : ℤ) := by
  have he := (ZMod.intCast_eq_intCast_iff' z t w).mp h
  simpa only [Int.gcd_emod] using congrArg (fun k : ℤ => Int.gcd k (w : ℤ)) he

theorem integer_gcd_unit_mul (w : ℕ) (b z : ℤ) (hb : IsUnit (b : ZMod w)) :
    Int.gcd (b * z) (w : ℤ) = Int.gcd z (w : ℤ) := by
  have hb' : Int.gcd b (w : ℤ) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ((ZMod.coe_int_isUnit_iff_isCoprime b w).mp hb).symm
  exact Int.gcd_mul_right_left_of_gcd_eq_one hb'

/-- Clearing the actual inverse row indices leaves exactly the integer cubic difference. -/
theorem inverse_cubic_gcd (w u v : ℕ) (a m n A B : ℤ)
    (ha : IsUnit (a : ZMod w)) (hm : IsUnit (m : ZMod w)) (hn : IsUnit (n : ZMod w))
    (hA : (A : ZMod w) * (m : ZMod w) = (a : ZMod w))
    (hB : (B : ZMod w) * (n : ZMod w) = (a : ZMod w)) :
    Int.gcd (B * (u : ℤ) ^ 3 - A * (v : ℤ) ^ 3) (w : ℤ) =
      Int.gcd (m * (u : ℤ) ^ 3 - n * (v : ℤ) ^ 3) (w : ℤ) := by
  have hmn : IsUnit ((m * n : ℤ) : ZMod w) := by simpa only [Int.cast_mul] using hm.mul hn
  have he : (((m * n) * (B * (u : ℤ) ^ 3 - A * (v : ℤ) ^ 3) : ℤ) : ZMod w) =
      ((a * (m * (u : ℤ) ^ 3 - n * (v : ℤ) ^ 3) : ℤ) : ZMod w) := by
    push_cast
    calc
      _ = ((B : ZMod w) * (n : ZMod w)) * ((m : ZMod w) * (u : ZMod w) ^ 3) -
          ((A : ZMod w) * (m : ZMod w)) * ((n : ZMod w) * (v : ZMod w) ^ 3) := by ring
      _ = _ := by rw [hA, hB]; ring
  calc
    _ = Int.gcd ((m * n) * (B * (u : ℤ) ^ 3 - A * (v : ℤ) ^ 3)) (w : ℤ) :=
      (integer_gcd_unit_mul w (m * n) _ hmn).symm
    _ = Int.gcd (a * (m * (u : ℤ) ^ 3 - n * (v : ℤ) ^ 3)) (w : ℤ) :=
      integer_gcd_eq_of_zmod_eq w _ _ he
    _ = _ := integer_gcd_unit_mul w a _ ha

theorem sharedPairFourier_zero_norm_le (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (hu : Squarefree u) (hv : Squarefree v) (hw : Squarefree w)
    (huv : u.Coprime v) (huw : u.Coprime w) (hvw : v.Coprime w)
    (A B : ℤ) (hA : IsUnit (A : ZMod (u * w))) (hB : IsUnit (B : ZMod (v * w))) :
    ‖sharedPairFourier u v w A B 0‖ ≤
      (2 : ℝ) ^ w.primeFactors.card *
        (Int.gcd (B * (u : ℤ) ^ 3 - A * (v : ℤ) ^ 3) (w : ℤ) : ℝ) /
          ((u * v : ℕ) : ℝ) := by
  have hh := PrimeGap186.kloosterman3Mod_mixed_coprime_norm_le w u v hw hu hv huv huw hvw A B hA hB
  simp only [sharedPairFourier, Int.cast_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
  let F (k : ℕ+) : ℝ := ‖∑ h : (ZMod (k : ℕ))ˣ,
    PrimeGap186.normalizedKloosterman3Mod (u * w)
      ((A : ZMod (u * w)) * ((h : ZMod (k : ℕ)).val : ZMod (u * w))) *
      star (PrimeGap186.normalizedKloosterman3Mod (v * w)
        ((B : ZMod (v * w)) * ((h : ZMod (k : ℕ)).val : ZMod (v * w))))‖
  let k₁ : ℕ+ := ⟨u * (v * w), mul_pos (NeZero.pos u) (mul_pos (NeZero.pos v) (NeZero.pos w))⟩
  let k₂ : ℕ+ := ⟨(u * v) * w, mul_pos (mul_pos (NeZero.pos u) (NeZero.pos v)) (NeZero.pos w)⟩
  have he : k₁ = k₂ := Subtype.ext (Nat.mul_assoc u v w).symm
  change F k₁ ≤ _
  rw [he]
  exact hh

/-- The precise gcd weight used by the paper's zero-frequency summation. -/
theorem sharedInverseFourier_zero_norm_le (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (hu : Squarefree u) (hv : Squarefree v) (hw : Squarefree w)
    (huv : u.Coprime v) (huw : u.Coprime w) (hvw : v.Coprime w)
    (a m n : ℤ) (ha : IsUnit (a : ZMod (u * (v * w))))
    (hm : IsUnit (m : ZMod (u * w))) (hn : IsUnit (n : ZMod (v * w))) :
    ‖sharedInverseFourier u v w a m n 0‖ ≤
      (2 : ℝ) ^ w.primeFactors.card *
        (Int.gcd (m * (u : ℤ) ^ 3 - n * (v : ℤ) ^ 3) (w : ℤ) : ℝ) /
          ((u * v : ℕ) : ℝ) := by
  have hdu : u * w ∣ u * (v * w) := by refine ⟨v, ?_⟩; ring
  have hdv : v * w ∣ u * (v * w) := dvd_mul_left _ _
  have hau := PrimeGap186.isUnit_intCast_of_dvd (u * w) (u * (v * w)) hdu a ha
  have hav := PrimeGap186.isUnit_intCast_of_dvd (v * w) (u * (v * w)) hdv a ha
  have haw := PrimeGap186.isUnit_intCast_of_dvd w (u * w) (dvd_mul_left _ _) a hau
  have hmw := PrimeGap186.isUnit_intCast_of_dvd w (u * w) (dvd_mul_left _ _) m hm
  have hnw := PrimeGap186.isUnit_intCast_of_dvd w (v * w) (dvd_mul_left _ _) n hn
  let A : ℤ := (((a : ZMod (u * w)) * (m : ZMod (u * w))⁻¹).val : ℤ)
  let B : ℤ := (((a : ZMod (v * w)) * (n : ZMod (v * w))⁻¹).val : ℤ)
  have hA : IsUnit (A : ZMod (u * w)) := by
    simpa only [A, Int.cast_natCast, ZMod.natCast_zmod_val] using hau.mul (ZMod.isUnit_inv hm)
  have hB : IsUnit (B : ZMod (v * w)) := by
    simpa only [B, Int.cast_natCast, ZMod.natCast_zmod_val] using hav.mul (ZMod.isUnit_inv hn)
  have hAw : (A : ZMod w) * (m : ZMod w) = (a : ZMod w) := by
    rw [show (A : ZMod w) = (a : ZMod w) * (m : ZMod w)⁻¹ from
      inverse_index_val_reduce (u * w) w (dvd_mul_left _ _) a m hm]
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hmw, mul_one]
  have hBw : (B : ZMod w) * (n : ZMod w) = (a : ZMod w) := by
    rw [show (B : ZMod w) = (a : ZMod w) * (n : ZMod w)⁻¹ from
      inverse_index_val_reduce (v * w) w (dvd_mul_left _ _) a n hn]
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hnw, mul_one]
  have hg := inverse_cubic_gcd w u v a m n A B haw hmw hnw hAw hBw
  change ‖sharedPairFourier u v w A B 0‖ ≤ _
  exact (sharedPairFourier_zero_norm_le u v w hu hv hw huv huw hvw A B hA hB).trans_eq
    (by rw [hg])

/-- The central Poisson sample has the actual support/derivative bound. -/
theorem normalizedProfileFourier_zero_bound (q : ℕ) [NeZero q]
    (T L H t₀ : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hH : 0 < H)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) :
    ‖normalizedProfileFourier q ψ H t₀ 0‖ ≤ (8 * T) * L * H / (q : ℝ) := by
  have hh := PrimeGap186.compactProfile_fourier_decay_bound T L H t₀
    hT hL hH ψ hψ hsupport hbound 0
  simp only [abs_zero, mul_zero, add_zero, one_pow, div_one] at hh
  unfold normalizedProfileFourier
  rw [Int.cast_zero, zero_div, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * ((8 * T) * L * H) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- After the real outer factor s and the Poisson normalization, the exact paper weight
is H/g times gcd(sg,D)/(u²v²), up to the displayed profile and prime-count constants. -/
theorem zeroFrequency_central_weight (s g u v : ℕ) [NeZero s] [NeZero g]
    [NeZero u] [NeZero v]
    (hu : Squarefree u) (hv : Squarefree v) (hw : Squarefree (s * g))
    (huv : u.Coprime v) (huw : u.Coprime (s * g)) (hvw : v.Coprime (s * g))
    (a m n : ℤ) (ha : IsUnit (a : ZMod (u * (v * (s * g)))))
    (hm : IsUnit (m : ZMod (u * (s * g)))) (hn : IsUnit (n : ZMod (v * (s * g))))
    (T L H t₀ : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hH : 0 < H)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) :
    (s : ℝ) * ‖normalizedProfileFourier (u * (v * (s * g))) ψ H t₀ 0 *
      sharedInverseFourier u v (s * g) a m n 0‖ ≤
      ((8 * T) * L) * (H / (g : ℝ)) * (2 : ℝ) ^ (s * g).primeFactors.card *
        (Int.gcd (m * (u : ℤ) ^ 3 - n * (v : ℤ) ^ 3) ((s * g : ℕ) : ℤ) : ℝ) /
          ((u : ℝ) ^ 2 * (v : ℝ) ^ 2) := by
  have hf := normalizedProfileFourier_zero_bound (u * (v * (s * g))) T L H t₀
    hT hL hH ψ hψ hsupport hbound
  have hc := sharedInverseFourier_zero_norm_le u v (s * g) hu hv hw huv huw hvw a m n ha hm hn
  rw [norm_mul]
  calc
    _ ≤ (s : ℝ) * (((8 * T) * L * H / ((u * (v * (s * g)) : ℕ) : ℝ)) *
        ((2 : ℝ) ^ (s * g).primeFactors.card *
          (Int.gcd (m * (u : ℤ) ^ 3 - n * (v : ℤ) ^ 3) ((s * g : ℕ) : ℤ) : ℝ) /
            ((u * v : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hf hc (norm_nonneg _) (by positivity))
        (Nat.cast_nonneg s)
    _ = _ := by
      have hs : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne s)
      have hg : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
      have hu' : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne u)
      have hv' : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
      simp only [Nat.cast_mul]
      field_simp

#print axioms sharedPairFourier_zero_norm_le
#print axioms sharedInverseFourier_zero_norm_le
#print axioms zeroFrequency_central_weight

end

end PrimeGap182.TypeIII
