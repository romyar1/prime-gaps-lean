import IncidenceCRT

/-!
# Exact zero-mode bound for every squarefree modulus

The prime Gram estimate is transferred through actual CRT tensor products,
without a prime-counting loss. Modulus one retains its constant column.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix WithLp
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem primeIncidenceMatrix_norm_le {p : ℕ} [Fact p.Prime]
    (A : ZMod p) (hA : A ≠ 0) : ‖primeIncidenceMatrix A‖ ≤ (p : ℝ) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg p) fun x => ?_
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg p) (norm_nonneg x))).mp
  change ‖(toLp 2 (primeIncidenceMatrix A *ᵥ x) :
    EuclideanSpace ℂ (ZMod p × ZMod p))‖ ^ 2 ≤ _
  simpa only [EuclideanSpace.norm_sq_eq, mul_pow, incidenceVectorEnergy] using
    primeIncidenceVectorEnergy_le A hA x

theorem primeIncidenceMode_zero_norm_le {p : ℕ} [Fact p.Prime]
    (A : ZMod p) (hA : A ≠ 0) : ‖primeIncidenceMode A 0‖ ≤ (p : ℝ) ^ 2 := by
  rw [primeIncidenceMode_zero, primeIncidenceZeroMode, Matrix.l2_opNorm_conjTranspose_mul_self]
  simpa only [sq] using mul_le_mul
    (primeIncidenceMatrix_norm_le A hA) (primeIncidenceMatrix_norm_le A hA)
    (norm_nonneg _) (Nat.cast_nonneg p)

theorem incidenceModeMod_one (A : ZMod 1) (ξ : ZMod 1 × ZMod 1) :
    incidenceModeMod A ξ = 1 := by
  have hR : incidenceMatrixMod A = fun _ _ => (1 : ℂ) := by
    ext z b
    have hu : IsUnit (z.1 * (z.2 + z.1 * b)) := by
      rw [Subsingleton.elim (z.1 * (z.2 + z.1 * b)) 1]
      exact isUnit_one
    simp only [incidenceMatrixMod, ite_eq_left hu]
    rw [Subsingleton.elim (A * (z.1 * (z.2 + z.1 * b))⁻¹) 0, AddChar.map_zero_eq_one]
  rw [Subsingleton.elim ξ 0, incidenceModeMod, incidenceMode_zero, hR]
  ext b b'
  have hbb : b = b' := Subsingleton.elim _ _
  subst b'
  rw [Matrix.one_apply_eq]
  change (∑ _ : ZMod 1 × ZMod 1, star (1 : ℂ) * 1) = 1
  simp

/-- No factor depending on the number of primes is charged to the zero mode. -/
theorem incidenceModeMod_zero_norm_le {q : ℕ} [NeZero q] (hq : Squarefree q)
    (A : ZMod q) (hA : IsUnit A) : ‖incidenceModeMod A 0‖ ≤ (q : ℝ) ^ 2 := by
  have hmain : ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ A : ZMod q, IsUnit A → ‖incidenceModeMod A 0‖ ≤ (q : ℝ) ^ 2 := by
    refine induction_on_primes ?_ ?_ ?_
    · intro _
      exact False.elim (NeZero.ne 0 rfl)
    · intro _ _ A _
      rw [incidenceModeMod_one]
      simp
    · intro p n hp ih _ hpn A hA
      have hn : Squarefree n := hpn.of_mul_right
      let : NeZero n := ⟨hn.ne_zero⟩
      let : Fact p.Prime := ⟨hp⟩
      have hcop : p.Coprime n := Nat.coprime_of_squarefree_mul hpn
      have hleft := incidenceCRTScaledLeft_isUnit hcop A hA
      have hright := incidenceCRTScaledRight_isUnit hcop A hA
      have hcrt := incidenceModeMod_crt_norm_le hcop A 0
      simp only [Prod.fst_zero, Prod.snd_zero, incidenceCRTScaledLeft_zero,
        incidenceCRTScaledRight_zero] at hcrt
      have hl : ‖incidenceModeMod (incidenceCRTScaledLeft hcop A) 0‖ ≤ (p : ℝ) ^ 2 := by
        rw [incidenceModeMod_eq_prime]
        exact primeIncidenceMode_zero_norm_le _ hleft.ne_zero
      calc
        _ ≤ ‖incidenceModeMod (incidenceCRTScaledLeft hcop A) 0‖ *
          ‖incidenceModeMod (incidenceCRTScaledRight hcop A) 0‖ := hcrt
        _ ≤ (p : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
          mul_le_mul hl (ih hn _ hright) (norm_nonneg _) (sq_nonneg _)
        _ = _ := by push_cast; ring
  exact hmain q hq A hA

#print axioms primeIncidenceMatrix_norm_le
#print axioms primeIncidenceMode_zero_norm_le
#print axioms incidenceModeMod_one
#print axioms incidenceModeMod_zero_norm_le

end PrimeGap182Audit
