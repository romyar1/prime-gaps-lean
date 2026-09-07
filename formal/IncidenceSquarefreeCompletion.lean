import IncidenceSquarefree

/-!
# Squarefree modes and sharp weighted completion

The uniform prime-count loss is derived from the existing elementary
subpower bound. The actual zero mode retains constant one in Loewner order
and in every nonnegative finite weighted energy estimate.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

theorem incidenceVectorEnergy_le_gram_norm (R : Matrix ρ ι ℂ) (C : ℝ)
    (hR : ‖Rᴴ * R‖ ≤ C) (c : ι → ℂ) :
    incidenceVectorEnergy (R *ᵥ c) ≤ C * incidenceVectorEnergy c := by
  have hgram : star c ⬝ᵥ ((Rᴴ * R) *ᵥ c) =
      (incidenceVectorEnergy (R *ᵥ c) : ℂ) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose,
      star_star, incidenceVectorEnergy_cast]
  have henergy : 0 ≤ incidenceVectorEnergy (R *ᵥ c) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ = ‖star c ⬝ᵥ ((Rᴴ * R) *ᵥ c)‖ := by
      rw [hgram, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy]
    _ ≤ ‖Rᴴ * R‖ * incidenceVectorEnergy c := incidence_quadratic_norm_le _ _
    _ ≤ C * incidenceVectorEnergy c := mul_le_mul_of_nonneg_right hR
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem incidence_gram_le_of_norm (R : Matrix ρ ι ℂ) (C : ℝ)
    (hR : ‖Rᴴ * R‖ ≤ C) :
    ((C : ℂ) • (1 : Matrix ι ι ℂ) - Rᴴ * R).PosSemidef := by
  have hHerm : ((C : ℂ) • (1 : Matrix ι ι ℂ) - Rᴴ * R).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro c
  have hgram : star c ⬝ᵥ ((Rᴴ * R) *ᵥ c) =
      (incidenceVectorEnergy (R *ᵥ c) : ℂ) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose,
      star_star, incidenceVectorEnergy_cast]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hgram, incidenceVectorEnergy_cast]
  rw [Complex.nonneg_iff]
  constructor
  · simpa only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re,
      sub_nonneg] using incidenceVectorEnergy_le_gram_norm R C hR c
  · simp

theorem incidenceModeMod_zero_posSemidef {q : ℕ} [NeZero q] (A : ZMod q) :
    (incidenceModeMod A 0).PosSemidef := by
  rw [incidenceModeMod, incidenceMode_zero]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The exact squarefree zero-frequency Loewner upper bound. -/
theorem incidenceModeMod_zero_le {q : ℕ} [NeZero q] (hq : Squarefree q)
    (A : ZMod q) (hA : IsUnit A) :
    (((q : ℂ) ^ 2) • (1 : Matrix (ZMod q) (ZMod q) ℂ) -
      incidenceModeMod A 0).PosSemidef := by
  have hn := incidenceModeMod_zero_norm_le hq A hA
  rw [incidenceModeMod, incidenceMode_zero] at hn ⊢
  simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using
    incidence_gram_le_of_norm (incidenceMatrixMod A) ((q : ℝ) ^ 2) hn

/-- The frequency gcd on actual residue classes, including the zero frequency. -/
def incidenceFrequencyGCD {q : ℕ} (ξ : ZMod q × ZMod q) : ℕ :=
  Nat.gcd q (Nat.gcd ξ.1.val ξ.2.val)

set_option maxHeartbeats 600000 in
theorem incidenceModeMod_squarefree_norm_le_residue (hK4 : AllIncidenceRankFourBounds)
    {q : ℕ} [NeZero q] (hq : Squarefree q) (A : ZMod q) (hA : IsUnit A)
    (ξ : ZMod q × ZMod q) :
    ‖incidenceModeMod A ξ‖ ≤
      (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
        Real.sqrt (incidenceFrequencyGCD ξ : ℝ) := by
  have hb := incidenceModeMod_squarefree_norm_le hK4 hq A hA
    (ξ.1.val : ℤ) (ξ.2.val : ℤ)
  have hfst : ((ξ.1.val : ℤ) : ZMod q) = ξ.1 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val ξ.1
  have hsnd : ((ξ.2.val : ℤ) : ZMod q) = ξ.2 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val ξ.2
  rw [hfst, hsnd] at hb
  simpa only [Int.gcd_def, Int.natAbs_natCast, incidenceFrequencyGCD, Prod.mk.eta] using hb

/-- The manuscript's uniform squarefree mode bound with its precise gcd factor. -/
theorem incidenceModeMod_uniform_norm_le (hK4 : AllIncidenceRankFourBounds)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], Squarefree q →
      ∀ A : ZMod q, IsUnit A → ∀ h ν : ℤ,
      ‖incidenceModeMod A ((h : ZMod q), (ν : ZMod q))‖ ≤
        C * (q : ℝ) ^ ((3 : ℝ) / 2 + η) * Real.sqrt (Nat.gcd q (Int.gcd h ν) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := PrimeGap186.exists_primeFactors_power_bound
    (by norm_num : (1 : ℝ) ≤ 8) hη
  refine ⟨C, hC, ?_⟩
  intro q _ hq A hA h ν
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hbase : (q : ℝ) ^ η * (q : ℝ) * Real.sqrt (q : ℝ) =
      (q : ℝ) ^ ((3 : ℝ) / 2 + η) := by
    calc
      _ = (q : ℝ) ^ η * (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = _ := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 1
        ring
  calc
    _ ≤ (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
        Real.sqrt (Nat.gcd q (Int.gcd h ν) : ℝ) :=
      incidenceModeMod_squarefree_norm_le hK4 hq A hA h ν
    _ ≤ (C * (q : ℝ) ^ η) * (q : ℝ) * Real.sqrt (q : ℝ) *
        Real.sqrt (Nat.gcd q (Int.gcd h ν) : ℝ) := by
      gcongr
      exact hbound q (NeZero.ne q)
    _ = _ := by rw [mul_assoc C, mul_assoc C, hbase]

/-- Constant-one mean plus the actual nonzero Fourier modes, for every
nonnegative finite weight on the complete squarefree row set. -/
theorem incidenceRowEnergy_squarefree_le (hK4 : AllIncidenceRankFourBounds)
    {q : ℕ} [NeZero q] (hq : Squarefree q) (A : ZMod q) (hA : IsUnit A)
    (W : ZMod q × ZMod q → ℝ) (hW : ∀ z, 0 ≤ W z) (c : ZMod q → ℂ) :
    incidenceRowEnergy (incidenceMatrixMod A) W c ≤
      ((∑ z, W z) + ((q : ℝ) ^ 2)⁻¹ *
        ∑ ξ ∈ Finset.univ.erase 0,
          ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ *
            ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
              Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) * incidenceVectorEnergy c := by
  let B (ξ : ZMod q × ZMod q) : ℝ :=
    (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
      Real.sqrt (incidenceFrequencyGCD ξ : ℝ)
  have hmean : incidenceVectorEnergy (incidenceMatrixMod A *ᵥ c) ≤
      (q : ℝ) ^ 2 * incidenceVectorEnergy c := by
    apply incidenceVectorEnergy_le_gram_norm
    simpa only [incidenceModeMod, incidenceMode_zero] using
      incidenceModeMod_zero_norm_le hq A hA
  have hmass : 0 ≤ ∑ z, W z := Finset.sum_nonneg fun z _ => hW z
  have hB : ∀ ξ, ξ ≠ 0 → ‖incidenceMode (incidenceMatrixMod A) ξ‖ ≤ B ξ :=
    fun ξ _ => incidenceModeMod_squarefree_norm_le_residue hK4 hq A hA ξ
  calc
    _ ≤ ((q : ℝ) ^ 2)⁻¹ *
        ((∑ z, W z) * incidenceVectorEnergy (incidenceMatrixMod A *ᵥ c) +
          (∑ ξ ∈ Finset.univ.erase 0,
            ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) * incidenceVectorEnergy c) :=
      incidenceRowEnergy_le_modes _ W c B hB
    _ ≤ ((q : ℝ) ^ 2)⁻¹ *
        ((∑ z, W z) * ((q : ℝ) ^ 2 * incidenceVectorEnergy c) +
          (∑ ξ ∈ Finset.univ.erase 0,
            ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) * incidenceVectorEnergy c) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hmean hmass) le_rfl)
        (inv_nonneg.mpr (sq_nonneg _))
    _ = _ := by
      have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
      dsimp only [B]
      field_simp
      simp only [mul_assoc, mul_left_comm, mul_comm]

#print axioms incidence_gram_le_of_norm
#print axioms incidenceModeMod_zero_posSemidef
#print axioms incidenceModeMod_zero_le
#print axioms incidenceModeMod_squarefree_norm_le_residue
#print axioms incidenceModeMod_uniform_norm_le
#print axioms incidenceRowEnergy_squarefree_le

end PrimeGap182Audit
