import IncidenceCompression

/-!
# Nonzero prime incidence modes from the scalar rank-four input

The projective substitution is an actual permutation of the finite field,
using inverse zero equals zero. Deleting its pole realizes the principal
matrix as a compression of the reciprocal rank-three circulant. Pole and
diagonal corrections are actual matrices with proved norm bounds.

The final numerical constant is a uniform `8`; sharp correction constants
are unnecessary for the squarefree subpower-loss application.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {p : ℕ} [Fact p.Prime]

/-- `b ↦ (ν(h-νb))⁻¹`, an actual permutation when `ν ≠ 0`. -/
def incidenceProjectiveEquiv (h ν : ZMod p) (hν : ν ≠ 0) : Equiv.Perm (ZMod p) :=
  (Equiv.mulLeft₀ ν hν).trans
    ((Equiv.subLeft h).trans ((Equiv.mulLeft₀ ν hν).trans (Equiv.inv (ZMod p))))

theorem incidenceProjectiveEquiv_apply (h ν : ZMod p) (hν : ν ≠ 0) (b : ZMod p) :
    incidenceProjectiveEquiv h ν hν b = (ν * (h - ν * b))⁻¹ := rfl

theorem incidenceProjective_pole_iff (h ν b : ZMod p) (hν : ν ≠ 0) :
    h - ν * b = 0 ↔ b = h / ν := by
  constructor
  · intro hb
    exact (eq_div_iff hν).mpr (by simpa [mul_comm] using (sub_eq_zero.mp hb).symm)
  · intro hb
    subst b
    field_simp
    ring

theorem incidenceProjective_argument (A h ν b b' : ZMod p) (hν : ν ≠ 0)
    (hbb : b ≠ b') (hb : b ≠ h / ν) (hb' : b' ≠ h / ν) :
    -A / (incidenceProjectiveEquiv h ν hν b - incidenceProjectiveEquiv h ν hν b') =
      A * (h - ν * b) * (h - ν * b') / (b' - b) := by
  have hd : b' - b ≠ 0 := sub_ne_zero.mpr hbb.symm
  have hf : h - ν * b ≠ 0 := fun h0 => hb ((incidenceProjective_pole_iff h ν b hν).mp h0)
  have hf' : h - ν * b' ≠ 0 := fun h0 => hb' ((incidenceProjective_pole_iff h ν b' hν).mp h0)
  have hdiff : incidenceProjectiveEquiv h ν hν b - incidenceProjectiveEquiv h ν hν b' ≠ 0 :=
    sub_ne_zero.mpr (fun heq => hbb ((incidenceProjectiveEquiv h ν hν).injective heq))
  apply (div_eq_iff hdiff).mpr
  simp only [incidenceProjectiveEquiv_apply]
  field_simp
  ring

/-- The principal matrix is defined by an actual diagonal compression and permutation. -/
def incidenceProjectivePrincipal (A h ν : ZMod p) (hν : ν ≠ 0) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  incidenceDeleteIndex (h / ν) *
    (((p : ℂ) • Matrix.circulant (incidenceReciprocalKl3Kernel (-A))).submatrix
      (incidenceProjectiveEquiv h ν hν) (incidenceProjectiveEquiv h ν hν)) *
    incidenceDeleteIndex (h / ν)

theorem incidenceProjectivePrincipal_apply (A h ν : ZMod p) (hν : ν ≠ 0)
    (b b' : ZMod p) :
    incidenceProjectivePrincipal A h ν hν b b' =
      if b = h / ν ∨ b' = h / ν then 0 else
        (p : ℂ) * incidenceReciprocalKl3Kernel (-A)
          (incidenceProjectiveEquiv h ν hν b - incidenceProjectiveEquiv h ν hν b') := by
  rw [incidenceProjectivePrincipal, incidenceDeleteIndex_mul_apply]
  rfl

theorem incidenceProjectivePrincipal_norm_le (A h ν : ZMod p) (hν : ν ≠ 0)
    (hA : A ≠ 0) (hK4 : IncidenceRankFourBound p) :
    ‖incidenceProjectivePrincipal A h ν hν‖ ≤ 4 * (p : ℝ) * Real.sqrt (p : ℝ) := by
  unfold incidenceProjectivePrincipal
  calc
    _ ≤ ‖(p : ℂ) • Matrix.circulant (incidenceReciprocalKl3Kernel (-A))‖ :=
      (incidence_compressed_norm_le _ _).trans (incidence_permuted_norm_le _ _)
    _ = (p : ℝ) * ‖Matrix.circulant (incidenceReciprocalKl3Kernel (-A))‖ := by
      rw [norm_smul, Complex.norm_natCast]
    _ ≤ (p : ℝ) * (4 * Real.sqrt (p : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (incidenceReciprocalKl3Circulant_norm_le (-A) (neg_ne_zero.mpr hA) hK4)
        (Nat.cast_nonneg p)
    _ = _ := by ring

/-- Exact matrix decomposition at a nonzero second frequency. -/
theorem primeIncidenceMode_projective_decomposition (A h ν : ZMod p)
    (hA : A ≠ 0) (hν : ν ≠ 0) :
    primeIncidenceMode A (h, ν) =
      incidenceProjectivePrincipal A h ν hν + incidencePoleMatrix (h / ν) -
        incidenceSquareMode A ν - (p : ℂ) • incidencePointProjection (h / ν) := by
  ext b b'
  by_cases hbb : b = b'
  · subst b'
    rw [primeIncidenceMode_diagonal]
    simp only [incidenceProjective_pole_iff h ν b hν]
    by_cases hb : b = h / ν <;>
      simp [incidenceProjectivePrincipal_apply,
        incidenceReciprocalKl3Kernel, incidencePoleMatrix, incidenceSquareMode_diagonal,
        incidencePointProjection, hν, hb]
  · rw [primeIncidenceMode_offDiagonal A h ν b b' hA hbb]
    have hpoint : incidencePointProjection (h / ν) b b' = 0 := by
      simp [incidencePointProjection, Matrix.diagonal_apply_ne _ hbb]
    simp only [hν, and_false, ↓reduceIte, sub_zero, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hpoint, mul_zero]
    by_cases hb : b = h / ν
    · have hb' : b' ≠ h / ν := fun heq => hbb (hb.trans heq.symm)
      have hf := (incidenceProjective_pole_iff h ν b hν).mpr hb
      rw [hf]
      simp [incidenceProjectivePrincipal_apply, incidencePoleMatrix, hb, hb',
        PrimeGap186.normalizedKloosterman3_zero]
    · by_cases hb' : b' = h / ν
      · have hf' := (incidenceProjective_pole_iff h ν b' hν).mpr hb'
        rw [hf']
        simp [incidenceProjectivePrincipal_apply, incidencePoleMatrix, hb, hb',
          PrimeGap186.normalizedKloosterman3_zero]
      · have hdiff : incidenceProjectiveEquiv h ν hν b - incidenceProjectiveEquiv h ν hν b' ≠ 0 :=
          sub_ne_zero.mpr (fun heq => hbb ((incidenceProjectiveEquiv h ν hν).injective heq))
        simp only [incidenceProjectivePrincipal_apply, hb, hb', ↓reduceIte,
          incidencePoleMatrix, false_and, or_false, add_zero, incidenceReciprocalKl3Kernel,
          ite_eq_right hdiff]
        rw [incidenceProjective_argument A h ν b b' hν hbb hb hb']

/-- At zero second frequency and nonzero first frequency, the principal matrix is circulant. -/
theorem primeIncidenceMode_circulant_decomposition (A h : ZMod p)
    (hA : A ≠ 0) (hh : h ≠ 0) :
    primeIncidenceMode A (h, 0) =
      (p : ℂ) • Matrix.circulant (incidenceReciprocalKl3Kernel (-A * h ^ 2)) -
        incidenceSquareMode A 0 := by
  ext b b'
  by_cases hbb : b = b'
  · subst b'
    simp [primeIncidenceMode_diagonal, incidenceSquareMode_diagonal,
      incidenceReciprocalKl3Kernel, hh]
  · have hd : b' - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbb)
    have hd' : b - b' ≠ 0 := sub_ne_zero.mpr hbb
    have harg : -(A * h ^ 2) / (b - b') = A * h * h / (b' - b) := by
      field_simp
      ring
    rw [primeIncidenceMode_offDiagonal A h 0 b b' hA hbb]
    simp [Matrix.circulant_apply, incidenceReciprocalKl3Kernel, hd', harg, hh]

theorem primeIncidenceMode_norm_le_of_second_ne_zero (A h ν : ZMod p)
    (hA : A ≠ 0) (hν : ν ≠ 0) (hK4 : IncidenceRankFourBound p) :
    ‖primeIncidenceMode A (h, ν)‖ ≤
      4 * (p : ℝ) * Real.sqrt (p : ℝ) + 4 * (p : ℝ) := by
  have hQ := incidenceProjectivePrincipal_norm_le A h ν hν hA hK4
  have hE : ‖incidencePoleMatrix (h / ν)‖ ≤ (p : ℝ) := by
    simpa only [ZMod.card] using incidencePoleMatrix_norm_le (h / ν)
  have hS := incidenceSquareMode_norm_le A ν hA
  have hD : ‖(p : ℂ) • incidencePointProjection (h / ν)‖ ≤ (p : ℝ) := by
    rw [norm_smul, Complex.norm_natCast]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (incidencePointProjection_norm_le (h / ν)) (Nat.cast_nonneg p)
  rw [primeIncidenceMode_projective_decomposition A h ν hA hν]
  calc
    _ ≤ ‖incidenceProjectivePrincipal A h ν hν + incidencePoleMatrix (h / ν) -
          incidenceSquareMode A ν‖ + ‖(p : ℂ) • incidencePointProjection (h / ν)‖ := norm_sub_le _ _
    _ ≤ (‖incidenceProjectivePrincipal A h ν hν + incidencePoleMatrix (h / ν)‖ +
          ‖incidenceSquareMode A ν‖) + ‖(p : ℂ) • incidencePointProjection (h / ν)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖incidenceProjectivePrincipal A h ν hν‖ + ‖incidencePoleMatrix (h / ν)‖) +
          ‖incidenceSquareMode A ν‖) + ‖(p : ℂ) • incidencePointProjection (h / ν)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ ((4 * (p : ℝ) * Real.sqrt (p : ℝ) + (p : ℝ)) + 2 * (p : ℝ)) + (p : ℝ) :=
      add_le_add (add_le_add (add_le_add hQ hE) hS) hD
    _ = _ := by ring

theorem primeIncidenceMode_norm_le_of_second_zero (A h : ZMod p)
    (hA : A ≠ 0) (hh : h ≠ 0) (hK4 : IncidenceRankFourBound p) :
    ‖primeIncidenceMode A (h, 0)‖ ≤
      4 * (p : ℝ) * Real.sqrt (p : ℝ) + 2 * (p : ℝ) := by
  rw [primeIncidenceMode_circulant_decomposition A h hA hh]
  have hL := incidenceReciprocalKl3Circulant_norm_le (-A * h ^ 2)
    (mul_ne_zero (neg_ne_zero.mpr hA) (pow_ne_zero 2 hh)) hK4
  have hC : ‖(p : ℂ) • Matrix.circulant (incidenceReciprocalKl3Kernel (-A * h ^ 2))‖ ≤
      4 * (p : ℝ) * Real.sqrt (p : ℝ) := by
    rw [norm_smul, Complex.norm_natCast]
    simpa only [mul_assoc, mul_left_comm (p : ℝ) 4] using
      mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg p)
  exact (norm_sub_le _ _).trans (add_le_add hC (incidenceSquareMode_norm_le A 0 hA))

/-- Uniform nonzero-mode bound for the actual incidence matrix. The only
external mathematical hypothesis is the explicit scalar rank-four sum bound. -/
theorem primeIncidenceMode_norm_le (A : ZMod p) (hA : A ≠ 0)
    (hK4 : IncidenceRankFourBound p) (ξ : ZMod p × ZMod p) (hξ : ξ ≠ 0) :
    ‖primeIncidenceMode A ξ‖ ≤ 8 * (p : ℝ) * Real.sqrt (p : ℝ) := by
  obtain ⟨h, ν⟩ := ξ
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hsqrt : 1 ≤ Real.sqrt (p : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  by_cases hν : ν = 0
  · subst ν
    have hh : h ≠ 0 := by
      intro hh
      exact hξ (by simp [hh])
    exact (primeIncidenceMode_norm_le_of_second_zero A h hA hh hK4).trans (by nlinarith)
  · exact (primeIncidenceMode_norm_le_of_second_ne_zero A h ν hA hν hK4).trans (by nlinarith)

/-- Completion with the actual prime modes now discharged by a scalar input. -/
theorem primeIncidenceRowEnergy_le_of_rankFour (A : ZMod p) (hA : A ≠ 0)
    (hK4 : IncidenceRankFourBound p) (W : ZMod p × ZMod p → ℝ) (hW : ∀ z, 0 ≤ W z)
    (c : ZMod p → ℂ) :
    incidenceRowEnergy (primeIncidenceMatrix A) W c ≤
      ((∑ z, W z) + ((p : ℝ) ^ 2)⁻¹ *
        ∑ ξ ∈ Finset.univ.erase 0,
          ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ *
            (8 * (p : ℝ) * Real.sqrt (p : ℝ))) * incidenceVectorEnergy c :=
  primeIncidenceRowEnergy_le A hA W hW c _
    (fun ξ hξ => primeIncidenceMode_norm_le A hA hK4 ξ hξ)

#print axioms incidenceProjectiveEquiv
#print axioms incidenceProjective_argument
#print axioms incidenceProjectivePrincipal_norm_le
#print axioms primeIncidenceMode_projective_decomposition
#print axioms primeIncidenceMode_circulant_decomposition
#print axioms primeIncidenceMode_norm_le
#print axioms primeIncidenceRowEnergy_le_of_rankFour

end PrimeGap182Audit
