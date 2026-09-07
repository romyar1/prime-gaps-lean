import IncidencePeriodization

/-!
# Explicit finite matrix inputs to the common incidence-window argument

These two hypotheses are bounds on actual finite matrices. They contain no
lattice, smooth-window, or asymptotic estimate. Both are proved for the
actual squarefree incidence matrix from the scalar rank-four input below.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]

structure IncidenceModalBounds (R : Matrix (ZMod q × ZMod q) ι ℂ) : Prop where
  zero_norm_le : ‖Rᴴ * R‖ ≤ (q : ℝ) ^ 2
  mode_norm_le : ∀ ξ : ZMod q × ZMod q, ‖incidenceMode R ξ‖ ≤
    (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
      Real.sqrt (incidenceFrequencyGCD ξ : ℝ)

theorem incidenceModalBounds_of_rankFour (hK4 : AllIncidenceRankFourBounds)
    (hq : Squarefree q) (A : ZMod q) (hA : IsUnit A) :
    IncidenceModalBounds (incidenceMatrixMod A) := by
  constructor
  · simpa only [incidenceModeMod, incidenceMode_zero] using incidenceModeMod_zero_norm_le hq A hA
  · exact incidenceModeMod_squarefree_norm_le_residue hK4 hq A hA

theorem incidenceRowEnergy_from_modes (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (hR : IncidenceModalBounds R) (W : ZMod q × ZMod q → ℝ)
    (hW : ∀ z, 0 ≤ W z) (c : ι → ℂ) :
    incidenceRowEnergy R W c ≤
      ((∑ z, W z) + ((q : ℝ) ^ 2)⁻¹ *
        ∑ ξ ∈ Finset.univ.erase 0,
          ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ *
            ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
              Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) * incidenceVectorEnergy c := by
  let B (ξ : ZMod q × ZMod q) : ℝ :=
    (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
      Real.sqrt (incidenceFrequencyGCD ξ : ℝ)
  have hm := incidenceVectorEnergy_le_gram_norm R ((q : ℝ) ^ 2) hR.zero_norm_le c
  have hmass : 0 ≤ ∑ z, W z := Finset.sum_nonneg (fun z _ => hW z)
  calc
    _ ≤ ((q : ℝ) ^ 2)⁻¹ *
        ((∑ z, W z) * incidenceVectorEnergy (R *ᵥ c) +
          (∑ ξ ∈ Finset.univ.erase 0,
            ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) * incidenceVectorEnergy c) :=
      incidenceRowEnergy_le_modes R W c B (fun ξ _ => hR.mode_norm_le ξ)
    _ ≤ ((q : ℝ) ^ 2)⁻¹ *
        ((∑ z, W z) * ((q : ℝ) ^ 2 * incidenceVectorEnergy c) +
          (∑ ξ ∈ Finset.univ.erase 0,
            ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) * incidenceVectorEnergy c) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hm hmass) le_rfl) (by positivity)
    _ = _ := by
      have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
      dsimp only [B]
      field_simp
      simp only [mul_assoc, mul_left_comm, mul_comm]

theorem incidenceLatticeEnergy_from_modes (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (hR : IncidenceModalBounds R) (w : ℤ × ℤ → ℝ) (hw : Summable w)
    (hw0 : ∀ z, 0 ≤ w z) (c : ι → ℂ) :
    (∑' z : ℤ × ℤ, w z * ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
      ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        ∑ ξ ∈ Finset.univ.erase 0,
          ‖∑' z : ℤ × ℤ, (w z : ℂ) * incidenceJointChar ξ (-incidenceIntegerResidue q z)‖ *
            ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
              Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) * incidenceVectorEnergy c := by
  have h := incidenceRowEnergy_from_modes R hR (incidencePeriodize w)
    (incidencePeriodize_nonneg w hw0) c
  rw [incidencePeriodize_energy R w hw c, incidencePeriodize_mass w hw] at h
  have hwc : Summable (fun z => ‖(w z : ℂ)‖) := by
    simpa only [Complex.norm_real] using hw.norm
  have hd (ξ : ZMod q × ZMod q) :
      incidenceJointDFT (fun r => ((incidencePeriodize w r : ℝ) : ℂ)) ξ =
        ∑' z : ℤ × ℤ, (w z : ℂ) * incidenceJointChar ξ (-incidenceIntegerResidue q z) := by
    have heq : incidencePeriodize (fun z => (w z : ℂ)) =
        (fun r : ZMod q × ZMod q => ((incidencePeriodize w r : ℝ) : ℂ)) := by
      funext r
      exact incidencePeriodize_ofReal w r
    rw [← heq]
    exact incidencePeriodize_dft (fun z => (w z : ℂ)) hwc ξ
  simpa only [hd] using h

#print axioms incidenceModalBounds_of_rankFour
#print axioms incidenceRowEnergy_from_modes
#print axioms incidenceLatticeEnergy_from_modes

end PrimeGap182Audit
