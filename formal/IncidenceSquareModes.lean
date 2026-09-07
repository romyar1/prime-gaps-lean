import IncidencePrimeIdentities

/-!
# The reciprocal-square correction modes

The Fourier eigenvalues are actual sums over fibers of `u ↦ A/u²`.
The fibers have cardinality at most two, by the field identity for equal
squares. This proves the `2p` Euclidean norm bound without any cancellation
axiom, including characteristic two.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {p : ℕ} [Fact p.Prime]

def incidenceSquareKernel (A ν d : ZMod p) : ℂ :=
  ∑ u : (ZMod p)ˣ, ZMod.stdAddChar (A * d / (u : ZMod p) ^ 2 + ν * (u : ZMod p))

theorem incidenceSquareMode_eq_circulant (A ν : ZMod p) :
    incidenceSquareMode A ν = Matrix.circulant (incidenceSquareKernel A ν) := by
  ext b b'
  simp only [incidenceSquareMode, Matrix.circulant_apply, incidenceSquareKernel]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem incidenceSquareKernel_dft (A ν s : ZMod p) :
    ZMod.dft (incidenceSquareKernel A ν) s =
      (p : ℂ) * ∑ u : (ZMod p)ˣ,
        if A / (u : ZMod p) ^ 2 = s then ZMod.stdAddChar (ν * (u : ZMod p)) else 0 := by
  rw [ZMod.dft_apply]
  simp only [incidenceSquareKernel, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  have hphase (d : ZMod p) :
      ZMod.stdAddChar (-(d * s)) *
        ZMod.stdAddChar (A * d / (u : ZMod p) ^ 2 + ν * (u : ZMod p)) =
      ZMod.stdAddChar (ν * (u : ZMod p)) *
        ZMod.stdAddChar ((A / (u : ZMod p) ^ 2 - s) * d) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  simp_rw [hphase, ← Finset.mul_sum, PrimeGap186.stdAddChar_sum]
  by_cases h : A / (u : ZMod p) ^ 2 = s <;> simp [h, sub_eq_zero, mul_comm]

theorem incidenceSquareMode_fiber_card_le (A : ZMod p) (hA : A ≠ 0) (s : ZMod p) :
    (Finset.univ.filter (fun u : (ZMod p)ˣ => A / (u : ZMod p) ^ 2 = s)).card ≤ 2 := by
  let F := Finset.univ.filter (fun u : (ZMod p)ˣ => A / (u : ZMod p) ^ 2 = s)
  change F.card ≤ 2
  by_cases hF : F.Nonempty
  · obtain ⟨u, hu⟩ := hF
    have hsub : F ⊆ {u, -u} := by
      intro v hv
      have hu' := (Finset.mem_filter.mp hu).2
      have hv' := (Finset.mem_filter.mp hv).2
      have hratio : A * ((v : ZMod p) ^ 2)⁻¹ = A * ((u : ZMod p) ^ 2)⁻¹ := by
        simpa only [div_eq_mul_inv] using hv'.trans hu'.symm
      have hsq : (v : ZMod p) ^ 2 = (u : ZMod p) ^ 2 :=
        inv_injective (mul_left_cancel₀ hA hratio)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
      · have hvu : v = u := Units.ext heq
        simp [hvu]
      · have hvu : v = -u := by
          apply Units.ext
          simpa only [Units.val_neg] using heq
        simp [hvu]
    exact (Finset.card_le_card hsub).trans (by
      simpa only [Finset.card_singleton] using Finset.card_insert_le u {-u})
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    norm_num

theorem incidenceSquareKernel_dft_norm_le (A ν s : ZMod p) (hA : A ≠ 0) :
    ‖ZMod.dft (incidenceSquareKernel A ν) s‖ ≤ 2 * (p : ℝ) := by
  rw [incidenceSquareKernel_dft, norm_mul, Complex.norm_natCast]
  let F := Finset.univ.filter (fun u : (ZMod p)ˣ => A / (u : ZMod p) ^ 2 = s)
  have hsum :
      ‖∑ u : (ZMod p)ˣ,
        if A / (u : ZMod p) ^ 2 = s then ZMod.stdAddChar (ν * (u : ZMod p)) else 0‖ ≤
      (F.card : ℝ) := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ u ∈ F, ‖ZMod.stdAddChar (ν * (u : ZMod p))‖ := norm_sum_le _ _
      _ = (F.card : ℝ) := by simp only [AddChar.norm_apply, Finset.sum_const,
        nsmul_eq_mul, mul_one]
  have hcard : (F.card : ℝ) ≤ 2 := by
    exact_mod_cast incidenceSquareMode_fiber_card_le A hA s
  simpa only [mul_comm (p : ℝ) 2] using
    mul_le_mul_of_nonneg_left (hsum.trans hcard) (Nat.cast_nonneg p)

theorem incidenceSquareMode_norm_le (A ν : ZMod p) (hA : A ≠ 0) :
    ‖incidenceSquareMode A ν‖ ≤ 2 * (p : ℝ) := by
  rw [incidenceSquareMode_eq_circulant]
  exact incidenceCirculant_norm_le _ _ (by positivity)
    (fun s => incidenceSquareKernel_dft_norm_le A ν s hA)

#print axioms incidenceSquareKernel_dft
#print axioms incidenceSquareMode_fiber_card_le
#print axioms incidenceSquareKernel_dft_norm_le
#print axioms incidenceSquareMode_norm_le

end PrimeGap182Audit
