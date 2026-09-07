import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The operator support-restoration argument in the bound-182 paper

These statements concern actual positive and symmetric operators on a real
inner product space. They do not assume or assert a prime-distribution result.
The final partition theorem permits noncommuting operators and signed vectors.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem positive_cross_sq (Q : E →ₗ[ℝ] E) (hQ : Q.IsPositive) (x y : E) :
    ⟪x, Q y⟫ ^ 2 ≤ ⟪x, Q x⟫ * ⟪y, Q y⟫ := by
  have hsym : ⟪y, Q x⟫ = ⟪x, Q y⟫ := by
    rw [real_inner_comm (Q x) y]
    exact hQ.isSymmetric x y
  have hpoly (r : ℝ) :
      0 ≤ ⟪x, Q x⟫ * (r * r) + (2 * ⟪x, Q y⟫) * r + ⟪y, Q y⟫ := by
    have h := hQ.inner_nonneg_right (r • x + y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hsym] at h
    nlinarith only [h]
  have hdisc := discrim_le_zero hpoly
  simp only [discrim] at hdisc
  nlinarith only [hdisc]

theorem positive_cross_le_sqrt (Q : E →ₗ[ℝ] E) (hQ : Q.IsPositive)
    (x y : E) {A M : ℝ} (hA : ⟪x, Q x⟫ ≤ A) (hM : ⟪y, Q y⟫ ≤ M) :
    ⟪x, Q y⟫ ≤ Real.sqrt (A * M) := by
  have hx := hQ.inner_nonneg_right x
  have hy := hQ.inner_nonneg_right y
  have hAnon : 0 ≤ A := hx.trans hA
  have hMnon : 0 ≤ M := hy.trans hM
  have hsq := (positive_cross_sq Q hQ x y).trans (mul_le_mul hA hM hy hAnon)
  have hr := Real.sq_sqrt (mul_nonneg hAnon hMnon)
  have hr0 := Real.sqrt_nonneg (A * M)
  nlinarith only [hsq, hr, hr0]

theorem positive_operator_young (D : E →ₗ[ℝ] E) (hD : D.IsPositive)
    {Γ t : ℝ} (hΓ : 0 < Γ) (ht : 0 < t)
    (hupper : ∀ x : E, ⟪x, D x⟫ ≤ Γ * ⟪x, x⟫) (e F : E) :
    -t * ⟪e, e⟫ - (Γ / t) * ⟪F, D F⟫ ≤ 2 * ⟪e, D F⟫ := by
  have hsym : ⟪F, D e⟫ = ⟪e, D F⟫ := by
    rw [real_inner_comm (D e) F]
    exact hD.isSymmetric e F
  have hpos := hD.inner_nonneg_right ((t / Γ) • e + F)
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hsym] at hpos
  have hupper' := mul_le_mul_of_nonneg_left (hupper e) (sq_nonneg (t / Γ))
  have hpre : 0 ≤ (t / Γ) ^ 2 * (Γ * ⟪e, e⟫) +
      2 * (t / Γ) * ⟪e, D F⟫ + ⟪F, D F⟫ := by
    nlinarith only [hpos, hupper']
  have hscaled := mul_nonneg (le_of_lt (div_pos hΓ ht)) hpre
  have hid : (Γ / t) * ((t / Γ) ^ 2 * (Γ * ⟪e, e⟫) +
      2 * (t / Γ) * ⟪e, D F⟫ + ⟪F, D F⟫) =
      t * ⟪e, e⟫ + 2 * ⟪e, D F⟫ + (Γ / t) * ⟪F, D F⟫ := by
    field_simp
  rw [hid] at hscaled
  linarith only [hscaled]

theorem restoration_expansion (C D P : E →ₗ[ℝ] E)
    (hC : C.IsSymmetric) (hD : D.IsSymmetric) (hP : P.IsSymmetric)
    (hPid : ∀ x : E, P (P x) = P x) (F : E) :
    ⟪P F, (C - D - 1) (P F)⟫ =
      ⟪F, (C - 1) F⟫ - ⟪F, D F⟫ - 2 * ⟪F - P F, C F⟫ +
      2 * ⟪F - P F, D F⟫ + ⟪F - P F, (C - D + 1) (F - P F)⟫ := by
  have horth : ⟪P F, F⟫ = ⟪P F, P F⟫ := by
    calc
      ⟪P F, F⟫ = ⟪F, P F⟫ := real_inner_comm F (P F)
      _ = ⟪F, P (P F)⟫ := congrArg (fun x ↦ ⟪F, x⟫) (hPid F).symm
      _ = ⟪P F, P F⟫ := (hP F (P F)).symm
  have hCsym : ⟪P F, C F⟫ = ⟪F, C (P F)⟫ := by
    rw [real_inner_comm (C F) (P F)]
    exact hC F (P F)
  have hDsym : ⟪P F, D F⟫ = ⟪F, D (P F)⟫ := by
    rw [real_inner_comm (D F) (P F)]
    exact hD F (P F)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
    map_sub, inner_sub_left, inner_sub_right, inner_add_right]
  rw [hCsym, hDsym, horth, real_inner_comm (P F) F, horth]
  ring

theorem projection_residual_form (P : E →ₗ[ℝ] E) (hP : P.IsSymmetric)
    (hPid : ∀ x : E, P (P x) = P x) (F : E) :
    ⟪F, F - P F⟫ = ⟪F - P F, F - P F⟫ := by
  have horth : ⟪P F, P F⟫ = ⟪F, P F⟫ := by
    simpa only [hPid] using hP F (P F)
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_comm F (P F), horth]
  ring

/-- The exact unnormalized partitioned restoration inequality. For the paper's
normalization divide this inequality by `⟪F,F⟫ > 0` and divide each source
bound by the same quantity. The positive partition operators are multiplication
by the paper's soft partition functions; no commutation with `C` or `D` is used. -/
theorem partitioned_restoration {ι : Type*} [Fintype ι]
    (C D P : E →ₗ[ℝ] E) (Q : ι → E →ₗ[ℝ] E)
    (hC : C.IsSymmetric) (hD : D.IsPositive) (hP : P.IsSymmetric)
    (hPid : ∀ x : E, P (P x) = P x)
    (hQ : ∀ j, (Q j).IsPositive) (hpartition : ∑ j, Q j = 1 - P)
    {Γ δ t : ℝ} (hΓ : 0 < Γ) (hδ : δ < 1) (ht : 1 - δ < t)
    (hDupper : ∀ x : E, ⟪x, D x⟫ ≤ Γ * ⟪x, x⟫)
    (hTlower : ∀ x : E, -δ * ⟪x, x⟫ ≤ ⟪x, (C - D) x⟫)
    (F : E) (A M : ι → ℝ) {b : ℝ}
    (hA : ∀ j, ⟪F, Q j F⟫ ≤ A j)
    (hM : ∀ j, ⟪C F, Q j (C F)⟫ ≤ M j)
    (hb : ⟪F, D F⟫ ≤ b) :
    ⟪F, (C - 1) F⟫ - b - Γ * b / t -
      2 * ∑ j, Real.sqrt (A j * M j) - (t - (1 - δ)) * ∑ j, A j ≤
      ⟪P F, (C - D - 1) (P F)⟫ := by
  have htpos : 0 < t := (sub_pos.mpr hδ).trans ht
  have hmass : ∑ j, ⟪F, Q j F⟫ = ⟪F - P F, F - P F⟫ := by
    calc
      ∑ j, ⟪F, Q j F⟫ = ⟪F, (∑ j, Q j) F⟫ := by simp [inner_sum]
      _ = ⟪F, F - P F⟫ := by rw [hpartition]; rfl
      _ = ⟪F - P F, F - P F⟫ := projection_residual_form P hP hPid F
  have hmassle : ⟪F - P F, F - P F⟫ ≤ ∑ j, A j := by
    rw [← hmass]
    exact Finset.sum_le_sum (fun j _ ↦ hA j)
  have hcross : ⟪F - P F, C F⟫ = ∑ j, ⟪F, Q j (C F)⟫ := by
    calc
      ⟪F - P F, C F⟫ = ⟪F, C F⟫ - ⟪P F, C F⟫ := inner_sub_left _ _ _
      _ = ⟪F, C F⟫ - ⟪F, P (C F)⟫ := by rw [hP F (C F)]
      _ = ⟪F, (1 - P) (C F)⟫ := by simp [inner_sub_right]
      _ = ∑ j, ⟪F, Q j (C F)⟫ := by rw [← hpartition]; simp [inner_sum]
  have hcrossle : ⟪F - P F, C F⟫ ≤ ∑ j, Real.sqrt (A j * M j) := by
    rw [hcross]
    exact Finset.sum_le_sum (fun j _ ↦ positive_cross_le_sqrt (Q j) (hQ j)
      F (C F) (hA j) (hM j))
  have hinner := positive_operator_young D hD hΓ htpos hDupper (F - P F) F
  have hlast : (1 - δ) * ⟪F - P F, F - P F⟫ ≤
      ⟪F - P F, (C - D + 1) (F - P F)⟫ := by
    have h := hTlower (F - P F)
    simp only [LinearMap.add_apply, Module.End.one_apply, inner_add_right]
    linarith only [h]
  have hreplace_mass := mul_le_mul_of_nonneg_left hmassle (sub_nonneg.mpr ht.le)
  have hreplace_b := mul_le_mul_of_nonneg_left hb (le_of_lt (div_pos hΓ htpos))
  have hexp := restoration_expansion C D P hC hD.isSymmetric hP hPid F
  have hpenalty : Γ * b / t = (Γ / t) * b := by ring
  rw [hpenalty]
  linarith only [hexp, hcrossle, hinner, hlast, hreplace_mass, hreplace_b, hb]

/-- The main paper's normalized restoration lemma, with an arbitrary common
positive normalization `N` (in the application `N = ‖F‖²`). -/
theorem partitioned_restoration_normalized {ι : Type*} [Fintype ι]
    (C D P : E →ₗ[ℝ] E) (Q : ι → E →ₗ[ℝ] E)
    (hC : C.IsSymmetric) (hD : D.IsPositive) (hP : P.IsSymmetric)
    (hPid : ∀ x : E, P (P x) = P x)
    (hQ : ∀ j, (Q j).IsPositive) (hpartition : ∑ j, Q j = 1 - P)
    {Γ δ t N : ℝ} (hΓ : 0 < Γ) (hδ : δ < 1) (ht : 1 - δ < t) (hN : 0 < N)
    (hDupper : ∀ x : E, ⟪x, D x⟫ ≤ Γ * ⟪x, x⟫)
    (hTlower : ∀ x : E, -δ * ⟪x, x⟫ ≤ ⟪x, (C - D) x⟫)
    (F : E) (A M : ι → ℝ) {b : ℝ}
    (hA : ∀ j, ⟪F, Q j F⟫ / N ≤ A j)
    (hM : ∀ j, ⟪C F, Q j (C F)⟫ / N ≤ M j)
    (hb : ⟪F, D F⟫ / N ≤ b) :
    ⟪F, (C - 1) F⟫ / N - b - Γ * b / t -
      2 * ∑ j, Real.sqrt (A j * M j) - (t - (1 - δ)) * ∑ j, A j ≤
      ⟪P F, (C - D - 1) (P F)⟫ / N := by
  have hA' (j) : ⟪F, Q j F⟫ ≤ N * A j := by
    simpa only [mul_comm N] using (div_le_iff₀ hN).mp (hA j)
  have hM' (j) : ⟪C F, Q j (C F)⟫ ≤ N * M j := by
    simpa only [mul_comm N] using (div_le_iff₀ hN).mp (hM j)
  have hb' : ⟪F, D F⟫ ≤ N * b := by
    simpa only [mul_comm N] using (div_le_iff₀ hN).mp hb
  have h := partitioned_restoration C D P Q hC hD hP hPid hQ hpartition
    hΓ hδ ht hDupper hTlower F (fun j ↦ N * A j) (fun j ↦ N * M j) hA' hM' hb'
  have hsqrt (j) : Real.sqrt ((N * A j) * (N * M j)) = N * Real.sqrt (A j * M j) := by
    rw [show (N * A j) * (N * M j) = N ^ 2 * (A j * M j) by ring,
      Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
  simp_rw [hsqrt] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h
  apply (le_div_iff₀ hN).mpr
  calc
    (⟪F, (C - 1) F⟫ / N - b - Γ * b / t -
        2 * ∑ j, Real.sqrt (A j * M j) - (t - (1 - δ)) * ∑ j, A j) * N =
        ⟪F, (C - 1) F⟫ - N * b - Γ * (N * b) / t -
        2 * (N * ∑ j, Real.sqrt (A j * M j)) -
        (t - (1 - δ)) * (N * ∑ j, A j) := by
          field_simp [ne_of_gt hN, ne_of_gt ((sub_pos.mpr hδ).trans ht)]
    _ ≤ ⟪P F, (C - D - 1) (P F)⟫ := h

#print axioms positive_cross_sq
#print axioms positive_cross_le_sqrt
#print axioms positive_operator_young
#print axioms restoration_expansion
#print axioms projection_residual_form
#print axioms partitioned_restoration
#print axioms partitioned_restoration_normalized

end PrimeGap182Audit
