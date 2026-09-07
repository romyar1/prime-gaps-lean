import SourceHybridReference182

/-! Uniform coefficient control for the actual signed hybrid polynomial.
An arbitrary additional H² loss is retained. The true deficit parameter
ranges over a compact interval; it is never replaced in the mixed terms. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace PrimeGap182

def trialHybridCoefficient (κ extra K : ℝ) (h : Fin 3 → ℝ) : ℝ :=
  trialPhysicalHybridPolynomial κ K 1 (h 0) (h 2) (h 1 - h 0) - extra * (h 1 - h 0) ^ 2

theorem trialHybridCoefficient_factor (κ extra K U : ℝ) (h : Fin 3 → ℝ) :
    trialPhysicalHybridPolynomial κ K U (h 0 * U) (h 2 * U) ((h 1 - h 0) * U) -
      extra * ((h 1 - h 0) * U) ^ 2 = trialHybridCoefficient κ extra K h * U ^ 2 := by
  unfold trialHybridCoefficient trialPhysicalHybridPolynomial
  ring

theorem trialHybridCoefficient_control (κmax extra : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      (∀ κ K : ℝ, 0 ≤ κ → κ ≤ κmax → 0 ≤ K → K ≤ 1097 / 500 →
        ∀ h : Fin 3 → ℝ, (∀ b, 0 ≤ h b ∧ h b ≤ 1) → |trialHybridCoefficient κ extra K h| ≤ B) ∧
      ∀ κ K : ℝ, 0 ≤ κ → κ ≤ κmax → 0 ≤ K → K ≤ 1097 / 500 →
        ∀ h h' : Fin 3 → ℝ, (∀ b, 0 ≤ h b ∧ h b ≤ 1) → (∀ b, 0 ≤ h' b ∧ h' b ≤ 1) →
        |trialHybridCoefficient κ extra K h - trialHybridCoefficient κ extra K h'| ≤
          B * ∑ b : Fin 3, |h b - h' b| := by
  let Q : ℝ × (ℝ × (Fin 3 → ℝ)) → ℝ := fun z => trialHybridCoefficient z.1 extra z.2.1 z.2.2
  let S : Set (ℝ × (ℝ × (Fin 3 → ℝ))) :=
    Set.Icc 0 κmax ×ˢ (Set.Icc 0 (1097 / 500 : ℝ) ×ˢ Set.Icc (0 : Fin 3 → ℝ) 1)
  have hQ : ContDiff ℝ 1 Q := by
    unfold Q trialHybridCoefficient trialPhysicalHybridPolynomial
    fun_prop
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hconvex : Convex ℝ S := (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  obtain ⟨L, hL⟩ := hQ.contDiffOn.exists_lipschitzOnWith (by norm_num) hconvex hS
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hQ.continuous.continuousOn
  let B : ℝ := max M ((L : ℝ) + 1)
  have hB : 0 < B := lt_max_of_lt_right (by positivity)
  have hLB : (L : ℝ) ≤ B :=
    (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  refine ⟨B, hB, ?_, ?_⟩
  · intro κ K hκ hκm hK hKm h hh
    have hm : (κ, K, h) ∈ S := ⟨⟨hκ, hκm⟩, ⟨hK, hKm⟩,
      (fun b => (hh b).1), fun b => (hh b).2⟩
    simpa only [Q, Real.norm_eq_abs] using (hM _ hm).trans (le_max_left _ _)
  · intro κ K hκ hκm hK hKm h h' hh hh'
    have hm : (κ, K, h) ∈ S := ⟨⟨hκ, hκm⟩, ⟨hK, hKm⟩,
      (fun b => (hh b).1), fun b => (hh b).2⟩
    have hm' : (κ, K, h') ∈ S := ⟨⟨hκ, hκm⟩, ⟨hK, hKm⟩,
      (fun b => (hh' b).1), fun b => (hh' b).2⟩
    have hd : dist (κ, K, h) (κ, K, h') ≤ ∑ b : Fin 3, |h b - h' b| := by
      simp only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      apply (dist_pi_le_iff (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr
      intro b
      simpa only [Real.dist_eq] using
        (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
          abs_nonneg (h j - h' j)) (Finset.mem_univ b))
    have hp := hL.dist_le_mul _ hm _ hm'
    have hp' : |trialHybridCoefficient κ extra K h - trialHybridCoefficient κ extra K h'| ≤
        (L : ℝ) * dist (κ, K, h) (κ, K, h') := by simpa only [Q, Real.dist_eq] using hp
    exact hp'.trans (mul_le_mul hLB hd dist_nonneg hB.le)

theorem trial_weighted_square_coefficients_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (r : ℝ) (hr : 0 < r)
    (v w z : α → ℝ) (e : Fin 3 → α → ℝ) (C B : ℝ) (hB : 0 ≤ B)
    (hw : Integrable (fun x => w x * v x ^ 2) μ)
    (hz : Integrable (fun x => z x * v x ^ 2) μ)
    (he : ∀ b, Integrable (fun x => e b x ^ 2) μ)
    (hv : ∀ x, v x ^ 2 ≤ C ^ 2)
    (hcoeff : ∀ x, |w x - z x| ≤ B * ∑ b : Fin 3, |e b x|) :
    |(∫ x, w x * v x ^ 2 ∂μ) - ∫ x, z x * v x ^ 2 ∂μ| ≤
      C ^ 2 * B * (3 * r * μ.real Set.univ +
        (1 + r⁻¹) * ∑ b : Fin 3, ∫ x, e b x ^ 2 ∂μ) := by
  have habs (s : ℝ) : |s| ≤ r + (1 + r⁻¹) * s ^ 2 := by
    have hy := two_mul_le_add_mul_sq (a := (1 : ℝ)) (b := |s|) hr
    rw [one_pow, sq_abs] at hy
    nlinarith only [hy, sq_nonneg s, abs_nonneg s]
  have hes : Integrable (fun x => ∑ b : Fin 3, e b x ^ 2) μ :=
    integrable_finsetSum _ fun b _ => he b
  have hdom : Integrable (fun x => 3 * r + (1 + r⁻¹) * ∑ b : Fin 3, e b x ^ 2) μ :=
    (integrable_const _).fun_add (hes.const_mul _)
  calc
    _ = |∫ x, w x * v x ^ 2 - z x * v x ^ 2 ∂μ| := by rw [integral_sub hw hz]
    _ ≤ ∫ x, |w x * v x ^ 2 - z x * v x ^ 2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C ^ 2 * B * (3 * r + (1 + r⁻¹) * ∑ b : Fin 3, e b x ^ 2) ∂μ := by
      apply integral_mono (hw.sub' hz).abs (hdom.const_mul _)
      intro x
      dsimp only
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (v x))]
      have hs : (∑ b : Fin 3, |e b x|) ≤ 3 * r + (1 + r⁻¹) * ∑ b : Fin 3, e b x ^ 2 := by
        simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum] using
          Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) => habs (e b x))
      calc
        _ ≤ (B * ∑ b : Fin 3, |e b x|) * C ^ 2 :=
          mul_le_mul (hcoeff x) (hv x) (sq_nonneg _)
            (mul_nonneg hB (Finset.sum_nonneg fun _ _ => abs_nonneg _))
        _ ≤ (B * (3 * r + (1 + r⁻¹) * ∑ b : Fin 3, e b x ^ 2)) * C ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hB) (sq_nonneg _)
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const _) (hes.const_mul _),
        integral_const, integral_const_mul, integral_finsetSum _ (fun b _ => he b)]
      simp only [smul_eq_mul]
      ring

#print axioms trialHybridCoefficient_control
#print axioms trial_weighted_square_coefficients_error

end PrimeGap182
