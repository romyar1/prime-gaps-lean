import IncidenceSourceProfile

/-!
# Uniform compact pullback of Schwartz profiles

Multiplication by a fixed compact smooth cutoff makes pullback along an
arbitrary fixed smooth real-valued map continuous on Schwartz space. The
proof supplies finite seminorm bounds, so Fourier separation constants
can be controlled uniformly for the actual source profile families.
-/

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem incidenceCompactPullback_bound (b : 𝓢(V, ℂ)) (hb : HasCompactSupport b)
    (P : V → ℝ) (hP : ContDiff ℝ ∞ P) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ℝ, ℂ), ∀ x : V,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => b z * f (P z)) x‖ ≤
        C * (Finset.range (n + 1)).sup (fun i => SchwartzMap.seminorm ℂ 0 i) f := by
  classical
  obtain ⟨R₀, hR₀⟩ := hb.exists_bound_of_continuousOn (continuous_id.continuousOn)
  let R : ℝ := 1 + |R₀|
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRx : ∀ x ∈ tsupport b, ‖x‖ ≤ R := fun x hx =>
    (hR₀ x hx).trans ((le_abs_self R₀).trans (by dsimp only [R]; linarith [abs_nonneg R₀]))
  let H : V → ℝ := fun x => ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i P x‖
  have hH : Continuous H := continuous_finsetSum _ (fun i _ =>
    (hP.continuous_iteratedFDeriv (by simp)).norm)
  obtain ⟨D₀, hD₀⟩ := hb.exists_bound_of_continuousOn hH.continuousOn
  let D : ℝ := 1 + |D₀|
  have hD : 1 ≤ D := by dsimp only [D]; linarith [abs_nonneg D₀]
  have hPx : ∀ x ∈ tsupport b, ∀ i ≤ n, ‖iteratedFDeriv ℝ i P x‖ ≤ D := by
    intro x hx i hi
    have hterm : ‖iteratedFDeriv ℝ i P x‖ ≤ H x := by
      change _ ≤ ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j P x‖
      exact Finset.single_le_sum (s := Finset.range (n + 1)) (a := i)
        (fun j _ => norm_nonneg (iteratedFDeriv ℝ j P x))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact hterm.trans ((le_abs_self (H x)).trans
      ((hD₀ x hx).trans ((le_abs_self D₀).trans (by dsimp only [D]; linarith [abs_nonneg D₀]))))
  let B : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ 0 i b
  have hB : 0 < B := by
    dsimp only [B]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  have hbB : ∀ i ≤ n, ∀ x : V, ‖iteratedFDeriv ℝ i b x‖ ≤ B := by
    intro i hi x
    have ht : SchwartzMap.seminorm ℂ 0 i b ≤
        ∑ j ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ 0 j b :=
      Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
    exact (b.norm_iteratedFDeriv_le_seminorm ℂ i x).trans
      (ht.trans (by dsimp only [B]; linarith))
  let C : ℝ := R ^ k * 2 ^ n * B * (n.factorial : ℝ) * D ^ n
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro f x
  let L : ℝ := (Finset.range (n + 1)).sup (fun i => SchwartzMap.seminorm ℂ 0 i) f
  have hL : 0 ≤ L := apply_nonneg _ _
  have hfL : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f (P x)‖ ≤ L := by
    intro i hi
    exact (f.norm_iteratedFDeriv_le_seminorm ℂ i (P x)).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (by omega)))
  have hmul := norm_iteratedFDeriv_mul_le (b.smooth ⊤) ((f.smooth ⊤).comp hP)
    x (n := n) (by simp)
  by_cases hx : x ∈ tsupport b
  · have hcomp : ∀ j ≤ n,
        ‖iteratedFDeriv ℝ j (fun z => f (P z)) x‖ ≤ (n.factorial : ℝ) * L * D ^ n := by
      intro j hj
      have hraw := norm_iteratedFDeriv_comp_le (f.smooth ⊤) hP (n := j) (by simp) x
        (fun i hi => hfL i (hi.trans hj)) (fun i hi hij =>
          (hPx x hx i (hij.trans hj)).trans (Bound.le_self_pow_of_pos hD hi))
      apply hraw.trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.factorial_le hj)) hL)
        (pow_le_pow_right₀ hD hj) (pow_nonneg (zero_le_one.trans hD) _)
        (mul_nonneg (Nat.cast_nonneg _) hL)
    have hprod : ‖iteratedFDeriv ℝ n (fun z => b z * f (P z)) x‖ ≤
        2 ^ n * B * ((n.factorial : ℝ) * L * D ^ n) := by
      apply hmul.trans
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B *
            ((n.factorial : ℝ) * L * D ^ n) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hbB i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) x) (Nat.cast_nonneg _))
            (hcomp (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hB.le)
        _ = _ := by
          simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow,
            Nat.cast_ofNat]
    calc
      _ ≤ R ^ k * (2 ^ n * B * ((n.factorial : ℝ) * L * D ^ n)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hRx x hx) k) hprod
          (norm_nonneg _) (pow_nonneg hR.le k)
      _ = C * L := by dsimp only [C]; ring
  · have hz : ∀ i : ℕ, iteratedFDeriv ℝ i b x = 0 := by
      intro i
      apply Function.notMem_support.mp
      exact fun hi => hx ((support_iteratedFDeriv_subset (𝕜 := ℝ) (f := (b : V → ℂ)) i) hi)
    simp only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hmul
    have hpz : ‖iteratedFDeriv ℝ n (fun z => b z * f (P z)) x‖ = 0 :=
      le_antisymm hmul (norm_nonneg _)
    rw [hpz, mul_zero]
    exact mul_nonneg (by dsimp only [C]; positivity) hL

/-- The actual compact pullback map, with continuity proved by the
finite derivative bounds above. -/
def incidenceCompactPullbackCLM (b : 𝓢(V, ℂ)) (hb : HasCompactSupport b)
    (P : V → ℝ) (hP : ContDiff ℝ ∞ P) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  SchwartzMap.mkCLM (fun f x => b x * f (P x))
    (fun f g x => by simp only [add_apply, mul_add])
    (fun a f x => by simp only [smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
    (fun f => (b.smooth ⊤).mul ((f.smooth ⊤).comp hP)) (by
      intro kn
      obtain ⟨C, hC, hbound⟩ := incidenceCompactPullback_bound b hb P hP kn.1 kn.2
      refine ⟨(Finset.range (kn.2 + 1)).image (fun j => (0, j)), C, hC.le, ?_⟩
      intro f x
      simpa only [Finset.sup_image, Function.comp_def, SchwartzMap.schwartzSeminormFamily_apply]
        using hbound f x)

theorem incidenceCompactPullbackCLM_apply (b : 𝓢(V, ℂ)) (hb : HasCompactSupport b)
    (P : V → ℝ) (hP : ContDiff ℝ ∞ P) (f : 𝓢(ℝ, ℂ)) (x : V) :
    incidenceCompactPullbackCLM b hb P hP f x = b x * f (P x) := rfl

#print axioms incidenceCompactPullback_bound
#print axioms incidenceCompactPullbackCLM
#print axioms incidenceCompactPullbackCLM_apply

end PrimeGap182Audit
