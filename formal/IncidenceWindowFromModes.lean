import IncidenceWindow
import IncidenceModalBounds

/-!
# Common window theorem from explicit finite modal bounds

These theorems reuse the proved Poisson, decay, alias, and plateau arguments.
The hypotheses mention only the actual finite Gram and Fourier-mode matrices.
There is no assumed window estimate, no supplied asymptotic saving, and no axiom.
The actual incidence matrix and its affine progression satisfy these hypotheses
by the separately proved local identities.
-/

noncomputable section
namespace PrimeGap182Audit
open Matrix
open scoped BigOperators SchwartzMap FourierTransform ComplexOrder Matrix.Norms.L2Operator

section
variable {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
theorem incidenceSchwartzWindow_from_modes (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (hR : IncidenceModalBounds R)
    (u v : 𝓢(ℝ, ℂ)) (τ C₁ C₂ E₁ E₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hu : ∀ t, ‖𝓕 u t‖ ≤ C₁ * incidenceDecay E₁ t)
    (hv : ∀ t, ‖𝓕 v t‖ ≤ C₂ * incidenceDecay E₂ t)
    (w : ℤ × ℤ → ℝ) (hw0 : ∀ z, 0 ≤ w z)
    (hw : ∀ z, (w z : ℂ) = u (z.1 : ℝ) * v ((z.2 : ℝ) - τ * (z.1 : ℝ)))
    (c : ι → ℂ) :
    (∑' z : ℤ × ℤ, w z *
      ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
      ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)) *
        (C₁ * C₂) * (q.divisors.card : ℝ) *
        (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q))) *
          incidenceVectorEnergy c := by
  have hws := incidenceSchwartzWeight_summable u v τ w hw
  have hbase := incidenceLatticeEnergy_from_modes R hR w hws hw0 c
  have hd (ξ : ZMod q × ZMod q) :
      (∑' z : ℤ × ℤ, (w z : ℂ) * incidenceJointChar ξ (-incidenceIntegerResidue q z)) =
        ∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
          ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z := by
    rw [← incidencePoisson_sheared]
    apply tsum_congr
    intro z
    simp only [hw, incidenceJointChar_integer, incidenceShearedPhysical]
  simp only [hd] at hbase
  let P : ℝ := (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)
  let H (ξ : ZMod q × ZMod q) : ℝ :=
    ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
      ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
        Real.sqrt (incidenceFrequencyGCD ξ : ℝ)
  have hfactor :
      (∑ ξ ∈ (Finset.univ : Finset (ZMod q × ZMod q)).erase 0,
        ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
          ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
          (P * Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) =
        P * ∑ ξ ∈ Finset.univ.erase 0, H ξ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    dsimp [H]
    ring
  change _ ≤ ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
    ∑ ξ ∈ Finset.univ.erase 0,
      ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
        ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
          (P * Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) * incidenceVectorEnergy c at hbase
  rw [hfactor] at hbase
  have hbound := incidenceShearedAliases_gcd_bound (q := q) u v τ C₁ C₂ E₁ E₂
    hC₁ hC₂ hE₁ hE₂ hu hv
  calc
    _ ≤ ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        (P * ∑ ξ ∈ Finset.univ.erase 0, H ξ)) * incidenceVectorEnergy c := hbase
    _ ≤ ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        (P * ((C₁ * C₂) * (q.divisors.card : ℝ) *
          (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q))))) *
            incidenceVectorEnergy c := by
      apply mul_le_mul_of_nonneg_right _ (incidenceVectorEnergy_nonneg c)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hbound (by dsimp [P]; positivity)
    _ = _ := by simp only [P, mul_assoc]

end

set_option maxHeartbeats 1000000 in
theorem incidenceCompactProductWindow_from_modes
    (f g : 𝓢(ℝ, ℂ)) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (T₁ T₂ L₁ L₂ : ℝ) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hsf : Function.support f ⊆ Set.Icc (-T₁) T₁)
    (hsg : Function.support g ⊆ Set.Icc (-T₂) T₂)
    (hbf : ∀ x : ℝ, ‖f x‖ ≤ L₁ ∧ ‖deriv f x‖ ≤ L₁ ∧ ‖deriv (deriv f) x‖ ≤ L₁)
    (hbg : ∀ x : ℝ, ‖g x‖ ≤ L₂ ∧ ‖deriv g x‖ ≤ L₂ ∧ ‖deriv (deriv g) x‖ ≤ L₂)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q],
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ R : Matrix (ZMod q × ZMod q) ι ℂ,
      IncidenceModalBounds R → ∀ E₁ E₂ e₀ γ₀ τ : ℝ, 0 < E₁ → 0 < E₂ →
      ∀ c : ι → ℂ,
        (∑' z : ℤ × ℤ, incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ z *
          ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
          C * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨CM, hCM, hmass⟩ := incidenceScaledProductWeight_mass_bound f g hf hg
  obtain ⟨CS, hCS, hsub⟩ := incidence_prime_divisor_subpower η hη
  let K₁ : ℝ := 8 * T₁ * L₁
  let K₂ : ℝ := 8 * T₂ * L₂
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  let CE : ℝ := 8 * K₁ * K₂ * CS
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  refine ⟨16 * CM + CE, by positivity, ?_⟩
  intro q _ ι _ _ R hR E₁ E₂ e₀ γ₀ τ hE₁ hE₂ c
  let u := incidenceScaledSchwartz f E₁ e₀ hE₁.ne'
  let v := incidenceScaledSchwartz g E₂ γ₀ hE₂.ne'
  let w := incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ
  let err : ℝ := ((q : ℝ) ^ 2)⁻¹ *
    ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)) *
    ((K₁ * E₁) * (K₂ * E₂)) * (q.divisors.card : ℝ) *
    (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q))
  have hu : ∀ t, ‖𝓕 u t‖ ≤ (K₁ * E₁) * incidenceDecay E₁ t :=
    incidenceScaledSchwartz_fourier_bound f T₁ L₁ E₁ e₀ hT₁ hL₁ hE₁ hsf hbf
  have hv : ∀ t, ‖𝓕 v t‖ ≤ (K₂ * E₂) * incidenceDecay E₂ t :=
    incidenceScaledSchwartz_fourier_bound g T₂ L₂ E₂ γ₀ hT₂ hL₂ hE₂ hsg hbg
  have hbase : (∑' z : ℤ × ℤ, w z *
      ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
      ((∑' z, w z) + err) * incidenceVectorEnergy c :=
    incidenceSchwartzWindow_from_modes R hR u v τ (K₁ * E₁) (K₂ * E₂) E₁ E₂
      (mul_nonneg hK₁ hE₁.le) (mul_nonneg hK₂ hE₂.le) hE₁ hE₂ hu hv w
      (incidenceScaledProductWeight_nonneg f g hf hg E₁ E₂ e₀ γ₀ τ)
      (incidenceScaledProductWeight_cast f g hf hg E₁ E₂ e₀ γ₀ τ hE₁.ne' hE₂.ne') c
  have he : err ≤ CE * incidenceWindowScale η q E₁ E₂ :=
    incidenceWindowScale_error η q (NeZero.ne q) CS K₁ K₂ E₁ E₂
      hCS.le hK₁ hK₂ hE₁ hE₂ (hsub q (NeZero.ne q))
  have hm : (∑' z : ℤ × ℤ, w z) ≤ 16 * CM * incidenceWindowScale η q E₁ E₂ := by
    calc
      _ ≤ CM * (2 + 4 * E₁) * (2 + 4 * E₂) := hmass E₁ E₂ e₀ γ₀ τ hE₁ hE₂
      _ = CM * ((2 + 4 * E₁) * (2 + 4 * E₂)) := by ring
      _ ≤ CM * (16 * incidenceWindowScale η q E₁ E₂) :=
        mul_le_mul_of_nonneg_left
          (incidenceWindowScale_mass η hη q (NeZero.ne q) E₁ E₂ hE₁.le hE₂.le) hCM.le
      _ = _ := by ring
  calc
    _ ≤ ((∑' z, w z) + err) * incidenceVectorEnergy c := hbase
    _ ≤ (16 * CM * incidenceWindowScale η q E₁ E₂ +
        CE * incidenceWindowScale η q E₁ E₂) * incidenceVectorEnergy c :=
      mul_le_mul_of_nonneg_right (add_le_add hm he) (incidenceVectorEnergy_nonneg c)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem incidenceShearedBox_from_modes
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q],
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ R : Matrix (ZMod q × ZMod q) ι ℂ,
      IncidenceModalBounds R → ∀ E₁ E₂ e₀ γ₀ τ L : ℝ,
      0 < E₁ → 0 < E₂ → 0 ≤ L → ∀ w : ℤ × ℤ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀| ≤ E₂) →
      ∀ c : ι → ℂ,
        (∑' z : ℤ × ℤ, w z *
          ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
          C * L * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨f, Lf, hLf, hf, hfone, hfs, hfb⟩ := incidence_exists_plateau
  obtain ⟨C, hC, hwindow⟩ := incidenceCompactProductWindow_from_modes f f hf hf
    2 2 Lf Lf (by norm_num) (by norm_num) (le_trans zero_le_one hLf)
    (le_trans zero_le_one hLf) hfs hfs hfb hfb η hη
  refine ⟨C, hC, ?_⟩
  intro q _ ι _ _ R hR E₁ E₂ e₀ γ₀ τ L hE₁ hE₂ hL w hw0 hwL hws c
  let W := incidenceScaledProductWeight f f E₁ E₂ e₀ γ₀ τ
  have hW0 (z : ℤ × ℤ) : 0 ≤ W z :=
    incidenceScaledProductWeight_nonneg f f hf hf E₁ E₂ e₀ γ₀ τ z
  have hW := incidenceScaledProductWeight_summable f f hf hf E₁ E₂ e₀ γ₀ τ hE₁ hE₂
  have hdom (z : ℤ × ℤ) : w z ≤ L * W z := by
    by_cases hz : w z = 0
    · rw [hz]
      exact mul_nonneg hL (hW0 z)
    · have hr := hws z hz
      have hf₁ : f (((z.1 : ℝ) - e₀) / E₁) = 1 := hfone _ (by
        rw [abs_div, abs_of_pos hE₁]
        exact (div_le_one hE₁).mpr hr.1)
      have hf₂ : f (((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀) / E₂) = 1 := hfone _ (by
        rw [abs_div, abs_of_pos hE₂]
        exact (div_le_one hE₂).mpr hr.2)
      simpa only [W, incidenceScaledProductWeight, hf₁, hf₂, Complex.one_re, mul_one] using hwL z
  have hw : Summable w := Summable.of_nonneg_of_le hw0 hdom (hW.mul_left L)
  calc
    _ ≤ ∑' z : ℤ × ℤ, (L * W z) *
        ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2 :=
      (incidenceIntegerEnergy_summable (R) w hw c).tsum_le_tsum
        (fun z => mul_le_mul_of_nonneg_right (hdom z) (sq_nonneg _))
        (incidenceIntegerEnergy_summable (R) (fun z => L * W z)
          (hW.mul_left L) c)
    _ = L * ∑' z : ℤ × ℤ, W z *
        ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2 := by
      simp only [mul_assoc, tsum_mul_left]
    _ ≤ L * (C * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c) :=
      mul_le_mul_of_nonneg_left (hwindow q ι R hR E₁ E₂ e₀ γ₀ τ hE₁ hE₂ c) hL
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem incidenceCompactWindow_from_modes
    (η T L : ℝ) (hη : 0 < η) (hT : 1 ≤ T) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ × ℝ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |z.1| ≤ T ∧ |z.2| ≤ T) →
      ∀ q : ℕ, ∀ [NeZero q],
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ R : Matrix (ZMod q × ZMod q) ι ℂ,
      IncidenceModalBounds R →
      ∀ E₁ E₂ e₀ γ₀ τ : ℝ, 0 < E₁ → 0 < E₂ → ∀ c : ι → ℂ,
        (∑' z : ℤ × ℤ, incidenceContinuousWindow w E₁ E₂ e₀ γ₀ τ z *
          ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
          C * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨C₀, hC₀, hbox⟩ := incidenceShearedBox_from_modes η hη
  have hCL : 0 ≤ C₀ * L := mul_nonneg hC₀.le hL
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  refine ⟨1 + C₀ * L * T ^ 2, by positivity, ?_⟩
  intro w hw0 hwL hws q _ ι _ _ R hR E₁ E₂ e₀ γ₀ τ hE₁ hE₂ c
  let W := incidenceContinuousWindow w E₁ E₂ e₀ γ₀ τ
  have hshape (z : ℤ × ℤ) (hz : W z ≠ 0) :
      |(z.1 : ℝ) - e₀| ≤ T * E₁ ∧
      |(z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀| ≤ T * E₂ := by
    have hb := hws ((((z.1 : ℝ) - e₀) / E₁),
      (((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀) / E₂)) hz
    rw [abs_div, abs_of_pos hE₁, abs_div, abs_of_pos hE₂] at hb
    exact ⟨(div_le_iff₀ hE₁).mp hb.1, (div_le_iff₀ hE₂).mp hb.2⟩
  have hb := hbox q ι R hR (T * E₁) (T * E₂) e₀ γ₀ τ L
    (mul_pos hT0 hE₁) (mul_pos hT0 hE₂) hL W (fun z => hw0 _) (fun z => hwL _) hshape c
  calc
    _ ≤ C₀ * L * incidenceWindowScale η q (T * E₁) (T * E₂) * incidenceVectorEnergy c := hb
    _ ≤ C₀ * L * (T ^ 2 * incidenceWindowScale η q E₁ E₂) * incidenceVectorEnergy c :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (incidenceWindowScale_rescale η q T E₁ E₂ hT hE₁.le hE₂.le)
          hCL) (incidenceVectorEnergy_nonneg c)
    _ ≤ _ := by
      have hs := incidenceWindowScale_nonneg η q E₁ E₂ hE₁.le hE₂.le
      have he := incidenceVectorEnergy_nonneg c
      nlinarith [mul_nonneg hs he]

#print axioms incidenceSchwartzWindow_from_modes
#print axioms incidenceCompactProductWindow_from_modes
#print axioms incidenceShearedBox_from_modes
#print axioms incidenceCompactWindow_from_modes

end PrimeGap182Audit
