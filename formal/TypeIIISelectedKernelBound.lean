import TypeIIISelectedEstimate
import TypeIIISelectedCoefficientSupport
import TypeIIISelectedCauchy
import TypeIIIDyadicSelection

/-!
# A bound for the original selected Kloosterman sum

The left side is the actual weighted, signed modulus sum in the public Type III
reduction. Its Cauchy inequality and all squarefreeness and primitive-residue
conditions are proved, not hypotheses. Coefficients need bounds only on their
actual finite supports.
-/

open scoped BigOperators Classical ContDiff
open PrimeGap186 UniqueFactorizationMonoid

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

def selectedFrequencyRange (H : ℝ) : Finset ℤ :=
  (Finset.Icc (Int.ceil (-H)) (Int.floor H)).filter (fun ℓ => ℓ ≠ 0)

def ternaryDivisorWeight (ℓ : ℤ) : ℝ :=
  (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) ℓ.natAbs : ℝ)

def selectedKloostermanTerm (b : ℕ+) (B : ℕ)
    (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ)
    (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (d : ℕ+) (ℓ : ℤ) : ℂ :=
  if Int.gcd (((b : ℕ) : ℤ) * ℓ) ((d : ℕ) : ℤ) = 1 then
    η ((b : ℕ) * (d : ℕ)) *
      ∑ m ∈ M, if Int.gcd m (((b : ℕ) * (d : ℕ) : ℕ) : ℤ) = 1 then
        α m * normalizedKloosterman3Mod (d : ℕ)
          (((Units.map ((ZMod.castHom (Nat.dvd_mul_left (d : ℕ) (b : ℕ))
            (ZMod (d : ℕ))).toMonoidHom) (a d) : (ZMod (d : ℕ))ˣ) : ZMod (d : ℕ)) *
            (B : ZMod (d : ℕ)) * (ℓ : ZMod (d : ℕ)) * (m : ZMod (d : ℕ))⁻¹ *
            (((b : ℕ) : ZMod (d : ℕ))⁻¹) ^ 3)
      else 0
  else 0

def selectedKloostermanL1 (b : ℕ+) (B : ℕ) (D : Finset ℕ+)
    (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ)
    (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (H : ℝ) : ℝ :=
  weightedKernelL1 D (selectedFrequencyRange H) ternaryDivisorWeight
    (selectedKloostermanTerm b B a M η α)

theorem selectedKloostermanL1_nonneg (b : ℕ+) (B : ℕ) (D : Finset ℕ+)
    (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ)
    (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (H : ℝ) :
    0 ≤ selectedKloostermanL1 b B D a M η α H := by
  unfold selectedKloostermanL1 weightedKernelL1 ternaryDivisorWeight
  positivity

def selectedFirstMoment (H : ℝ) (Sset : Finset ℕ+) : ℝ :=
  ∑ s ∈ Sset, (1 / (s : ℝ)) * ∑ ℓ ∈ selectedFrequencyRange H, ternaryDivisorWeight ℓ ^ 2

def firstMomentLogBound (H S : ℝ) : ℝ :=
  2 * H * (1 + Real.log (max 1 H)) ^ 15 * (1 + Real.log S)

theorem selectedFirstMoment_le_log {H S : ℝ} (hH : 0 < H) (hS : 1 ≤ S)
    (Sset : Finset ℕ+) (hSset : ∀ s ∈ Sset, (s : ℝ) ≤ S) :
    selectedFirstMoment H Sset ≤ firstMomentLogBound H S :=
  typeIII_first_moment_le_log_bound H S hH hS Sset hSset

def selectedCommonResidue (b : ℕ+) (B : ℕ) (D : Finset ℕ+) (a₀ : ℤ) : ℤ :=
  let P : ℕ := ∏ d ∈ D, (d : ℕ)
  (((a₀ : ZMod P) * (B : ZMod P) * (((b : ℕ) : ZMod P)⁻¹) ^ 3).val : ℤ)

def selectedMomentScale (N R S H ε : ℝ) : ℝ :=
  (R * S) ^ ε * nonzeroSGScale N R S +
    H * (1 + 2 * S * R) ^ ε * (1 + N * (2 * R) ^ 3) ^ ε * zeroSGScale N R S

/-- The new five-term estimate for the original weighted Kloosterman sum. -/
theorem LocalFourierHypothesis.exists_selected_kernel_square_estimate
    {C : ℝ} (hC : 0 ≤ C) {D₀ p₀ : ℕ} (hlocal : LocalFourierHypothesis C D₀ p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (b : ℕ+) (b₁ b₂ b₃ : ℕ), 0 < b₁ → 0 < b₂ → 0 < b₃ →
      (b : ℕ) = (radical (b₁ * b₂ * b₃) : ℕ) →
    ∀ (D : Finset ℕ+), (∀ d ∈ D, Squarefree ((b : ℕ) * (d : ℕ))) →
    ∀ (ρ σ : ℕ+ → ℕ+), (∀ d ∈ D, d = ρ d * σ d) →
    ∀ (N R S : ℕ), 0 < N → 0 < R → 0 < S →
      (∀ d ∈ D, R ≤ (ρ d : ℕ) ∧ (ρ d : ℕ) ≤ 2 * R) →
      (∀ d ∈ D, (σ d : ℕ) ≤ S) →
    ∀ (a₀ : ℤ) (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ),
      (∀ d ∈ D, (a d : ZMod ((b : ℕ) * (d : ℕ))) = (a₀ : ZMod ((b : ℕ) * (d : ℕ)))) →
    ∀ (M : Finset ℤ), M ⊆ Finset.Ico 1 (1 + (N : ℤ)) →
    ∀ (η : ℕ → ℂ) (α : ℤ → ℂ) (E W T L H : ℝ),
      0 ≤ E → 0 ≤ W → 1 ≤ T → 0 ≤ L → 0 < H →
      (∀ d ∈ D, ‖η ((b : ℕ) * (d : ℕ))‖ ≤ E) → (∀ m ∈ M, ‖α m‖ ≤ W) →
    ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → (∀ t : ℝ, 0 ≤ ψ t) →
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, ψ t = 1) → Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      selectedKloostermanL1 b (b₁ * b₂ * b₃) D a M η α H ^ 2 ≤
        K * (T * L) * (E * W) ^ 2 * firstMomentLogBound H S *
          selectedMomentScale N R S H ε := by
  obtain ⟨K, hK, hprofile⟩ := hlocal.exists_selected_profile_estimate hC hε
  refine ⟨K, hK, ?_⟩
  intro b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb D hD ρ σ hfactor N R S hN hR hS hρ hσ
    a₀ a ha M hM η α E W T L H hE hW hT hL hH hη hα ψ hψ hψnonneg hψone hsupp hψbound
  let B : ℕ := b₁ * b₂ * b₃
  let Sset : Finset ℕ+ := D.image σ
  let Rs : ℕ+ → Finset ℕ+ := fun s => (D.filter (fun d => σ d = s)).image ρ
  let A : ℤ := selectedCommonResidue b B D a₀
  have hB : (0 : ℝ) < (B : ℝ) := by dsimp only [B]; positivity
  have hHb : (1 : ℝ) ^ (3 * (0 : ℝ) / 2) * (H * (B : ℝ)) / (B : ℝ) = H := by
    norm_num
    exact mul_div_cancel_right₀ H hB.ne'
  have hc := selected_factor_cauchy_profile_bound b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb D hD
    ρ σ hfactor a₀ a ha M η α N hM 1 (H * (B : ℝ)) 0 T (by norm_num)
    (mul_pos hH hB) hT ψ hψnonneg hψone hsupp
  obtain ⟨hT₁, _, _, _, hcs, hparts⟩ := hc
  change 0 ≤ selectedFirstMoment
    ((1 : ℝ) ^ (3 * (0 : ℝ) / 2) * (H * (B : ℝ)) / (B : ℝ)) Sset at hT₁
  rw [hHb] at hT₁
  change selectedKloostermanL1 b B D a M η α
      ((1 : ℝ) ^ (3 * (0 : ℝ) / 2) * (H * (B : ℝ)) / (B : ℝ)) ^ 2 ≤
    selectedFirstMoment ((1 : ℝ) ^ (3 * (0 : ℝ) / 2) * (H * (B : ℝ)) / (B : ℝ)) Sset *
      selectedProfileMass (b : ℕ) Sset Rs A M η α N T
        ((1 : ℝ) ^ (3 * (0 : ℝ) / 2) * (H * (B : ℝ)) / (B : ℝ)) ψ at hcs
  rw [hHb] at hcs
  have hSs : ∀ s ∈ Sset, (s : ℕ) ≤ S := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    exact hσ d hd
  have hRr : ∀ s ∈ Sset, ∀ r ∈ Rs s, R ≤ (r : ℕ) ∧ (r : ℕ) ≤ 2 * R := by
    intro s _ r hr
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hr
    exact hρ d (Finset.mem_filter.mp hd).1
  have hdata : ∀ s ∈ Sset, ∀ r₁ ∈ Rs s, ∀ r₂ ∈ Rs s,
      Squarefree (s : ℕ) ∧ Squarefree (r₁ : ℕ) ∧ Squarefree (r₂ : ℕ) ∧
      Nat.Coprime (s : ℕ) ((r₁ : ℕ) * (r₂ : ℕ)) ∧
      IsUnit (A : ZMod ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ))) := by
    intro s hs r₁ hr₁ r₂ hr₂
    exact (hparts s hs r₁ hr₁ r₂ hr₂).2.2
  let Q : Finset ℕ := D.image (fun d : ℕ+ => (b : ℕ) * (d : ℕ))
  have hQ : ∀ s ∈ Sset, ∀ r ∈ Rs s, (b : ℕ) * ((r : ℕ) * (s : ℕ)) ∈ Q := by
    intro s hs r hr
    have hd := (hparts s hs r hr r hr).1
    exact Finset.mem_image.mpr ⟨r * s, hd, rfl⟩
  have hηQ : ∀ q ∈ Q, ‖η q‖ ≤ E := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    exact hη d hd
  obtain ⟨η', hη', heq⟩ := selectedProfileMass_bounded_reduction (b : ℕ) Sset Rs A M η α N
    hM Q hQ E hE hηQ T H ψ
  have hmass := hprofile (b : ℕ) Sset Rs A M η' α N R S hN hR hSs hRr hdata
    E W T L H hE hW (zero_le_one.trans hT) hL hH hη' hα ψ hψ hsupp hψbound
  rw [heq] at hmass
  have hfirst := selectedFirstMoment_le_log hH
    (show (1 : ℝ) ≤ S by exact_mod_cast hS) Sset (by
      intro s hs
      exact_mod_cast hSs s hs)
  have hscale : 0 ≤ selectedMomentScale N R S H ε := by
    unfold selectedMomentScale nonzeroSGScale zeroSGScale
    positivity
  calc
    _ ≤ selectedFirstMoment H Sset * selectedProfileMass (b : ℕ) Sset Rs A M η α N T H ψ := hcs
    _ ≤ selectedFirstMoment H Sset *
        (K * (T * L) * (E * W) ^ 2 * selectedMomentScale N R S H ε) :=
      mul_le_mul_of_nonneg_left hmass hT₁
    _ ≤ firstMomentLogBound H S *
        (K * (T * L) * (E * W) ^ 2 * selectedMomentScale N R S H ε) :=
      mul_le_mul_of_nonneg_right hfirst (by positivity)
    _ = _ := by ring

#print axioms selectedKloostermanL1_nonneg
#print axioms LocalFourierHypothesis.exists_selected_kernel_square_estimate

end

end PrimeGap182.TypeIII
