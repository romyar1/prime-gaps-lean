import TypeIIIProfileCoordinates
import TypeIIISelectedGram
import TypeIIIGcdFinite
import TypeIIIFixedProfile

/-! The actual selected signed Gram blocks satisfy the new five-term second-moment bound. -/

open scoped BigOperators Classical ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

def selectedLeftRows (b : ℕ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ)
    (s g u _v : ℕ) : IntegerIntervalIndex 1 N → ℂ :=
  selectedRowCoefficient b (u * (s * g)) M η α N

def selectedRightRows (b : ℕ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ)
    (s g _u v : ℕ) : IntegerIntervalIndex 1 N → ℂ :=
  selectedRowCoefficient b (v * (s * g)) M η α N

theorem selectedGcdProfile_norm_eq_guarded (b : ℕ) (s r₁ r₂ : ℕ+) (a : ℤ)
    (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ) (T H : ℝ) (ψ : ℝ → ℝ)
    (hs : Squarefree (s : ℕ)) (h₁ : Squarefree (r₁ : ℕ)) (h₂ : Squarefree (r₂ : ℕ))
    (hcop : Nat.Coprime (s : ℕ) ((r₁ : ℕ) * (r₂ : ℕ)))
    (ha : IsUnit (a : ZMod ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ)))) :
    ‖selectedGcdProfile b s r₁ r₂ a M η α N T H ψ‖ =
      guardedProfilePairMass a N s (selectedGcd r₁ r₂) (selectedLeft r₁ r₂) (selectedRight r₁ r₂)
        (selectedLeftRows b M η α N s (selectedGcd r₁ r₂)
          (selectedLeft r₁ r₂) (selectedRight r₁ r₂))
        (selectedRightRows b M η α N s (selectedGcd r₁ r₂)
          (selectedLeft r₁ r₂) (selectedRight r₁ r₂)) T H 0 (fun t => (ψ t : ℂ)) := by
  obtain ⟨hw, haw, houter⟩ := selected_gcd_admissible s r₁ r₂ a hs h₁ h₂ hcop ha
  rw [guardedProfilePairMass_eq, ite_eq_left ⟨hw, haw⟩, ite_eq_left houter]
  rfl

theorem sum_pnat_le_nat_Icc (Sset : Finset ℕ+) (S : ℕ)
    (hS : ∀ s ∈ Sset, (s : ℕ) ≤ S) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ s ∈ Sset, f s) ≤ ∑ s ∈ Finset.Icc 1 S, f s := by
  have hsub : Sset.image PNat.val ⊆ Finset.Icc 1 S := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_Icc.mpr ⟨t.pos, hS t ht⟩
  calc
    _ = ∑ s ∈ Sset.image PNat.val, f s := (Finset.sum_image PNat.coe_injective.injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

/-- The selected signed profile mass is enlarged only after its entire signed inner
sum has been formed. Exact gcd coordinates preserve all arithmetic guards. -/
theorem selectedProfileMass_le_residual (b : ℕ) (Sset : Finset ℕ+)
    (Rs : ℕ+ → Finset ℕ+) (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N R S : ℕ) (hR : 0 < R) (hS : ∀ s ∈ Sset, (s : ℕ) ≤ S)
    (hRs : ∀ s ∈ Sset, ∀ r ∈ Rs s, R ≤ (r : ℕ) ∧ (r : ℕ) ≤ 2 * R)
    (hdata : ∀ s ∈ Sset, ∀ r₁ ∈ Rs s, ∀ r₂ ∈ Rs s,
      Squarefree (s : ℕ) ∧ Squarefree (r₁ : ℕ) ∧ Squarefree (r₂ : ℕ) ∧
      Nat.Coprime (s : ℕ) ((r₁ : ℕ) * (r₂ : ℕ)) ∧
      IsUnit (a : ZMod ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ))))
    (T H : ℝ) (ψ : ℝ → ℝ) :
    selectedProfileMass b Sset Rs a M η α N T H ψ ≤
      ∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
        (s : ℝ) * admissibleResidualProfileMass a N R s g
          (selectedLeftRows b M η α N s g) (selectedRightRows b M η α N s g)
          T H 0 (fun t => (ψ t : ℂ)) := by
  let F (s g u v : ℕ) : ℝ := (s : ℝ) * guardedProfilePairMass a N s g u v
    (selectedLeftRows b M η α N s g u v) (selectedRightRows b M η α N s g u v)
    T H 0 (fun t => (ψ t : ℂ))
  have hF (s g u v : ℕ) : 0 ≤ F s g u v := mul_nonneg (Nat.cast_nonneg s)
    (guardedProfilePairMass_nonneg _ _ _ _ _ _ _ _ _ _ _ _)
  have hpoint (s : ℕ+) (hs : s ∈ Sset) :
      (∑ r₁ ∈ Rs s, ∑ r₂ ∈ Rs s,
        (s : ℝ) * ‖selectedGcdProfile b s r₁ r₂ a M η α N T H ψ‖) ≤
      ∑ g ∈ Finset.Icc 1 (2 * R), (s : ℝ) * admissibleResidualProfileMass a N R s g
        (selectedLeftRows b M η α N s g) (selectedRightRows b M η α N s g)
        T H 0 (fun t => (ψ t : ℂ)) := by
    have hb := selected_pair_sum_le_gcd_residual R (Rs s) (hRs s hs)
      (fun r₁ r₂ => (s : ℝ) * ‖selectedGcdProfile b s r₁ r₂ a M η α N T H ψ‖)
      (F s) (fun g _ u _ v _ => hF s g u v) (by
        intro r₁ hr₁ r₂ hr₂
        obtain ⟨hsq, h₁, h₂, hcop, ha⟩ := hdata s hs r₁ hr₁ r₂ hr₂
        rw [selectedGcdProfile_norm_eq_guarded b s r₁ r₂ a M η α N T H ψ hsq h₁ h₂ hcop ha]
        exact le_rfl)
    apply hb.trans_eq
    apply Finset.sum_congr rfl
    intro g hg
    rw [admissibleResidualProfileMass_eq_sum a N R s g hR s.pos (Finset.mem_Icc.mp hg).1]
    simp only [F, Finset.mul_sum]
  unfold selectedProfileMass
  apply (Finset.sum_le_sum hpoint).trans
  apply sum_pnat_le_nat_Icc Sset S hS
    (fun s : ℕ => ∑ g ∈ Finset.Icc 1 (2 * R),
      (s : ℝ) * admissibleResidualProfileMass a N R s g
        (selectedLeftRows b M η α N s g) (selectedRightRows b M η α N s g)
        T H 0 (fun t => (ψ t : ℂ)))
  intro s
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (Nat.cast_nonneg s)
    (admissibleResidualProfileMass_nonneg _ _ _ _ _ _ _ _ _ _ _))

/-- A quantitative estimate for the actual selected Gram blocks, with the coefficient
support, arithmetic masks, profile, and every finite sum retained in the conclusion. -/
theorem LocalFourierHypothesis.exists_selected_profile_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : ℕ) (Sset : Finset ℕ+) (Rs : ℕ+ → Finset ℕ+)
      (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (N R S : ℕ),
      0 < N → 0 < R → (∀ s ∈ Sset, (s : ℕ) ≤ S) →
      (∀ s ∈ Sset, ∀ r ∈ Rs s, R ≤ (r : ℕ) ∧ (r : ℕ) ≤ 2 * R) →
      (∀ s ∈ Sset, ∀ r₁ ∈ Rs s, ∀ r₂ ∈ Rs s,
        Squarefree (s : ℕ) ∧ Squarefree (r₁ : ℕ) ∧ Squarefree (r₂ : ℕ) ∧
        Nat.Coprime (s : ℕ) ((r₁ : ℕ) * (r₂ : ℕ)) ∧
        IsUnit (a : ZMod ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ)))) →
      ∀ E W T L H : ℝ, 0 ≤ E → 0 ≤ W → 0 ≤ T → 0 ≤ L → 0 < H →
      (∀ d : ℕ, ‖η d‖ ≤ E) → (∀ m ∈ M, ‖α m‖ ≤ W) →
      ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      selectedProfileMass b Sset Rs a M η α N T H ψ ≤
        K * (T * L) * (E * W) ^ 2 *
          (((R : ℝ) * (S : ℝ)) ^ ε * nonzeroSGScale N R S +
            H * (1 + 2 * (S : ℝ) * (R : ℝ)) ^ ε *
              (1 + (N : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε * zeroSGScale N R S) := by
  obtain ⟨K, hK, hb⟩ := hlocal.exists_residual_profile_total_estimate hC hε
  refine ⟨K, hK, ?_⟩
  intro b Sset Rs a M η α N R S hN hR hS hRs hdata E W T L H hE hW hT hL hH hη hα
    ψ hψ hsupp hbound
  obtain ⟨hψc, hsuppc, hboundc⟩ := realProfile_complex_control ψ hψ T L hsupp hbound
  have hleft : ∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
      ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m,
        ‖selectedLeftRows b M η α N s g u v m‖ ≤ E * W := by
    intro s _ g _ u _ v _ m
    exact selectedRowCoefficient_norm_le b (u * (s * g)) M η α N E W (hη _) hW hα m
  have hright : ∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
      ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n,
        ‖selectedRightRows b M η α N s g u v n‖ ≤ E * W := by
    intro s _ g _ u _ v _ n
    exact selectedRowCoefficient_norm_le b (v * (s * g)) M η α N E W (hη _) hW hα n
  apply (selectedProfileMass_le_residual b Sset Rs a M η α N R S hR hS hRs hdata T H ψ).trans
  have hh := hb a N R S hN hR (E * W) (E * W) T L H 0
    (mul_nonneg hE hW) (mul_nonneg hE hW) hT hL hH
    (fun t => (ψ t : ℂ)) hψc hsuppc hboundc
    (selectedLeftRows b M η α N) (selectedRightRows b M η α N) hleft hright
  simpa only [pow_two] using hh

#print axioms selectedGcdProfile_norm_eq_guarded
#print axioms selectedProfileMass_le_residual
#print axioms LocalFourierHypothesis.exists_selected_profile_estimate

end

end PrimeGap182.TypeIII
