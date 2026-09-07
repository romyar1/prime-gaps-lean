import SourcePairDense182
import SourceArraySupport182

/-! Actual support-to-source inclusion for all six signed moment pairings.
The only input is the constructed smooth profile package. No dense source
membership or distribution estimate is assumed. -/

noncomputable section
open PrimeGap186 PrimeGap182Analytic Filter
open scoped BigOperators Topology

namespace PrimeGap182

theorem sievePair_integer_kinds : ∀ k : Fin 6, ∀ l r : Fin 4,
    l ∈ sieveRoleIntegerKinds (TrialSmoothProfiles182.sievePairLeft k) →
    r ∈ sieveRoleIntegerKinds (TrialSmoothProfiles182.sievePairRight k) →
    (k = 0 ∧ l = 0 ∧ r = 1) ∨
      (k = 2 ∧ l = 0 ∧ (r = 1 ∨ r = 2)) ∨
      ((l = 1 ∨ l = 2) ∧ (r = 1 ∨ r = 2)) ∨
      (k = 3 ∧ l = 3 ∧ (r = 1 ∨ r = 2)) := by
  decide +kernel

theorem trialInteger_pair_modulus (k : Fin 6) (l r : Fin 4)
    (hl : l ∈ sieveRoleIntegerKinds (TrialSmoothProfiles182.sievePairLeft k))
    (hr : r ∈ sieveRoleIntegerKinds (TrialSmoothProfiles182.sievePairRight k))
    (x : ℝ) (hx : 1 < x) (W D E : ℕ) (hW : 0 < W)
    (hWs : (W : ℝ) ≤ x ^ (trialPresieveExponent : ℝ))
    (hDW : D.Coprime W) (hEW : E.Coprime W)
    (ho : TrialIntegerSupport l (x ^ (trialRhoStar : ℝ)) D)
    (hi : TrialIntegerSupport r (x ^ (trialRhoStar : ℝ)) E) :
    TrialSupportedModulus182 (TrialSmoothProfiles182.sievePairWeight k) x (W.lcm (D.lcm E)) := by
  have henlarge {c : Fin 4} {N : ℕ} (hc : c = 1 ∨ c = 2)
      (h : TrialIntegerSupport c (x ^ (trialRhoStar : ℝ)) N) :
      TrialIntegerSupport 2 (x ^ (trialRhoStar : ℝ)) N := by
    rcases hc with rfl | rfl
    · exact h.base_to_enlarged
    · exact h
  rcases sievePair_integer_kinds k l r hl hr with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hr⟩ | ⟨hl, hr⟩ | ⟨rfl, rfl, hr⟩
  · rcases trialInteger_ladder_modulus 0 x hx W D E hW hWs hDW hEW ho hi with hb | hs
    · exact Or.inl hb
    · exact Or.inr (Or.inl ⟨rfl, hs⟩)
  · rcases trialInteger_ladder_modulus 1 x hx W D E hW hWs hDW hEW ho (henlarge hr hi) with hb | hs
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hs⟩))
  · rcases trialInteger_common_modulus x hx W D E hW hWs hDW hEW
      (henlarge hl ho) (henlarge hr hi) with hb | hs
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
  · rcases trialInteger_subtraction_modulus x hx W D E hW hWs hDW hEW ho (henlarge hr hi) with hb | hs
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))

theorem trial_presieve_small (H : Finset ℕ) :
    ∀ᶠ x : ℝ in atTop, (presievingModulus H x : ℝ) ≤ x ^ (trialPresieveExponent : ℝ) := by
  have hη : (0 : ℝ) < trialPresieveExponent := by norm_num [trialPresieveExponent]
  filter_upwards [PrimeGap182.Selberg.presieving_le_mul_log_eventually H 1 zero_lt_one,
    (isLittleO_log_rpow_atTop hη).eventuallyLE, eventually_ge_atTop (0 : ℝ)] with x hWlog hsmall hx
  exact (show (presievingModulus H x : ℝ) ≤ Real.log x by
      simpa only [one_mul] using hWlog).trans ((le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx _)] using hsmall))

namespace TrialSmoothProfiles182

theorem sieve_moduli_supported (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (x : ℝ) (hx : 1 < x)
    (hWs : (presievingModulus H x : ℝ) ≤ x ^ (trialPresieveExponent : ℝ))
    (i : Fin 39) (k : Fin 6) (q : ℕ)
    (hq : q ∈ selbergModuliSupport182 H x
      (P.sieveFaceArray H i (sievePairLeft k) x) (P.sieveFaceArray H i (sievePairRight k) x)) :
    TrialSupportedModulus182 (sievePairWeight k) x q := by
  classical
  obtain ⟨⟨d, e⟩, hde, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hmem, _hcompat, hd, he⟩ := Finset.mem_filter.mp hde
  obtain ⟨hdmem, hemem⟩ := Finset.mem_product.mp hmem
  have hDdata := erasedBandArray182_divisor_support_data H P.a i
    (P.sieveFacePart i (sievePairLeft k)) (P.sieveRootPart (sievePairLeft k)) x d hdmem
  have hEdata := erasedBandArray182_divisor_support_data H P.a i
    (P.sieveFacePart i (sievePairRight k)) (P.sieveRootPart (sievePairRight k)) x e hemem
  obtain ⟨l, hl, hD⟩ := P.sieveFaceArray_coefficient_source H i (sievePairLeft k) x hx d hd
  obtain ⟨r, hr, hE⟩ := P.sieveFaceArray_coefficient_source H i (sievePairRight k) x hx e he
  have hρ : selbergRho182 = (trialRhoStar : ℝ) := by norm_num [selbergRho182, trialRhoStar]
  rw [hρ] at hD hE
  exact trialInteger_pair_modulus k l r hl hr x hx (presievingModulus H x) (∏ j, d j) (∏ j, e j)
    (presieving_pos H x) hWs hDdata.2.1 hEdata.2.1 hD hE

theorem sieve_moduli_supported_eventually (P : TrialSmoothProfiles182) (H : Finset ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ i : Fin 39, ∀ k : Fin 6, ∀ q ∈ selbergModuliSupport182 H x
      (P.sieveFaceArray H i (sievePairLeft k) x) (P.sieveFaceArray H i (sievePairRight k) x),
      TrialSupportedModulus182 (sievePairWeight k) x q := by
  filter_upwards [trial_presieve_small H, eventually_gt_atTop (1 : ℝ)] with x hW hx
  exact P.sieve_moduli_supported H x hx hW

#print axioms sieve_moduli_supported
#print axioms sieve_moduli_supported_eventually

end TrialSmoothProfiles182

#print axioms sievePair_integer_kinds
#print axioms trialInteger_pair_modulus

end PrimeGap182
