import SourceWeights182

/-! Finite marked-fragment tools for the actual 39-coordinate law.
The atom labels are retained even when locations or owner coordinates
coincide. Counts and owner mass bounds therefore include repeated owners. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace PrimeGap182

theorem trialProductMeasure_ae_finite_tail_elim
    (δ : ℝ) (hδ : 0 < δ) (d : ℕ)
    (P : (Fin d → FiniteMeasure ℝ) → Prop) (hP : MeasurableSet {X | P X})
    (hfinite : ∀ (Y : Fin d → FiniteMeasure ℝ) (n : Fin d → ℕ)
      (x : (i : Fin d) → Fin (n i) → ℝ),
      (∀ i, (Y i).restrict (Set.Ioc (0 : ℝ) δ) = Y i) →
      (∀ i a, δ < x i a ∧ x i a ≤ (trialLargestCap : ℝ)) →
      P (fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i))) :
    ∀ᵐ X ∂trialProductMeasure d, P X := by
  let κ : ℝ := trialLargestCap
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ)
  have hκ : 0 < κ := by norm_num [κ, trialLargestCap]
  let : IsProbabilityMeasure (PrimeGap186.fragmentLaw κ) :=
    PrimeGap186.fragmentLaw_isProbabilityMeasure κ
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  have hpi : trialProductMeasure d =
      c ^ d • Measure.pi (fun _ : Fin d => PrimeGap186.fragmentLaw κ) := by
    apply Measure.pi_eq
    intro S _
    rw [Measure.smul_apply, Measure.pi_pi]
    change c ^ d * (∏ i : Fin d, PrimeGap186.fragmentLaw κ (S i)) =
      ∏ i : Fin d, c * PrimeGap186.fragmentLaw κ (S i)
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpi]
  exact Measure.ae_smul_measure
    (PrimeGap186.fragmentLaw_ae_finite_tail_elim κ δ hκ hδ d P hP hfinite) (c ^ d)

theorem source_finite_atoms_restrict {ι : Type*} [Fintype ι]
    (N : Measure ℝ) (δ : ℝ) (f : ι → ℝ)
    (hN : N.restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (S : Set ℝ) (hS : S ⊆ Set.Ioi δ) :
    N.restrict S = ∑ a : ι, if f a ∈ S then Measure.dirac (f a) else 0 := by
  classical
  calc
    _ = (N.restrict (Set.Ioi δ)).restrict S :=
      (Measure.restrict_restrict_of_subset hS).symm
    _ = _ := by
      rw [hN, ← Measure.restrictₗ_apply, map_sum]
      simp only [Measure.restrictₗ_apply]
      exact Finset.sum_congr rfl (fun a _ => restrict_dirac)

theorem source_finite_atoms_count {ι : Type*} [Fintype ι]
    (N : Measure ℝ) (δ : ℝ) (f : ι → ℝ)
    (hN : N.restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (S : Set ℝ) (hS : S ⊆ Set.Ioi δ) :
    N S = ((Finset.univ.filter (fun a : ι => f a ∈ S)).card : ℝ≥0∞) := by
  classical
  simpa [Measure.finsetSum_apply, apply_ite, ite_apply] using
      congrArg (fun μ : Measure ℝ => μ Set.univ) (source_finite_atoms_restrict N δ f hN S hS)

theorem source_finite_atoms_count_real {ι : Type*} [Fintype ι]
    (N : Measure ℝ) (δ : ℝ) (f : ι → ℝ)
    (hN : N.restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (S : Set ℝ) (hS : S ⊆ Set.Ioi δ) :
    N.real S = ((Finset.univ.filter (fun a : ι => f a ∈ S)).card : ℝ) := by
  classical
  rw [measureReal_def, source_finite_atoms_count N δ f hN S hS, ENNReal.toReal_natCast]

theorem source_finite_atoms_integral {ι : Type*} [Fintype ι]
    (N : Measure ℝ) (δ : ℝ) (f : ι → ℝ)
    (hN : N.restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (S : Set ℝ) (hS : S ⊆ Set.Ioi δ) (F : ℝ → ℝ) :
    (∫ q : ℝ in S, F q ∂N) = ∑ a : ι, if f a ∈ S then F (f a) else 0 := by
  classical
  rw [source_finite_atoms_restrict N δ f hN S hS,
    integral_finsetSum_measure (s := (Finset.univ : Finset ι))]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a ∈ S <;> simp only [ha, ite_true, ite_false, integral_dirac,
      integral_zero_measure]
  · intro a _
    by_cases ha : f a ∈ S
    · simp only [ha, ite_true]
      exact integrable_dirac (by simp)
    · simp only [ha, ite_false]
      exact integrable_zero_measure

theorem source_finite_atoms_integral_one_le {ι : Type*} [Fintype ι]
    (N : Measure ℝ) (δ : ℝ) (f : ι → ℝ)
    (hN : N.restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (S : Set ℝ) (hS : S ⊆ Set.Ioi δ) (F : ℝ → ℝ)
    (hF : ∀ q, 0 ≤ F q) (a : ι) (ha : f a ∈ S) (hFa : 1 ≤ F (f a)) :
    1 ≤ ∫ q : ℝ in S, F q ∂N := by
  classical
  rw [source_finite_atoms_integral N δ f hN S hS F]
  apply hFa.trans
  have hnon : ∀ b ∈ (Finset.univ : Finset ι),
      (0 : ℝ) ≤ if f b ∈ S then F (f b) else 0 := by
    intro b _
    split_ifs
    · exact hF _
    · exact le_rfl
  simpa only [ha, ite_true] using Finset.single_le_sum hnon (Finset.mem_univ a)

theorem source_finite_atoms_mass_le {ι : Type*} [Fintype ι]
    (X : FiniteMeasure ℝ) (δ : ℝ) (hδ : 0 < δ) (f : ι → ℝ)
    (hf : ∀ a, δ < f a)
    (htail : (X : Measure ℝ).restrict (Set.Ioi δ) =
      ∑ a : ι, ENNReal.ofReal (f a) • Measure.dirac (f a)) :
    (∑ a : ι, f a) ≤ (X.mass : ℝ) := by
  have hreal := PrimeGap186.trial_finite_tail_measureReal X δ f htail
    (fun a => (hδ.trans (hf a)).le) (Set.Ioi δ) measurableSet_Ioi (fun _ h => h)
  simp only [Set.mem_Ioi, hf, ite_true] at hreal
  have hle : (X : Measure ℝ).real (Set.Ioi δ) ≤ (X : Measure ℝ).real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  rw [hreal] at hle
  simpa only [measureReal_def, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using hle

/-- Distinct atom labels may share an owner; the mass is reserved only once
per owner coordinate. -/
theorem source_finite_atoms_owner_mass {d : ℕ}
    (X : Fin d → FiniteMeasure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (n : Fin d → ℕ) (x : (i : Fin d) → Fin (n i) → ℝ)
    (hx : ∀ i a, δ < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi δ) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (H : Finset ((i : Fin d) × Fin (n i))) :
    (∑ a ∈ H, x a.1 a.2) ≤
      ∑ i ∈ H.image Sigma.fst, ((X i).mass : ℝ) := by
  classical
  let A := H.image Sigma.fst
  have hsub : H ⊆ A.sigma (fun i => (Finset.univ : Finset (Fin (n i)))) := by
    intro a ha
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ a ∈ A.sigma (fun i => (Finset.univ : Finset (Fin (n i)))), x a.1 a.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a _ _ => (hδ.trans (hx a.1 a.2)).le)
    _ = ∑ i ∈ A, ∑ a : Fin (n i), x i a := Finset.sum_sigma _ _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      source_finite_atoms_mass_le (X i) δ hδ (x i) (hx i) (htail i)

theorem trialSourceOwnerEvent_of_marked_mass (r : TrialOuterCertificateData)
    (X : Fin 39 → FiniteMeasure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (n : Fin 39 → ℕ) (x : (i : Fin 39) → Fin (n i) → ℝ)
    (hx : ∀ i a, δ < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi δ) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (H : Finset ((i : Fin 39) × Fin (n i))) (hH : H.Nonempty)
    (hcard : H.card ≤ r.maxOwners)
    (hmass : (r.ownerMass : ℝ) ≤ ∑ a ∈ H, x a.1 a.2) :
    TrialSourceOwnerEvent r X := by
  classical
  refine ⟨H.image Sigma.fst, (Finset.card_image_le).trans hcard, Or.inr ?_,
    hmass.trans (source_finite_atoms_owner_mass X δ hδ n x hx htail H)⟩
  exact Finset.card_pos.mpr (hH.image _)

theorem measurableSet_trialSourceOwnerEvent (r : TrialOuterCertificateData) :
    MeasurableSet {X : Fin 39 → FiniteMeasure ℝ | TrialSourceOwnerEvent r X} := by
  classical
  simp only [TrialSourceOwnerEvent, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro A
  by_cases hc : A.card ≤ r.maxOwners ∧ (r.maxOwners = 0 ∨ 0 < A.card)
  · simp only [hc, true_and]
    exact measurableSet_le measurable_const (Finset.measurable_sum _ fun i _ =>
      ((Measure.measurable_coe MeasurableSet.univ).comp
        (measurable_subtype_coe.comp (measurable_pi_apply i))).ennreal_toReal)
  · simp only [← and_assoc, hc, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

#print axioms trialProductMeasure_ae_finite_tail_elim
#print axioms source_finite_atoms_integral
#print axioms source_finite_atoms_owner_mass
#print axioms trialSourceOwnerEvent_of_marked_mass

end PrimeGap182
