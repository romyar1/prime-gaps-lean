import SourceFiniteAtoms182
import SourceEventData182

/-! Labelled finite-fragment witnesses for the positive source kernels and
their owner mass reservations. Atom labels, not coordinate labels, must be
distinct; several witnesses in one coordinate are fully included. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace PrimeGap182

theorem source_finite_atoms_measureReal_sum {ι : Type*} [Fintype ι]
    (N : Measure ℝ) (δ : ℝ) (f : ι → ℝ)
    (hN : N.restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (S : Set ℝ) (hS : S ⊆ Set.Ioi δ) :
    N.real S = ∑ a : ι, Set.indicator S (fun _ => (1 : ℝ)) (f a) := by
  classical
  rw [source_finite_atoms_count_real N δ f hN S hS]
  symm
  calc
    _ = ∑ a : ι, if f a ∈ S then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a ∈ S
      · rw [ite_eq_left ha]
        exact Set.indicator_of_mem (s := S) ha _
      · rw [ite_eq_right ha]
        exact Set.indicator_of_notMem (s := S) ha _
    _ = _ := Finset.sum_boole _ _

/-- A linear offender above the low split either supplies three high
fragments or a balanced largest-fragment pair. -/
theorem source_two_high_or_balanced_pair {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (m U split cap : ℝ) (hm : 0 < m)
    (hcap : ∀ a, f a ≤ cap) (hguard : cap + m * split ≤ U)
    (a : ι) (ha : split < f a)
    (htwo : 2 ≤ (Finset.univ.filter (fun b : ι => f a ≤ f b)).card)
    (hbad : U < (∑ b ∈ Finset.univ.filter (fun b : ι => f a ≤ f b), f b) +
      (m - 1) * f a) :
    3 ≤ (Finset.univ.filter (fun b : ι => split < f b)).card ∨
      ∃ b c : ι, b ≠ c ∧ (∀ u, f u ≤ f b) ∧ f c ≤ f b ∧ split < f c ∧
        U < f b + m * f c ∧ U / (m + 1) < f b ∧ split ≤ (U - f b) / m := by
  classical
  let H := Finset.univ.filter (fun b : ι => split < f b)
  let T := Finset.univ.filter (fun b : ι => f a ≤ f b)
  change 2 ≤ T.card at htwo
  have haH : a ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  have hTH : T ⊆ H := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.trans_le (Finset.mem_filter.mp hb).2⟩
  have htwoH : 2 ≤ H.card := htwo.trans (Finset.card_le_card hTH)
  by_cases hthree : 3 ≤ H.card
  · exact Or.inl hthree
  · apply Or.inr
    have hcard : H.card = 2 := by omega
    have hT : T = H := Finset.eq_of_subset_of_card_le hTH (by omega)
    obtain ⟨b, hb, hmax⟩ := H.exists_max_image f ⟨a, haH⟩
    obtain ⟨c, hc, hcb⟩ := H.exists_mem_ne (by omega) b
    have hbc : b ≠ c := hcb.symm
    have hpair : ({b, c} : Finset ι) = H :=
      Finset.eq_of_subset_of_card_le
        (Finset.insert_subset_iff.mpr ⟨hb, Finset.singleton_subset_iff.mpr hc⟩)
        (hcard.trans (Finset.card_pair hbc).symm).le
    have hcbValue : f c ≤ f b := hmax c hc
    have hac : f a ≤ f c := (Finset.mem_filter.mp (hT.symm ▸ hc : c ∈ T)).2
    have hacEq : f a = f c := by
      have hamem : a = b ∨ a = c := by
        simpa only [← hpair, Finset.mem_insert, Finset.mem_singleton] using haH
      rcases hamem with rfl | rfl
      · exact le_antisymm hac hcbValue
      · rfl
    change U < (∑ u ∈ T, f u) + (m - 1) * f a at hbad
    rw [hT, ← hpair, Finset.sum_pair hbc, hacEq] at hbad
    have hbalanced : U < f b + m * f c := by nlinarith only [hbad]
    have hglobal (u : ι) : f u ≤ f b := by
      by_cases hu : split < f u
      · exact hmax u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      · exact (le_of_not_gt hu).trans (Finset.mem_filter.mp hb).2.le
    refine ⟨b, c, hbc, hglobal, hcbValue, (Finset.mem_filter.mp hc).2,
      hbalanced, ?_, ?_⟩
    · apply (div_lt_iff₀ (by linarith : 0 < m + 1)).mpr
      nlinarith only [hbalanced, mul_le_mul_of_nonneg_left hcbValue hm.le]
    · apply (le_div_iff₀ hm).mpr
      linarith only [hguard, hcap b]

theorem trialSource_low_unmasked_one_le {d : ℕ}
    (c : TrialSourceCoverData) (X : Fin d → FiniteMeasure ℝ)
    (hkind : c.kind = .low) (hθ : (0 : ℝ) ≤ (c.slope : ℝ))
    (hcount : 1 ≤ (trialSourceCountMeasure X).real (Set.Ioc (c.low : ℝ) (c.high : ℝ)))
    (hphase : 0 ≤ trialTotalMass X + ((c.order : ℝ) - 1) * (c.witnessUpper : ℝ) -
      (c.threshold : ℝ) - trialSourceSmallMass c X) :
    1 ≤ trialSourceUnmasked c X := by
  simp only [trialSourceUnmasked, hkind]
  exact one_le_mul_of_one_le_of_one_le hcount
    (Real.one_le_exp_iff.mpr (mul_nonneg hθ hphase))

theorem trialSource_rank_unmasked_one_le {d : ℕ} {ι : Type*} [Fintype ι]
    (c : TrialSourceCoverData) (X : Fin d → FiniteMeasure ℝ)
    (hkind : c.kind = .rankTwo) (δ : ℝ) (f : ι → ℝ)
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi δ) =
      ∑ a : ι, Measure.dirac (f a))
    (hlo : δ ≤ (c.low : ℝ)) (a b : ι) (hne : a ≠ b)
    (hqbin : f a ∈ Set.Ioc (c.low : ℝ) (c.high : ℝ))
    (hmax : ∀ u, f u ≤ f a) (hbq : f b ≤ f a)
    (hcut : δ ≤ ((c.threshold : ℝ) - f a) / (c.order : ℝ))
    (hpair : ((c.threshold : ℝ) - f a) / (c.order : ℝ) < f b) :
    1 ≤ trialSourceUnmasked c X := by
  classical
  let N := trialSourceCountMeasure X
  let q := f a
  let cut := ((c.threshold : ℝ) - q) / (c.order : ℝ)
  have hq : δ < q := hlo.trans_lt hqbin.1
  have htail : N (Set.Ioi q) = 0 := by
    rw [← Measure.restrict_eq_self N (Set.Ioi_subset_Ioi hq.le), hN,
      Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro u _
    rw [Measure.dirac_apply' _ measurableSet_Ioi]
    exact Set.indicator_of_notMem (s := Set.Ioi q) (not_lt_of_ge (hmax u)) _
  have hwindow : (2 : ℝ) ≤ N.real (Set.Ioc cut q) := by
    rw [source_finite_atoms_measureReal_sum N δ f hN (Set.Ioc cut q)
      (fun _ hu => hcut.trans_lt hu.1)]
    calc
      2 = ∑ u ∈ ({a, b} : Finset ι), Set.indicator (Set.Ioc cut q) (fun _ => (1 : ℝ)) (f u) := by
        rw [Finset.sum_pair hne,
          Set.indicator_of_mem (s := Set.Ioc cut q) ⟨hpair.trans_le hbq, le_rfl⟩,
          Set.indicator_of_mem (s := Set.Ioc cut q) ⟨hpair, hbq⟩]
        norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ => by
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  let F : ℝ → ℝ := fun v =>
    if N (Set.Ioi v) = 0 ∧ (2 : ℝ) ≤
        N.real (Set.Ioc (((c.threshold : ℝ) - v) / (c.order : ℝ)) v)
      then 1 else 0
  have hF : ∀ v, 0 ≤ F v := by intro v; dsimp only [F]; split_ifs <;> norm_num
  have hFa : 1 ≤ F (f a) := by
    rw [show F (f a) = 1 from ite_eq_left ⟨htail, hwindow⟩]
  have h := source_finite_atoms_integral_one_le N δ f hN
    (Set.Ioc (c.low : ℝ) (c.high : ℝ)) (fun _ hu => hlo.trans_lt hu.1) F hF a hqbin hFa
  simpa only [trialSourceUnmasked, hkind, F, N] using h

theorem trialSource_high_unmasked_one_le {d : ℕ} {ι : Type*} [Fintype ι]
    (c : TrialSourceCoverData) (X : Fin d → FiniteMeasure ℝ)
    (hkind : c.kind = .high) (δ : ℝ) (f : ι → ℝ)
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi δ) =
      ∑ a : ι, Measure.dirac (f a))
    (hsplit : δ ≤ (c.split : ℝ))
    (hthree : 3 ≤ (Finset.univ.filter (fun a : ι => (c.split : ℝ) < f a)).card) :
    1 ≤ trialSourceUnmasked c X := by
  classical
  simp only [trialSourceUnmasked, hkind]
  rw [source_finite_atoms_count_real _ δ f hN _ (Set.Ioi_subset_Ioi hsplit)]
  simp only [Set.mem_Ioi, Nat.floor_natCast]
  exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos hthree))

theorem source_rank_pair_mass_bound (m U q p lo : ℝ)
    (hm : 1 ≤ m) (hlo : lo ≤ q) (hpair : U ≤ q + m * p) :
    (U + (m - 1) * lo) / m ≤ q + p := by
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hm)).mpr
  nlinarith only [hpair, mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hm)]

theorem trialSourceOwnerEvent_low (r : TrialOuterCertificateData)
    (hformula : TrialSourceOwnerFormula r) (hkind : r.cover.kind = .low)
    (X : Fin 39 → FiniteMeasure ℝ) : TrialSourceOwnerEvent r X := by
  have hf : r.maxOwners = 0 ∧ r.ownerMass = 0 := by
    simpa only [TrialSourceOwnerFormula, hkind, ite_true] using hformula
  refine ⟨∅, by simp only [Finset.card_empty, Nat.zero_le], Or.inl hf.1, ?_⟩
  simp only [Finset.sum_empty, hf.2, Rat.cast_zero, le_refl]

theorem trialSourceOwnerEvent_rank_pair (r : TrialOuterCertificateData)
    (hformula : TrialSourceOwnerFormula r) (hkind : r.cover.kind = .rankTwo)
    (hm : (1 : ℝ) ≤ (r.cover.order : ℝ))
    (X : Fin 39 → FiniteMeasure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (n : Fin 39 → ℕ) (x : (i : Fin 39) → Fin (n i) → ℝ)
    (hx : ∀ i a, δ < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi δ) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (a b : (i : Fin 39) × Fin (n i)) (hne : a ≠ b)
    (hlo : (r.cover.low : ℝ) ≤ x a.1 a.2)
    (hpair : (r.cover.threshold : ℝ) ≤
      x a.1 a.2 + (r.cover.order : ℝ) * x b.1 b.2) :
    TrialSourceOwnerEvent r X := by
  classical
  have hf : r.maxOwners = 2 ∧ r.ownerMass =
      (r.cover.threshold + (r.cover.order - 1) * r.cover.low) / r.cover.order := by
    simpa only [TrialSourceOwnerFormula, hkind, reduceCtorEq, ite_false,
      ite_true] using hformula
  apply trialSourceOwnerEvent_of_marked_mass r X δ hδ n x hx htail {a, b}
    ⟨a, by simp only [Finset.mem_insert, true_or]⟩
    (by simp only [Finset.card_pair hne, hf.1, le_refl])
  rw [Finset.sum_pair hne, hf.2]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_one]
  exact source_rank_pair_mass_bound _ _ _ _ _ hm hlo hpair

theorem trialSourceOwnerEvent_high (r : TrialOuterCertificateData)
    (hformula : TrialSourceOwnerFormula r) (hkind : r.cover.kind = .high)
    (X : Fin 39 → FiniteMeasure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (n : Fin 39 → ℕ) (x : (i : Fin 39) → Fin (n i) → ℝ)
    (hx : ∀ i a, δ < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi δ) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (hthree : 3 ≤ (Finset.univ.filter
      (fun a : (i : Fin 39) × Fin (n i) => (r.cover.split : ℝ) < x a.1 a.2)).card) :
    TrialSourceOwnerEvent r X := by
  classical
  have hf : r.maxOwners = 3 ∧ r.ownerMass = 3 * r.cover.split := by
    simpa only [TrialSourceOwnerFormula, hkind, reduceCtorEq, ite_false] using hformula
  obtain ⟨H, hHsub, hHcard⟩ := Finset.exists_subset_card_eq hthree
  have hH : H.Nonempty := Finset.card_pos.mp (by omega)
  apply trialSourceOwnerEvent_of_marked_mass r X δ hδ n x hx htail H hH
    (by simp only [hHcard, hf.1, le_refl])
  rw [hf.2, Rat.cast_mul, Rat.cast_ofNat]
  calc
    _ = ∑ _a ∈ H, (r.cover.split : ℝ) := by
      simp only [Finset.sum_const, hHcard, nsmul_eq_mul, Nat.cast_ofNat]
    _ ≤ _ := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp (hHsub ha)).2.le

#print axioms source_two_high_or_balanced_pair
#print axioms trialSource_rank_unmasked_one_le
#print axioms trialSource_high_unmasked_one_le
#print axioms trialSourceOwnerEvent_rank_pair
#print axioms trialSourceOwnerEvent_high

end PrimeGap182
