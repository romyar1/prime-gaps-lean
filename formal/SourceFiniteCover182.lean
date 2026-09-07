import SourceGroupCover182

/-! Actual row-to-event cover for finite marked fragments, with owner
reservations derived from the same weighted atoms. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace PrimeGap182

theorem source_outer_row_covered_finite (ref : Fin 2 × ℕ)
    (href : ref ∈ trialAllRowReferences) (X : Fin 39 → FiniteMeasure ℝ)
    (n : Fin 39 → ℕ) (x : (i : Fin 39) → Fin (n i) → ℝ)
    (hx : ∀ i a, (trialMesh : ℝ) < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : (i : Fin 39) × Fin (n i), Measure.dirac (x a.1 a.2))
    (hW : (trialWeightedMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : (i : Fin 39) × Fin (n i),
        ENNReal.ofReal (x a.1 a.2) • Measure.dirac (x a.1 a.2))
    (hShell : TrialShellDomain 0 X)
    (hfailure : ¬ TrialOuterRowAllowed (trialRowByReference ref) X) :
    ∃ j : Fin 60, TrialOuterCoverEvent j X := by
  let f : ((i : Fin 39) × Fin (n i)) → ℝ := fun a => x a.1 a.2
  have hδ : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have hcore : ((trialRowByReference ref).outerCore : ℝ) < trialTotalMass X :=
    lt_of_not_ge (fun h => hfailure (Or.inl h))
  obtain ⟨g, hrow, hl, hu, hcapX⟩ := trialOuterGroup_cap_of_row_core ref href X hShell hcore
  have hcap (a : (i : Fin 39) × Fin (n i)) : f a ≤ ((trialOuterGroup g).hardCap : ℝ) :=
    source_finite_mark_le_cap (X a.1) (trialMesh : ℝ) _ (x a.1)
      (fun b => hδ.trans (hx a.1 b)) (htail a.1) (hcapX a.1) a.2
  obtain ⟨_, a, hact, htwo, hbad⟩ := source_outer_failure_offender
    (trialRowByReference ref) X (trialMesh : ℝ) (trialOuterGroup g).hardCap f hδ
    (Rat.cast_le.mpr (trialRows_mesh_activation ref href).le) (fun a => hx a.1 a.2)
    hcap hN hW (trialOuterGroup_caps g ref hrow) hfailure
  obtain ⟨horder, hthreshold, hactivation⟩ := trialOuterGroup_linear_parameters g ref hrow
  have hactG : ((trialOuterGroup g).activation : ℝ) < f a :=
    (Rat.cast_le.mpr hactivation).trans_lt hact
  have hbadG : ((trialOuterGroup g).threshold : ℝ) <
      (∑ b ∈ Finset.univ.filter (fun b => f a ≤ f b), f b) +
        (((trialOuterGroup g).order : ℝ) - 1) * f a := by
    have hm : (trialSourceEffectiveOrder (trialRowByReference ref) : ℝ) ≤
        ((trialOuterGroup g).order : ℝ) := Rat.cast_le.mpr horder
    have hU : ((trialOuterGroup g).threshold : ℝ) ≤
        ((trialRowByReference ref).outerThreshold : ℝ) := Rat.cast_le.mpr hthreshold
    nlinarith only [hbad, hU, mul_le_mul_of_nonneg_right hm (hδ.trans (hx a.1 a.2)).le]
  have hbadTotal : ((trialRowByReference ref).outerThreshold : ℝ) <
      trialTotalMass X + ((trialSourceEffectiveOrder (trialRowByReference ref) : ℝ) - 1) * f a := by
    have ht := source_weighted_inclusive_tail X (trialMesh : ℝ) f
      (fun b => (hδ.trans (hx b.1 b.2)).le) hW (f a) (hx a.1 a.2)
    have hb := trialWeightedMeasure_tail_le_total X (f a)
    rw [ht] at hb
    linarith only [hbad, hb]
  obtain ⟨j, _, hD, hK, hOwner⟩ := source_group_cover (trialOuterInventory g) X f hN hW
    (fun a => hx a.1 a.2) hcap hl hu
    (fun j _ hlow hupp => trialSourceDomain_outer_of_shell j X hShell hlow hupp)
    a hactG htwo hbadG (fun j hj hjbin =>
      sourceLow_clipped_radius_lt true _ _ (trialOuterLow_clipping g j hj) ref hrow
        (trialTotalMass X) (f a) hact hjbin.2 hl hcore hbadTotal)
  exact ⟨j, hD, hK, trialSourceOwnerEvent_of_marked_witness j X n x hx htail hOwner⟩

theorem source_inner_row_covered_finite (side : Fin 2) (ref : Fin 2 × ℕ)
    (href : ref ∈ trialLadderRowReferences side) (X : Fin 38 → FiniteMeasure ℝ)
    (n : Fin 38 → ℕ) (x : (i : Fin 38) → Fin (n i) → ℝ)
    (hx : ∀ i a, (trialMesh : ℝ) < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : (i : Fin 38) × Fin (n i), Measure.dirac (x a.1 a.2))
    (hW : (trialWeightedMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : (i : Fin 38) × Fin (n i),
        ENNReal.ofReal (x a.1 a.2) • Measure.dirac (x a.1 a.2))
    (hShell : TrialShellDomain (if side = 0 then 1 else 2) X)
    (hfailure : ¬ TrialInnerRowAllowed (trialRowByReference ref) X) :
    ∃ j : Fin 137, trialSourceInnerRole j = (if side = 0 then 1 else 2) ∧
      TrialInnerCoverEvent j X := by
  let f : ((i : Fin 38) × Fin (n i)) → ℝ := fun a => x a.1 a.2
  have hδ : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have horderR : (trialRowByReference ref).order ≠ 1 := fun h => hfailure (Or.inl h)
  have hcore : ((trialRowByReference ref).innerCore : ℝ) < trialTotalMass X :=
    lt_of_not_ge (fun h => hfailure (Or.inr (Or.inl h)))
  have hrefAll : ref ∈ trialAllRowReferences := by
    fin_cases side
    · exact List.mem_append_left _ href
    · exact List.mem_append_right _ href
  obtain ⟨g, hrow, hrole, hl, hu, hcapX⟩ :=
    trialInnerGroup_cap_of_row_core side ref href horderR X hShell hcore
  have hcap (a : (i : Fin 38) × Fin (n i)) : f a ≤ ((trialInnerGroup g).hardCap : ℝ) :=
    source_finite_mark_le_cap (X a.1) (trialMesh : ℝ) _ (x a.1)
      (fun b => hδ.trans (hx a.1 b)) (htail a.1) (hcapX a.1) a.2
  obtain ⟨_, _, a, hact, htwo, hbad⟩ := source_inner_failure_offender
    (trialRowByReference ref) X (trialMesh : ℝ) (trialInnerGroup g).hardCap f hδ
    (Rat.cast_le.mpr (trialRows_mesh_activation ref hrefAll).le) (fun a => hx a.1 a.2)
    hcap hN hW (trialInnerGroup_caps g ref hrow) hfailure
  obtain ⟨horder, hthreshold, hactivation⟩ := trialInnerGroup_linear_parameters g ref hrow
  have hactG : ((trialInnerGroup g).activation : ℝ) < f a :=
    (Rat.cast_le.mpr hactivation).trans_lt hact
  have hbadG : ((trialInnerGroup g).threshold : ℝ) <
      (∑ b ∈ Finset.univ.filter (fun b => f a ≤ f b), f b) +
        (((trialInnerGroup g).order : ℝ) - 1) * f a := by
    have hm : (trialSourceEffectiveOrder (trialRowByReference ref) : ℝ) ≤
        ((trialInnerGroup g).order : ℝ) := Rat.cast_le.mpr horder
    have hU : ((trialInnerGroup g).threshold : ℝ) ≤
        ((trialRowByReference ref).innerThreshold : ℝ) := Rat.cast_le.mpr hthreshold
    nlinarith only [hbad, hU, mul_le_mul_of_nonneg_right hm (hδ.trans (hx a.1 a.2)).le]
  have hbadTotal : ((trialRowByReference ref).innerThreshold : ℝ) <
      trialTotalMass X + ((trialSourceEffectiveOrder (trialRowByReference ref) : ℝ) - 1) * f a := by
    have ht := source_weighted_inclusive_tail X (trialMesh : ℝ) f
      (fun b => (hδ.trans (hx b.1 b.2)).le) hW (f a) (hx a.1 a.2)
    have hb := trialWeightedMeasure_tail_le_total X (f a)
    rw [ht] at hb
    linarith only [hbad, hb]
  obtain ⟨j, hj, hD, hK, _⟩ := source_group_cover (trialInnerInventory g) X f hN hW
    (fun a => hx a.1 a.2) hcap hl hu
    (trialInnerInventory_domain g X (hrole.symm ▸ hShell))
    a hactG htwo hbadG (fun j hj hjbin =>
      sourceLow_clipped_radius_lt false _ _ (trialInnerLow_clipping g j hj) ref hrow
        (trialTotalMass X) (f a) hact hjbin.2 hl hcore hbadTotal)
  have hjrole : trialSourceInnerRole j = (if side = 0 then 1 else 2) := by
    apply Eq.trans _ hrole
    rcases hj with rfl | hj | hj
    · exact (trialInnerBins_role g).1
    · exact (trialInnerBins_role g).2.1 j hj
    · exact (trialInnerBins_role g).2.2 j hj
  exact ⟨j, hjrole, hD, hK⟩

set_option maxRecDepth 10000 in
theorem source_subtraction_row_covered_finite (X : Fin 38 → FiniteMeasure ℝ)
    (n : Fin 38 → ℕ) (x : (i : Fin 38) → Fin (n i) → ℝ)
    (hx : ∀ i a, (trialMesh : ℝ) < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : (i : Fin 38) × Fin (n i), Measure.dirac (x a.1 a.2))
    (hW : (trialWeightedMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : (i : Fin 38) × Fin (n i),
        ENNReal.ofReal (x a.1 a.2) • Measure.dirac (x a.1 a.2))
    (hShell : TrialShellDomain 3 X)
    (hfailure : ¬ TrialOuterRowAllowed trialSubtractionSourceRow X) :
    ∃ j : Fin 137, trialSourceInnerRole j = 3 ∧ TrialInnerCoverEvent j X := by
  let f : ((i : Fin 38) × Fin (n i)) → ℝ := fun a => x a.1 a.2
  have hδ : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  obtain ⟨hcoreEq, hactEq, hUeq, hmEq, hcompatible, hLowEq⟩ := trialSubtractionGroup_geometry
  have hcore : (trialSubtractionSourceRow.outerCore : ℝ) < trialTotalMass X :=
    lt_of_not_ge (fun h => hfailure (Or.inl h))
  have hl : ((trialInnerGroup 4).lowerRadius : ℝ) < trialTotalMass X := by
    simpa only [hcoreEq] using hcore
  have hu : trialTotalMass X ≤ ((trialInnerGroup 4).upperRadius : ℝ) :=
    sourceShell_total_le 3 _ trialSourceGroups_shell_upper.2.2 X hShell
  have hcapX : TrialCapAllowed (trialInnerGroup 4).hardCap X := by
    apply trialSourceDomain_group_cap _ (trialSourceGroups_piece_caps.2 4) X
    apply trialSourceDomain_inner_of_shell (trialInnerHighBin 4) X _ hl hu
    exact (trialInnerBins_role 4).1.symm ▸ hShell
  have hcap (a : (i : Fin 38) × Fin (n i)) : f a ≤ ((trialInnerGroup 4).hardCap : ℝ) :=
    source_finite_mark_le_cap (X a.1) (trialMesh : ℝ) _ (x a.1)
      (fun b => hδ.trans (hx a.1 b)) (htail a.1) (hcapX a.1) a.2
  have hactδ : trialMesh ≤ trialSubtractionSourceRow.activation := by decide +kernel
  obtain ⟨_, a, hact, htwo, hbad⟩ := source_outer_failure_offender
    trialSubtractionSourceRow X (trialMesh : ℝ) (trialInnerGroup 4).hardCap f hδ
    (Rat.cast_le.mpr hactδ) (fun a => hx a.1 a.2) hcap hN hW hcompatible hfailure
  obtain ⟨j, hj, hD, hK, _⟩ := source_group_cover (trialInnerInventory 4) X f hN hW
    (fun a => hx a.1 a.2) hcap hl hu (trialInnerInventory_domain 4 X hShell)
    a (by
      change ((trialInnerGroup 4).activation : ℝ) < f a
      rw [hactEq]
      exact hact) htwo
    (by
      change ((trialInnerGroup 4).threshold : ℝ) <
        (∑ b ∈ Finset.univ.filter (fun b => f a ≤ f b), f b) +
          (((trialInnerGroup 4).order : ℝ) - 1) * f a
      rw [hUeq, hmEq]
      exact hbad)
    (fun j hj _ => by
      change ((trialInnerCertificates j).cover.lowerRadius : ℝ) < trialTotalMass X
      rw [hLowEq j hj]
      exact hl)
  have hjrole : trialSourceInnerRole j = 3 := by
    rcases hj with rfl | hj | hj
    · exact (trialInnerBins_role 4).1
    · exact (trialInnerBins_role 4).2.1 j hj
    · exact (trialInnerBins_role 4).2.2 j hj
  exact ⟨j, hjrole, hD, hK⟩

#print axioms source_outer_row_covered_finite
#print axioms source_inner_row_covered_finite
#print axioms source_subtraction_row_covered_finite

end PrimeGap182
