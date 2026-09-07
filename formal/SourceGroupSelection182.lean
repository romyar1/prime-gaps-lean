import SourceRowGeometry182

/-! Every failed actual row is routed to one of the literal radial groups. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

set_option maxRecDepth 10000 in
theorem trialRows_mesh_activation : ∀ ref ∈ trialAllRowReferences,
    trialMesh < (trialRowByReference ref).activation := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialOuterGroup_linear_parameters : ∀ g : Fin 2,
    ∀ ref ∈ (trialOuterGroup g).sourceRows,
      trialSourceEffectiveOrder (trialRowByReference ref) ≤ (trialOuterGroup g).order ∧
      (trialOuterGroup g).threshold ≤ (trialRowByReference ref).outerThreshold ∧
      (trialOuterGroup g).activation ≤ (trialRowByReference ref).activation := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerGroup_linear_parameters : ∀ g : Fin 5,
    ∀ ref ∈ (trialInnerGroup g).sourceRows,
      trialSourceEffectiveOrder (trialRowByReference ref) ≤ (trialInnerGroup g).order ∧
      (trialInnerGroup g).threshold ≤ (trialRowByReference ref).innerThreshold ∧
      (trialInnerGroup g).activation ≤ (trialRowByReference ref).activation := by
  decide +kernel

theorem trialInnerGroup_roles (side : Fin 2) :
    trialInnerGroupRole (trialInnerFirstGroup side) = (if side = 0 then 1 else 2) ∧
    trialInnerGroupRole (trialInnerSecondGroup side) = (if side = 0 then 1 else 2) := by
  fin_cases side <;> decide +kernel

theorem sourceShell_total_le {d : ℕ} (role : Fin 5) (B : ℚ)
    (hb : ∀ g ∈ trialGridShells role, (g.upper : ℚ) * trialMesh ≤ B)
    (X : Fin d → FiniteMeasure ℝ) (hShell : TrialShellDomain role X) :
    trialTotalMass X ≤ (B : ℝ) := by
  obtain ⟨g, hg, hgrid⟩ := (trialShellDomain_grid_iff role X).mp hShell
  have hh : (0 : ℝ) ≤ (trialMesh : ℝ) := (Rat.cast_pos.mpr trialMesh_pos).le
  have hi : (((∑ i, trialCellIndex (X i)) + d : ℕ) : ℝ) ≤ (g.upper : ℝ) :=
    Nat.cast_le.mpr hgrid.2.2.1
  have hgB : (g.upper : ℝ) * (trialMesh : ℝ) ≤ (B : ℝ) := by exact_mod_cast hb g hg
  exact (trialTotalMass_cell_bound X).trans ((mul_le_mul_of_nonneg_right hi hh).trans hgB)

theorem trialSourceDomain_group_cap {d : ℕ} (c : TrialSourceCoverData)
    (hc : ∀ p ∈ c.pieces, p.cap ≤ c.hardCap)
    (X : Fin d → FiniteMeasure ℝ) (hX : TrialSourceDomain c X) :
    TrialCapAllowed c.hardCap X := by
  obtain ⟨_, j, _, _, hj⟩ := hX
  exact trialCapAllowed_mono (hc _ (List.get_mem _ j)) hj

theorem trialOuterGroup_of_row_core (ref : Fin 2 × ℕ) (href : ref ∈ trialAllRowReferences)
    (X : Fin 39 → FiniteMeasure ℝ) (hShell : TrialShellDomain 0 X)
    (hcore : ((trialRowByReference ref).outerCore : ℝ) < trialTotalMass X) :
    ∃ g : Fin 2, ref ∈ (trialOuterGroup g).sourceRows ∧
      ((trialOuterGroup g).lowerRadius : ℝ) < trialTotalMass X ∧
      trialTotalMass X ≤ ((trialOuterGroup g).upperRadius : ℝ) := by
  obtain ⟨hlow, hfirst, hlast⟩ := trialOuterGroup_row_ranges.2 ref href
  by_cases hs : trialTotalMass X ≤ ((trialOuterGroup 0).upperRadius : ℝ)
  · refine ⟨0, ?_, (Rat.cast_le.mpr hlow).trans_lt hcore, hs⟩
    exact hfirst.resolve_right (fun h => not_lt_of_ge
      (hs.trans (Rat.cast_le.mpr h)) hcore)
  · refine ⟨1, hlast, ?_, sourceShell_total_le 0 _ trialSourceGroups_shell_upper.1 X hShell⟩
    rw [trialOuterGroup_row_ranges.1]
    exact lt_of_not_ge hs

theorem trialInnerGroup_of_row_core (side : Fin 2) (ref : Fin 2 × ℕ)
    (href : ref ∈ trialLadderRowReferences side)
    (horder : (trialRowByReference ref).order ≠ 1)
    (X : Fin 38 → FiniteMeasure ℝ)
    (hShell : TrialShellDomain (if side = 0 then 1 else 2) X)
    (hcore : ((trialRowByReference ref).innerCore : ℝ) < trialTotalMass X) :
    ∃ g : Fin 5, ref ∈ (trialInnerGroup g).sourceRows ∧
      trialInnerGroupRole g = (if side = 0 then 1 else 2) ∧
      ((trialInnerGroup g).lowerRadius : ℝ) < trialTotalMass X ∧
      trialTotalMass X ≤ ((trialInnerGroup g).upperRadius : ℝ) := by
  obtain ⟨hlow, hfirst, hlast⟩ := (trialInnerGroup_row_ranges side).2 ref href horder
  by_cases hs : trialTotalMass X ≤ ((trialInnerGroup (trialInnerFirstGroup side)).upperRadius : ℝ)
  · refine ⟨trialInnerFirstGroup side, ?_, (trialInnerGroup_roles side).1,
      (Rat.cast_le.mpr hlow).trans_lt hcore, hs⟩
    exact hfirst.resolve_right (fun h => not_lt_of_ge
      (hs.trans (Rat.cast_le.mpr h)) hcore)
  · refine ⟨trialInnerSecondGroup side, hlast, (trialInnerGroup_roles side).2, ?_, ?_⟩
    · rw [(trialInnerGroup_row_ranges side).1]
      exact lt_of_not_ge hs
    · apply sourceShell_total_le _ _ (trialSourceGroups_shell_upper.2.1 side) X
      simpa only [(trialInnerGroup_roles side).2] using hShell

theorem trialOuterGroup_cap_of_row_core (ref : Fin 2 × ℕ) (href : ref ∈ trialAllRowReferences)
    (X : Fin 39 → FiniteMeasure ℝ) (hShell : TrialShellDomain 0 X)
    (hcore : ((trialRowByReference ref).outerCore : ℝ) < trialTotalMass X) :
    ∃ g : Fin 2, ref ∈ (trialOuterGroup g).sourceRows ∧
      ((trialOuterGroup g).lowerRadius : ℝ) < trialTotalMass X ∧
      trialTotalMass X ≤ ((trialOuterGroup g).upperRadius : ℝ) ∧
      TrialCapAllowed (trialOuterGroup g).hardCap X := by
  obtain ⟨g, hr, hl, hu⟩ := trialOuterGroup_of_row_core ref href X hShell hcore
  refine ⟨g, hr, hl, hu, trialSourceDomain_group_cap _ (trialSourceGroups_piece_caps.1 g) X ?_⟩
  exact trialSourceDomain_outer_of_shell (trialOuterHighBin g) X hShell hl hu

theorem trialInnerGroup_cap_of_row_core (side : Fin 2) (ref : Fin 2 × ℕ)
    (href : ref ∈ trialLadderRowReferences side)
    (horder : (trialRowByReference ref).order ≠ 1)
    (X : Fin 38 → FiniteMeasure ℝ)
    (hShell : TrialShellDomain (if side = 0 then 1 else 2) X)
    (hcore : ((trialRowByReference ref).innerCore : ℝ) < trialTotalMass X) :
    ∃ g : Fin 5, ref ∈ (trialInnerGroup g).sourceRows ∧
      trialInnerGroupRole g = (if side = 0 then 1 else 2) ∧
      ((trialInnerGroup g).lowerRadius : ℝ) < trialTotalMass X ∧
      trialTotalMass X ≤ ((trialInnerGroup g).upperRadius : ℝ) ∧
      TrialCapAllowed (trialInnerGroup g).hardCap X := by
  obtain ⟨g, hr, hrole, hl, hu⟩ := trialInnerGroup_of_row_core side ref href horder X hShell hcore
  refine ⟨g, hr, hrole, hl, hu, trialSourceDomain_group_cap _
    (trialSourceGroups_piece_caps.2 g) X ?_⟩
  apply trialSourceDomain_inner_of_shell (trialInnerHighBin g) X _ hl hu
  simpa only [(trialInnerBins_role g).1, hrole] using hShell

#print axioms trialOuterGroup_cap_of_row_core
#print axioms trialInnerGroup_cap_of_row_core
#print axioms trialOuterGroup_linear_parameters
#print axioms trialInnerGroup_linear_parameters

end PrimeGap182
