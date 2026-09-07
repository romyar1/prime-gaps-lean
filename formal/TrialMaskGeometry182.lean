import TrialCapGeometry182

/-! Exact inward grid masks and their nesting, derived from the literal shells. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

structure TrialGridShell where
  lower : ℕ
  upper : ℕ
  cap : ℕ
  deriving DecidableEq

def trialShellToGrid (s : TrialShell) : TrialGridShell :=
  ⟨⌊s.lower / trialMesh⌋₊, ⌊s.upper / trialMesh⌋₊, ⌊s.cap / trialMesh⌋₊⟩

def trialGridShells : Fin 5 → List TrialGridShell :=
  ![[⟨0, 352736, 246256⟩, ⟨352736, 376488, 196608⟩, ⟨376488, 393216, 186253⟩],
    [⟨0, 334291, 246256⟩, ⟨334291, 343201, 177542⟩, ⟨343201, 355085, 140306⟩],
    [⟨0, 336312, 246256⟩, ⟨336312, 343207, 179967⟩, ⟨343207, 359934, 141724⟩],
    [⟨0, 352736, 246256⟩, ⟨352736, 371709, 186491⟩],
    [⟨0, 393216, 246256⟩]]

theorem trialGridShells_base : trialGridShells 1 =
    [⟨0, 334291, 246256⟩, ⟨334291, 343201, 177542⟩, ⟨343201, 355085, 140306⟩] := rfl

theorem trialGridShells_enlarged : trialGridShells 2 =
    [⟨0, 336312, 246256⟩, ⟨336312, 343207, 179967⟩, ⟨343207, 359934, 141724⟩] := rfl

theorem trialGridShells_exact (role : Fin 5) :
    (trialShells role).map trialShellToGrid = trialGridShells role := by
  fin_cases role <;> decide +kernel

theorem trialShell_grid_admissible (role : Fin 5) :
    ∀ s ∈ trialShells role, 0 ≤ s.lower ∧ 0 ≤ s.upper ∧
      ((trialShellToGrid s).cap : ℚ) * trialMesh = s.cap := by
  fin_cases role <;> decide +kernel

def TrialGridAllowed {d : ℕ} (g : TrialGridShell) (X : Fin d → FiniteMeasure ℝ) : Prop :=
  let r := ∑ i, trialCellIndex (X i)
  r < trialCellCount ∧ g.lower < r + d ∧ r + d ≤ g.upper ∧
    TrialCapAllowed ((g.cap : ℚ) * trialMesh) X

theorem trialShellAllowed_grid_iff {d : ℕ} (role : Fin 5) (s : TrialShell)
    (hs : s ∈ trialShells role) (X : Fin d → FiniteMeasure ℝ) :
    TrialShellAllowed s X ↔ TrialGridAllowed (trialShellToGrid s) X := by
  obtain ⟨hl, hu, hc⟩ := trialShell_grid_admissible role s hs
  dsimp only [TrialShellAllowed, TrialGridAllowed]
  rw [hc]
  simp only [trialShellToGrid]
  rw [Nat.floor_lt (div_nonneg hl trialMesh_pos.le),
    Nat.le_floor_iff (div_nonneg hu trialMesh_pos.le),
    div_lt_iff₀ trialMesh_pos, le_div_iff₀ trialMesh_pos]

theorem trialShellDomain_grid_iff {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) :
    TrialShellDomain role X ↔ ∃ g ∈ trialGridShells role, TrialGridAllowed g X := by
  constructor
  · rintro ⟨i, hi⟩
    have hs := List.get_mem (trialShells role) i
    refine ⟨trialShellToGrid ((trialShells role).get i), ?_,
      (trialShellAllowed_grid_iff role _ hs X).mp hi⟩
    rw [← trialGridShells_exact]
    exact List.mem_map.mpr ⟨_, hs, rfl⟩
  · rintro ⟨g, hg, hgood⟩
    rw [← trialGridShells_exact] at hg
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hs
    exact ⟨i, (trialShellAllowed_grid_iff role _ (List.get_mem _ i) X).mpr hgood⟩

private theorem trialBase_grid_logic (r : ℕ) (P : ℕ → Prop) :
    ((r < 393177 ∧ 0 < r + 38 ∧ r + 38 ≤ 334291 ∧ P 246256) ∨
      (r < 393177 ∧ 334291 < r + 38 ∧ r + 38 ≤ 343201 ∧ P 177542) ∨
      (r < 393177 ∧ 343201 < r + 38 ∧ r + 38 ≤ 355085 ∧ P 140306)) ↔
    r ≤ 355047 ∧ P (if r ≤ 334253 then 246256 else if r ≤ 343163 then 177542 else 140306) := by
  split_ifs <;>
    (by_cases h₁ : P 246256 <;> by_cases h₂ : P 177542 <;>
      by_cases h₃ : P 140306 <;> simp_all <;> omega)

private theorem trialEnlarged_grid_logic (r : ℕ) (P : ℕ → Prop) :
    ((r < 393177 ∧ 0 < r + 38 ∧ r + 38 ≤ 336312 ∧ P 246256) ∨
      (r < 393177 ∧ 336312 < r + 38 ∧ r + 38 ≤ 343207 ∧ P 179967) ∨
      (r < 393177 ∧ 343207 < r + 38 ∧ r + 38 ≤ 359934 ∧ P 141724)) ↔
    r ≤ 359896 ∧ P (if r ≤ 336274 then 246256 else if r ≤ 343169 then 179967 else 141724) := by
  split_ifs <;>
    (by_cases h₁ : P 246256 <;> by_cases h₂ : P 179967 <;>
      by_cases h₃ : P 141724 <;> simp_all <;> omega)

theorem trialBase_grid_iff (Y : Fin 38 → FiniteMeasure ℝ) :
    TrialShellDomain 1 Y ↔
      (∑ i, trialCellIndex (Y i)) ≤ 355047 ∧
      TrialCapAllowed (((if (∑ i, trialCellIndex (Y i)) ≤ 334253 then 246256
        else if (∑ i, trialCellIndex (Y i)) ≤ 343163 then 177542 else 140306 : ℕ) : ℚ) *
          trialMesh) Y := by
  rw [trialShellDomain_grid_iff]
  rw [trialGridShells_base]
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or, exists_eq_left]
  simpa only [TrialGridAllowed, trialCellCount_eq] using
    trialBase_grid_logic (∑ i, trialCellIndex (Y i))
      (fun c => TrialCapAllowed ((c : ℚ) * trialMesh) Y)

theorem trialEnlarged_grid_iff (Y : Fin 38 → FiniteMeasure ℝ) :
    TrialShellDomain 2 Y ↔
      (∑ i, trialCellIndex (Y i)) ≤ 359896 ∧
      TrialCapAllowed (((if (∑ i, trialCellIndex (Y i)) ≤ 336274 then 246256
        else if (∑ i, trialCellIndex (Y i)) ≤ 343169 then 179967 else 141724 : ℕ) : ℚ) *
          trialMesh) Y := by
  rw [trialShellDomain_grid_iff]
  rw [trialGridShells_enlarged]
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or, exists_eq_left]
  simpa only [TrialGridAllowed, trialCellCount_eq] using
    trialEnlarged_grid_logic (∑ i, trialCellIndex (Y i))
      (fun c => TrialCapAllowed ((c : ℚ) * trialMesh) Y)

theorem trialBase_subset_enlarged (Y : Fin 38 → FiniteMeasure ℝ) :
    TrialShellDomain 1 Y → TrialShellDomain 2 Y := by
  rw [trialBase_grid_iff, trialEnlarged_grid_iff]
  rintro ⟨hr, hcap⟩
  refine ⟨by omega, trialCapAllowed_mono ?_ hcap⟩
  apply mul_le_mul_of_nonneg_right _ trialMesh_pos.le
  exact_mod_cast (show
    (if (∑ i, trialCellIndex (Y i)) ≤ 334253 then 246256
      else if (∑ i, trialCellIndex (Y i)) ≤ 343163 then 177542 else 140306 : ℕ) ≤
    (if (∑ i, trialCellIndex (Y i)) ≤ 336274 then 246256
      else if (∑ i, trialCellIndex (Y i)) ≤ 343169 then 179967 else 141724 : ℕ) by
      split_ifs <;> omega)

theorem trialMask_base_le_enlarged (Y : Fin 38 → FiniteMeasure ℝ) :
    trialMask 1 Y ≤ trialMask 2 Y := by
  have h := trialBase_subset_enlarged Y
  unfold trialMask
  split_ifs <;> simp_all

#print axioms trialGridShells_exact
#print axioms trialShellDomain_grid_iff
#print axioms trialMask_base_le_enlarged

end PrimeGap182
