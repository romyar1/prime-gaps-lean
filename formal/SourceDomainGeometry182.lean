import SourceBinGeometry182

/-! Actual shell-to-source-domain geometry, including whole-cell inward
conventions and every clipped low-source interval. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialSourceLastIndex (c : TrialSourceCoverData) : ℕ :=
  (c.pieces.getLastD ⟨0, 0, 0⟩).last

def TrialSourceDomainShape (c : TrialSourceCoverData) (role : Fin 5) : Prop :=
  0 < c.dimension ∧ c.pieces ≠ [] ∧
    c.pieces.IsChain (fun a b => a.last + 1 = b.first) ∧
    ((trialSourceFirstIndex c + c.dimension - 1 : ℕ) : ℚ) * trialMesh ≤ c.lowerRadius ∧
    (∀ g ∈ trialGridShells role,
      min (trialCellCount - 1) (min (g.upper - c.dimension) ⌊c.upperRadius / trialMesh⌋₊) ≤
        trialSourceLastIndex c) ∧
    (∀ p ∈ c.pieces, p.first ≤ p.last ∧
      ∀ g ∈ trialGridShells role,
        p.first + c.dimension ≤ g.upper → g.lower < p.last + c.dimension →
          (g.cap : ℚ) * trialMesh ≤ p.cap)

set_option maxRecDepth 10000 in
theorem trialOuterDomain_geometry : ∀ j : Fin 60,
    (trialOuterCertificates j).cover.dimension = 39 ∧
      TrialSourceDomainShape (trialOuterCertificates j).cover 0 := by
  unfold TrialSourceDomainShape
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerDomain_geometry : ∀ j : Fin 137,
    (trialInnerCertificates j).cover.dimension = 38 ∧
      TrialSourceDomainShape (trialInnerCertificates j).cover (trialSourceInnerRole j) := by
  unfold TrialSourceDomainShape
  decide +kernel

theorem trialTotalMass_cell_lower_bound {d : ℕ} (X : Fin d → FiniteMeasure ℝ) :
    (trialSourceCellSum X : ℝ) * (trialMesh : ℝ) ≤ trialTotalMass X := by
  have hh : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have heach (i : Fin d) : (trialCellIndex (X i) : ℝ) * (trialMesh : ℝ) ≤
      ((X i).mass : ℝ) := by
    exact (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (by positivity) hh.le))
  simpa only [trialSourceCellSum, trialTotalMass, Nat.cast_sum, Finset.sum_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => heach i)

theorem sourcePieces_cover (L : List TrialSourcePiece) :
    L.IsChain (fun a b => a.last + 1 = b.first) → L ≠ [] →
    ∀ n : ℕ, (L.headD ⟨0, 0, 0⟩).first ≤ n → n ≤ (L.getLastD ⟨0, 0, 0⟩).last →
      ∃ p ∈ L, p.first ≤ n ∧ n ≤ p.last := by
  induction L with
  | nil => intro _ hn; exact (hn rfl).elim
  | cons a L ih =>
    intro hc _ n hlo hhi
    cases L with
    | nil => exact ⟨a, by simp, by simpa using hlo, by simpa using hhi⟩
    | cons b L =>
      by_cases ha : n ≤ a.last
      · exact ⟨a, by simp, by simpa using hlo, ha⟩
      · have hab := (List.isChain_cons_cons.mp hc).1
        obtain ⟨p, hp, hpn⟩ := ih (List.isChain_cons_cons.mp hc).2 (by simp) n
          (by simpa using (show b.first ≤ n by omega)) (by simpa using hhi)
        exact ⟨p, List.mem_cons_of_mem a hp, hpn⟩

theorem sourceDomain_of_shell {d : ℕ} (c : TrialSourceCoverData) (role : Fin 5)
    (hshape : TrialSourceDomainShape c role) (X : Fin d → FiniteMeasure ℝ)
    (hd : d = c.dimension) (hShell : TrialShellDomain role X)
    (hLower : (c.lowerRadius : ℝ) < trialTotalMass X)
    (hUpper : trialTotalMass X ≤ (c.upperRadius : ℝ)) : TrialSourceDomain c X := by
  subst d
  let r := trialSourceCellSum X
  have hh : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have hcellLo := trialTotalMass_cell_lower_bound X
  have hcellHi := trialTotalMass_cell_bound X
  change trialTotalMass X ≤ ((r + c.dimension : ℕ) : ℝ) * (trialMesh : ℝ) at hcellHi
  have hclip : ((trialSourceFirstIndex c + c.dimension - 1 : ℕ) : ℝ) * (trialMesh : ℝ) ≤
      (c.lowerRadius : ℝ) := by exact_mod_cast hshape.2.2.2.1
  have hnat : trialSourceFirstIndex c + c.dimension - 1 < r + c.dimension := by
    suffices h : (((trialSourceFirstIndex c + c.dimension - 1 : ℕ) : ℝ)) <
        ((r + c.dimension : ℕ) : ℝ) from Nat.cast_lt.mp h
    have hmul := (hclip.trans_lt hLower).trans_le hcellHi
    nlinarith only [hmul, hh]
  have hfirst : trialSourceFirstIndex c ≤ r := by have := hshape.1; omega
  have hfloor : r ≤ ⌊c.upperRadius / trialMesh⌋₊ := by
    have hreal : (r : ℝ) ≤ (c.upperRadius : ℝ) / (trialMesh : ℝ) :=
      (le_div_iff₀ hh).mpr (hcellLo.trans hUpper)
    simpa only [← Rat.cast_div, trialNatFloor_ratCast] using Nat.le_floor hreal
  obtain ⟨g, hg, hgrid⟩ := (trialShellDomain_grid_iff role X).mp hShell
  change r < trialCellCount ∧ g.lower < r + c.dimension ∧
    r + c.dimension ≤ g.upper ∧ TrialCapAllowed ((g.cap : ℚ) * trialMesh) X at hgrid
  have hlast : r ≤ trialSourceLastIndex c := by
    apply le_trans _ (hshape.2.2.2.2.1 g hg)
    exact le_min (by omega) (le_min (by omega) hfloor)
  obtain ⟨p, hp, hpr, hrp⟩ := sourcePieces_cover c.pieces hshape.2.2.1 hshape.2.1 r hfirst hlast
  have hcap : (g.cap : ℚ) * trialMesh ≤ p.cap :=
    (hshape.2.2.2.2.2 p hp).2 g hg (by omega) (by omega)
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  exact ⟨rfl, i, hpr, hrp, trialCapAllowed_mono hcap hgrid.2.2.2⟩

theorem trialSourceDomain_outer_of_shell (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ)
    (hShell : TrialShellDomain 0 X)
    (hLower : ((trialOuterCertificates j).cover.lowerRadius : ℝ) < trialTotalMass X)
    (hUpper : trialTotalMass X ≤ ((trialOuterCertificates j).cover.upperRadius : ℝ)) :
    TrialSourceDomain (trialOuterCertificates j).cover X :=
  sourceDomain_of_shell _ 0 (trialOuterDomain_geometry j).2 X
    (trialOuterDomain_geometry j).1.symm hShell hLower hUpper

theorem trialSourceDomain_inner_of_shell (j : Fin 137) (X : Fin 38 → FiniteMeasure ℝ)
    (hShell : TrialShellDomain (trialSourceInnerRole j) X)
    (hLower : ((trialInnerCertificates j).cover.lowerRadius : ℝ) < trialTotalMass X)
    (hUpper : trialTotalMass X ≤ ((trialInnerCertificates j).cover.upperRadius : ℝ)) :
    TrialSourceDomain (trialInnerCertificates j).cover X :=
  sourceDomain_of_shell _ _ (trialInnerDomain_geometry j).2 X
    (trialInnerDomain_geometry j).1.symm hShell hLower hUpper

#print axioms trialSourceDomain_outer_of_shell
#print axioms trialSourceDomain_inner_of_shell
#print axioms trialOuterDomain_geometry
#print axioms trialInnerDomain_geometry

end PrimeGap182
