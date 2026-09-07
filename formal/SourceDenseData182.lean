import PhysicalSources182

/-! Exact rational geometry of the literal source ladders, including the
common inner source and the enlarged subtraction source.  No analytic
distribution statement or finite integral value is assumed here. -/

namespace PrimeGap182

def trialSourceRows (ν : Fin 2) : List TrialSourceRow :=
  if ν = 0 then trialOldSourceRows else trialNewSourceRows

def trialSourceInnerRadius (ν : Fin 2) : ℚ :=
  if ν = 0 then trialBaseRadius else trialEnlargedRadius

def TrialSourceRowGeometry (row : TrialSourceRow) (S T : ℚ) : Prop :=
  0 ≤ row.activation ∧ 0 ≤ row.outerThreshold ∧ 0 ≤ row.innerThreshold ∧
    0 ≤ row.plateau ∧ (row.order = 1 ∨ row.order = 2 ∨ row.order = 3) ∧
    row.outerCore ≤ row.lowerBand - T ∧ row.innerCore ≤ row.lowerBand - S ∧
    (if row.order ≤ 2 then
      row.outerThreshold ≤ row.lowerBand - T + row.activation ∧
      row.innerThreshold ≤ row.lowerBand - S + row.activation ∧
      (row.order = 1 → 2 * T ≤ row.lowerBand + row.activation) ∧
      (row.order = 2 → 2 * S - T ≤ row.lowerBand + row.activation ∧
        2 * T - S ≤ row.lowerBand + row.activation)
    else row.outerThreshold + row.innerThreshold ≤ row.lowerBand + row.activation)

instance (row : TrialSourceRow) (S T : ℚ) : Decidable (TrialSourceRowGeometry row S T) := by
  unfold TrialSourceRowGeometry
  infer_instance

/-- A finite chain of bands covers every value above `B` and at most `H`. -/
def TrialRowCoverage (B H : ℚ) : List TrialSourceRow → Prop
  | [] => H ≤ B
  | row :: rows => row.lowerBand ≤ B ∧ B ≤ row.upperBand ∧
      TrialRowCoverage row.upperBand H rows

instance (B H : ℚ) (rows : List TrialSourceRow) : Decidable (TrialRowCoverage B H rows) := by
  induction rows generalizing B with
  | nil => unfold TrialRowCoverage; infer_instance
  | cons row rows ih =>
    unfold TrialRowCoverage
    have := ih row.upperBand
    infer_instance

set_option maxRecDepth 4096 in
theorem trialSourceRows_geometry : ∀ ν : Fin 2, ∀ row ∈ trialSourceRows ν,
    TrialSourceRowGeometry row trialRadius (trialSourceInnerRadius ν) := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialSourceRows_cover : ∀ ν : Fin 2,
    TrialRowCoverage ((1 / 2) / trialRho) (trialRadius + trialSourceInnerRadius ν)
      (trialSourceRows ν) := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialSourceRows_parameter_data : ∀ ν : Fin 2, ∀ row ∈ trialSourceRows ν,
    0 < row.activation ∧ 0 < row.omega ∧ 0 < row.upperBand ∧
      row.delta = trialRho * row.activation ∧
      trialRho * row.upperBand = 1 / 2 + 2 * row.omega := by
  decide +kernel

def trialCommonSourceOmega : ℚ := 3 / 1000
def trialCommonSourceDelta : ℚ := 1 / 50
def trialCommonInnerRow : TrialSourceRow := trialNewSourceRows[14]'(by decide)

theorem trialCommonInnerRow_mem : trialCommonInnerRow ∈ trialNewSourceRows :=
  List.getElem_mem (by decide)

set_option maxRecDepth 4096 in
theorem trialCommonSource_geometry :
    let row := trialCommonInnerRow
    let B := (1 / 2) / trialRho
    let T := trialEnlargedRadius
    let ξ := trialCommonSourceDelta / trialRho
    row.order = 2 ∧ row.innerCore ≤ B - T ∧ row.activation ≤ ξ ∧
      row.innerThreshold ≤ B - T + ξ ∧ 0 ≤ B - T + ξ ∧ 0 < ξ ∧
      2 * T * trialRho < 1 / 2 + 2 * trialCommonSourceOmega := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialSubtractionSource_geometry :
    TrialSourceRowGeometry trialSubtractionSourceRow trialSubtractionRadius trialEnlargedRadius ∧
      0 < trialSubtractionSourceRow.activation ∧ 0 < trialSubtractionSourceRow.omega ∧
      0 < trialSubtractionSourceRow.upperBand ∧
      trialSubtractionSourceRow.delta = trialRho * trialSubtractionSourceRow.activation ∧
      trialRho * trialSubtractionSourceRow.upperBand = 1 / 2 + 2 * trialSubtractionSourceRow.omega ∧
      trialSubtractionRadius + trialEnlargedRadius ≤ trialSubtractionSourceRow.upperBand ∧
      trialCommonInnerRow.innerCore ≤ trialSubtractionSourceRow.innerCore ∧
      trialCommonInnerRow.activation ≤ trialSubtractionSourceRow.activation ∧
      trialCommonInnerRow.innerThreshold ≤ trialSubtractionSourceRow.innerThreshold := by
  decide +kernel

theorem TrialRowCoverage.exists_band {B H : ℚ} {rows : List TrialSourceRow}
    (h : TrialRowCoverage B H rows) (x : ℝ) (hx : (B : ℝ) < x) (hH : x ≤ (H : ℝ)) :
    ∃ row ∈ rows, (row.lowerBand : ℝ) < x ∧ x ≤ (row.upperBand : ℝ) := by
  induction rows generalizing B with
  | nil =>
    have h' : (H : ℝ) ≤ (B : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (hH.trans h')) hx |>.elim
  | cons row rows ih =>
    by_cases hb : x ≤ (row.upperBand : ℝ)
    · refine ⟨row, List.mem_cons_self, ?_, hb⟩
      exact (show (row.lowerBand : ℝ) ≤ (B : ℝ) by exact_mod_cast h.1).trans_lt hx
    · obtain ⟨r, hr, hl, hu⟩ := ih h.2.2 (lt_of_not_ge hb)
      exact ⟨r, List.mem_cons_of_mem row hr, hl, hu⟩

#print axioms trialSourceRows_geometry
#print axioms trialSourceRows_cover
#print axioms trialSourceRows_parameter_data
#print axioms trialCommonSource_geometry
#print axioms trialSubtractionSource_geometry
#print axioms TrialRowCoverage.exists_band

end PrimeGap182
