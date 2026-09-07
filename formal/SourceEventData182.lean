import SourceCountCertificate182
import PhysicalSources182

/-! Exact finite-data obligations used in the true-event source cover.
All rational inequalities below are checked by the Lean kernel. -/

namespace PrimeGap182

def TrialSourceMarkParameters (c : TrialSourceCoverData) : Prop :=
  trialMesh < c.low ∧ 1 ≤ c.order ∧ c.activation < c.split ∧
    c.hardCap + c.order * c.split ≤ c.threshold ∧
    c.split < c.threshold / (c.order + 1) ∧
    if c.kind = .low then c.low < c.high ∧ c.high ≤ c.witnessUpper ∧
        0 ≤ c.slope ∧ c.high ≤ c.split
    else if c.kind = .rankTwo then c.threshold / (c.order + 1) ≤ c.low ∧
        c.low < c.high ∧ c.high ≤ c.hardCap
    else c.low = c.split ∧ c.high = c.hardCap

set_option maxRecDepth 4096 in
theorem trialOuterMark_parameters : ∀ j : Fin 60,
    TrialSourceMarkParameters (trialOuterCertificates j).cover := by
  unfold TrialSourceMarkParameters
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialInnerMark_parameters : ∀ j : Fin 137,
    TrialSourceMarkParameters (trialInnerCertificates j).cover := by
  unfold TrialSourceMarkParameters
  decide +kernel

def TrialSourceOwnerFormula (r : TrialOuterCertificateData) : Prop :=
  if r.cover.kind = .low then r.maxOwners = 0 ∧ r.ownerMass = 0
  else if r.cover.kind = .rankTwo then r.maxOwners = 2 ∧
      r.ownerMass = (r.cover.threshold + (r.cover.order - 1) * r.cover.low) / r.cover.order
  else r.maxOwners = 3 ∧ r.ownerMass = 3 * r.cover.split

set_option maxRecDepth 4096 in
theorem trialOuterOwner_formula : ∀ j : Fin 60,
    TrialSourceOwnerFormula (trialOuterCertificates j) := by
  unfold TrialSourceOwnerFormula
  decide +kernel

def trialRowByReference (ref : Fin 2 × ℕ) : TrialSourceRow :=
  if ref.1 = 0 then trialOldSourceRows.getD ref.2 trialSubtractionSourceRow
  else trialNewSourceRows.getD ref.2 trialSubtractionSourceRow

def TrialSourceRowsCompatible (c : TrialSourceCoverData) : Prop :=
  ∀ ref ∈ c.sourceRows,
    ref.2 < (if ref.1 = 0 then trialOldSourceRows.length else trialNewSourceRows.length) ∧
    (let r := trialRowByReference ref;
      (if r.order ≤ 2 then (2 : ℚ) else 5 / 2) ≤ c.order ∧
        c.threshold ≤ (if c.family.val < 2 then r.outerThreshold else r.innerThreshold) ∧
        c.activation ≤ r.activation)

set_option maxRecDepth 4096 in
theorem trialOuterRows_compatible : ∀ j : Fin 60,
    TrialSourceRowsCompatible (trialOuterCertificates j).cover := by
  unfold TrialSourceRowsCompatible
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialInnerRows_compatible : ∀ j : Fin 137,
    TrialSourceRowsCompatible (trialInnerCertificates j).cover := by
  unfold TrialSourceRowsCompatible
  decide +kernel

#print axioms trialOuterMark_parameters
#print axioms trialInnerMark_parameters
#print axioms trialOuterOwner_formula
#print axioms trialOuterRows_compatible
#print axioms trialInnerRows_compatible

end PrimeGap182
