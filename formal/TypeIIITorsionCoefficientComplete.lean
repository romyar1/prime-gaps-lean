import TypeIIITorsionCoefficientLimitTopology
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Adic completeness of the actual coefficient ring

The proved adic topology is the original compact Hausdorff topology.
Its compatible additive uniformity is therefore complete, giving the
algebraic adic-completeness predicate for the same ring and ideal.
-/

noncomputable section

namespace PrimeGap182.TypeIII

/-- The original coefficient ring is complete and separated for powers of (ℓ). -/
theorem torsionCoefficientLimit_isAdicComplete (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    IsAdicComplete (Ideal.span {(ell : TorsionCoefficientLimit p ell)})
      (TorsionCoefficientLimit p ell) := by
  let : UniformSpace (TorsionCoefficientLimit p ell) :=
    IsTopologicalAddGroup.rightUniformSpace (TorsionCoefficientLimit p ell)
  let : IsUniformAddGroup (TorsionCoefficientLimit p ell) :=
    isUniformAddGroup_of_addCommGroup
  exact (torsionCoefficientLimit_isAdic p ell).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

#print axioms torsionCoefficientLimit_isAdicComplete

end PrimeGap182.TypeIII
