import TypeIIIStandardTwoAdicAction
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# A fixed complex embedding of the standard two-adic coefficient field

Both the standard algebraic closure of Q₂ and C have characteristic zero
and cardinality continuum. Classification of algebraically closed fields
therefore supplies an algebraic field isomorphism, fixed independently of
the finite prime p. No compatibility with the usual complex topology is claimed.
-/

noncomputable section
open scoped Cardinal

namespace PrimeGap182.TypeIII.TwoAdicComplexEmbedding

open Cardinal

theorem padic_cardinal (p : ℕ) [Fact p.Prime] : #(ℚ_[p]) = 𝔠 := by
  apply le_antisymm
  · calc
      #(ℚ_[p]) ≤ #(PadicSeq p) :=
        mk_le_of_surjective (f := Padic.mk) Quotient.mk'_surjective
      _ ≤ #(ℕ → ℚ) := mk_subtype_le _
      _ = 𝔠 := by simp only [mk_arrow, lift_id, mk_eq_aleph0 ℚ, mk_nat, aleph0_power_aleph0]
  · exact continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p]

theorem padicAlgCl_cardinal (p : ℕ) [Fact p.Prime] : #(PadicAlgCl p) = 𝔠 := by
  apply le_antisymm
  · have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
    simpa only [padic_cardinal, max_eq_left aleph0_le_continuum] using h
  · calc
      𝔠 = #(ℚ_[p]) := (padic_cardinal p).symm
      _ ≤ #(PadicAlgCl p) := mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective

theorem exists_ringEquiv : Nonempty (PadicAlgCl 2 ≃+* ℂ) := by
  apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
  · rw [padicAlgCl_cardinal]
    exact aleph0_lt_continuum
  · apply Cardinal.lift_mk_eq'.mp
    simp only [lift_id, padicAlgCl_cardinal, mk_complex]

/-- A single algebraic coefficient identification, independent of p. -/
def complexEquiv : PadicAlgCl 2 ≃+* ℂ := exists_ringEquiv.some

scoped instance complexAlgebra : Algebra (PadicAlgCl 2) ℂ := complexEquiv.toRingHom.toAlgebra

theorem algebraMap_eq (x : PadicAlgCl 2) : algebraMap (PadicAlgCl 2) ℂ x = complexEquiv x := rfl

end PrimeGap182.TypeIII.TwoAdicComplexEmbedding

#print axioms PrimeGap182.TypeIII.TwoAdicComplexEmbedding.padic_cardinal
#print axioms PrimeGap182.TypeIII.TwoAdicComplexEmbedding.padicAlgCl_cardinal
#print axioms PrimeGap182.TypeIII.TwoAdicComplexEmbedding.exists_ringEquiv
#print axioms PrimeGap182.TypeIII.TwoAdicComplexEmbedding.complexEquiv
#print axioms PrimeGap182.TypeIII.TwoAdicComplexEmbedding.complexAlgebra
#print axioms PrimeGap182.TypeIII.TwoAdicComplexEmbedding.algebraMap_eq
