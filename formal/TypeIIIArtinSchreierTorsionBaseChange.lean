import TypeIIIArtinSchreierCoefficientExtension
import TypeIIIArtinSchreierTorsionTower

/-!
# Tensor compatibility of the actual finite-coefficient sheaf tower

Extending coefficients along the actual cyclotomic reduction Λ_n → Λ_m
identifies the original level-n character sheaf with the original level-m
sheaf. The canonical isomorphism is adjoint to the already constructed
transition map. Character compatibility and invertibility of p are
discharged by the actual finite coefficient rings.

The statement concerns sheafified tensor extension on the small étale site.
It does not assert a quotient description of the inverse-limit coefficient
ring or an adic cohomology comparison.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
  {R : Type} [CommRing R] [CharP R p] (f : R)

/-- Tensoring the actual finite-level character sheaf by the lower
coefficient ring gives the actual lower-level character sheaf. -/
def torsionArtinSchreierReductionIso {m n : ℕ} (hmn : m ≤ n) :
    (etaleModuleCoefficientExtension R (torsionCoefficientReduce p ell hmn)).obj
        (torsionArtinSchreierSheaf p ell hne n f) ≅
      torsionArtinSchreierSheaf p ell hne m f := by
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  let : Invertible (p : TorsionCoefficientRing p ell m) :=
    (torsionCoefficient_p_isUnit p ell m hne).invertible
  exact artinSchreierRingCharacterSheafCoefficientExtensionIso p f
    (torsionCoefficientReduce p ell hmn)
    (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell m)
    (torsionCoefficientReduce_char p ell hmn)

/-- The tensor isomorphism is induced by the actual reduction map
already used in the coherent inverse system. -/
theorem torsionArtinSchreierReductionIso_mate {m n : ℕ} (hmn : m ≤ n) :
    (etaleModuleCoefficientAdjunction R (torsionCoefficientReduce p ell hmn)).homEquiv _ _
        (torsionArtinSchreierReductionIso p ell hne f hmn).hom =
      torsionArtinSchreierReduction p ell hne f hmn := by
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  let : Invertible (p : TorsionCoefficientRing p ell m) :=
    (torsionCoefficient_p_isUnit p ell m hne).invertible
  exact artinSchreierRingCharacterSheafCoefficientExtensionIso_mate p f
    (torsionCoefficientReduce p ell hmn)
    (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell m)
    (torsionCoefficientReduce_char p ell hmn)

#print axioms torsionArtinSchreierReductionIso
#print axioms torsionArtinSchreierReductionIso_mate

end PrimeGap182.TypeIII
