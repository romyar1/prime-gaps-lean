import TypeIIIArtinSchreierLimitSheaf
import TypeIIIEtaleCoefficientRestrictionComposition

/-!
# The original torsion reductions under coefficient restriction

The existing transition maps in the common limit-coefficient category
are the restrictions of the existing finite-coefficient transition maps,
followed by the inverse of the original scalar composition comparison.
The coefficient equality used by that comparison is the proved equality
between reduction after projection and the lower-level projection.

All equalities concern the original sheaves and original morphisms.
The finite-level composition law is also recorded as an equality of
sheaf morphisms with the same scalar composition comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
  {R : Type} [CommRing R] [CharP R p] (f : R)

/-- The original common-coefficient reduction has exactly the original
finite reduction as its map on each section. -/
theorem torsionArtinSchreierLimitModuleReduction_apply {m n : ℕ} (hmn : m ≤ n)
    (X : (Spec (.of R)).Etaleᵒᵖ)
    (x : (torsionArtinSchreierSheaf p ell hne n f).obj.obj X) :
    (torsionArtinSchreierLimitModuleReduction p ell hne f hmn).hom.app X x =
      (torsionArtinSchreierReduction p ell hne f hmn).hom.app X x := rfl

/-- Restricting the original finite reduction along the upper projection,
then applying the inverse scalar comparison, is the original transition
in the category of limit-ring module sheaves. -/
theorem torsionArtinSchreierLimitModuleReduction_eq_restrictScalars
    {m n : ℕ} (hmn : m ≤ n) :
    torsionArtinSchreierLimitModuleReduction p ell hne f hmn =
      (EtaleCoefficientRestriction.functor (Spec (.of R))
          (torsionCoefficientLimitProjection p ell n)).map
        (torsionArtinSchreierReduction p ell hne f hmn) ≫
      (EtaleCoefficientRestriction.compIso' (Spec (.of R))
        (torsionCoefficientLimitProjection p ell n)
        (torsionCoefficientReduce p ell hmn)
        (torsionCoefficientLimitProjection p ell m)
        (torsionCoefficientLimitProjection_compatible p ell hmn).symm).inv.app
          (torsionArtinSchreierSheaf p ell hne m f) := by
  apply Sheaf.hom_ext
  ext X x
  rfl

/-- Equivalently, the original transition and the forward scalar
comparison give the actual restriction of the finite reduction. -/
theorem torsionArtinSchreierLimitModuleReduction_comp_compIso_hom
    {m n : ℕ} (hmn : m ≤ n) :
    torsionArtinSchreierLimitModuleReduction p ell hne f hmn ≫
        (EtaleCoefficientRestriction.compIso' (Spec (.of R))
          (torsionCoefficientLimitProjection p ell n)
          (torsionCoefficientReduce p ell hmn)
          (torsionCoefficientLimitProjection p ell m)
          (torsionCoefficientLimitProjection_compatible p ell hmn).symm).hom.app
            (torsionArtinSchreierSheaf p ell hne m f) =
      (EtaleCoefficientRestriction.functor (Spec (.of R))
          (torsionCoefficientLimitProjection p ell n)).map
        (torsionArtinSchreierReduction p ell hne f hmn) := by
  apply Sheaf.hom_ext
  ext X x
  rfl

/-- The original finite reductions compose as sheaf morphisms, with
the canonical comparison for the proved equality of reduction maps. -/
theorem torsionArtinSchreierReduction_comp {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    torsionArtinSchreierReduction p ell hne f hmn ≫
        (EtaleCoefficientRestriction.functor (Spec (.of R))
          (torsionCoefficientReduce p ell hmn)).map
            (torsionArtinSchreierReduction p ell hne f hkm) =
      torsionArtinSchreierReduction p ell hne f (hkm.trans hmn) ≫
        (EtaleCoefficientRestriction.compIso' (Spec (.of R))
          (torsionCoefficientReduce p ell hmn)
          (torsionCoefficientReduce p ell hkm)
          (torsionCoefficientReduce p ell (hkm.trans hmn))
          (torsionCoefficientReduce_comp p ell hkm hmn).symm).hom.app
            (torsionArtinSchreierSheaf p ell hne k f) := by
  apply Sheaf.hom_ext
  ext X x
  exact torsionArtinSchreierReduction_comp_apply p ell hne f hkm hmn X x

/-- The direct finite reduction is the successive original reductions
followed by the inverse of the original scalar comparison. -/
theorem torsionArtinSchreierReduction_eq_comp_restrictScalars {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    torsionArtinSchreierReduction p ell hne f (hkm.trans hmn) =
      torsionArtinSchreierReduction p ell hne f hmn ≫
        (EtaleCoefficientRestriction.functor (Spec (.of R))
          (torsionCoefficientReduce p ell hmn)).map
            (torsionArtinSchreierReduction p ell hne f hkm) ≫
        (EtaleCoefficientRestriction.compIso' (Spec (.of R))
          (torsionCoefficientReduce p ell hmn)
          (torsionCoefficientReduce p ell hkm)
          (torsionCoefficientReduce p ell (hkm.trans hmn))
          (torsionCoefficientReduce_comp p ell hkm hmn).symm).inv.app
            (torsionArtinSchreierSheaf p ell hne k f) := by
  apply Sheaf.hom_ext
  ext X x
  exact (torsionArtinSchreierReduction_comp_apply p ell hne f hkm hmn X x).symm

#print axioms torsionArtinSchreierLimitModuleReduction_apply
#print axioms torsionArtinSchreierLimitModuleReduction_eq_restrictScalars
#print axioms torsionArtinSchreierLimitModuleReduction_comp_compIso_hom
#print axioms torsionArtinSchreierReduction_comp
#print axioms torsionArtinSchreierReduction_eq_comp_restrictScalars

end PrimeGap182.TypeIII
