import TypeIIIEtaleGodementRetract
import TypeIIIEtaleCoefficientSkyscraperFamily
import TypeIIIEtaleSkyscraperFamilyCohomology
import TypeIIIDerivedBaseChangeAcyclic

/-!
# Original étale cohomology under restriction of coefficients

An injective sheaf is a retract of the actual product of skyscrapers of
its geometric stalks.  Coefficient restriction carries this product to
the product of the skyscrapers of the restricted modules.  The proved
vanishing of its positive cohomology therefore makes every restricted
injective acyclic for the original global-sections functor.

Applying the proved acyclic-resolution comparison to the literal
global-sections square gives the canonical cohomology comparison for
every ring homomorphism.  Its forward map is the existing derived
base-change transformation, and its degree-zero square retains the
original identity on sections and the resolution augmentations.

This compares ordinary module-sheaf cohomology across coefficient
categories.  It does not commute cohomology with an inverse limit or
identify ordinary cohomology with adic cohomology.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- The actual first Godement product remains acyclic after coefficient
restriction, because it is the actual product of restricted skyscrapers. -/
theorem isZero_cohomology_succ_restrict_godement (n : ℕ)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')) :
    IsZero ((EtaleCohomology.functor S E (n + 1)).obj
      ((functor S r).obj (EtaleGodement.obj S E' F))) := by
  let M := (EtaleSkyscraperFamily.stalks S (algebraicClosureEtalePoint S) E').obj F
  exact (EtaleSkyscraperFamily.isZero_cohomology_succ S
    (algebraicClosureEtalePoint S) E n
    ((EtaleCoefficientSkyscraperFamily.diagramRestriction r).obj M)).of_iso
      ((EtaleCohomology.functor S E (n + 1)).mapIso
        (EtaleCoefficientSkyscraperFamily.objIso S r (algebraicClosureEtalePoint S) M))

/-- Restriction of an actual injective sheaf is acyclic for the original
global sections; preservation of injectives is not needed. -/
theorem isZero_cohomology_succ_restrict_injective (n : ℕ)
    (J : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')) [Injective J] :
    IsZero ((EtaleCohomology.functor S E (n + 1)).obj ((functor S r).obj J)) := by
  let t := ((EtaleGodement.injectiveRetract S E' J).map (functor S r)).map
    (EtaleCohomology.functor S E (n + 1))
  have ht := isZero_cohomology_succ_restrict_godement S r n J
  apply (IsZero.iff_id_eq_zero _).2
  rw [← t.retract, ht.eq_zero_of_tgt t.i, zero_comp]

/-- The original derived comparison applied to the literal ordinary
global-sections square for coefficient restriction. -/
def cohomologyMap (n : ℕ) :
    EtaleCohomology.functor S E' n ⋙ ModuleCat.restrictScalars r ⟶
      functor S r ⋙ EtaleCohomology.functor S E n :=
  derivedBaseChangeMap (EtaleCohomology.sections S E') (EtaleCohomology.sections S E)
    (functor S r) (ModuleCat.restrictScalars r) (sectionsIso S r).inv n

/-- The proved Godement retract discharges acyclicity, so the same
coefficient comparison is invertible in every nonnegative degree. -/
theorem cohomologyMap_isIso (n : ℕ) : IsIso (cohomologyMap S r n) := by
  let := HasDerivedCategory.standard (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
  let := HasDerivedCategory.standard (ModuleCat.{u} E)
  exact derivedBaseChangeMap_isIso_of_acyclic
    (EtaleCohomology.sections S E') (EtaleCohomology.sections S E)
    (functor S r) (ModuleCat.restrictScalars r) (sectionsIso S r).inv
    (fun J hJ m => by
      let : Injective J := hJ
      exact isZero_cohomology_succ_restrict_injective S r m J) n

/-- Original étale cohomology commutes with arbitrary restriction of
coefficient rings through the canonical derived comparison. -/
def cohomologyIso (n : ℕ) :
    EtaleCohomology.functor S E' n ⋙ ModuleCat.restrictScalars r ≅
      functor S r ⋙ EtaleCohomology.functor S E n := by
  have : IsIso (cohomologyMap S r n) := cohomologyMap_isIso S r n
  exact asIso (cohomologyMap S r n)

/-- The packaged isomorphism uses exactly that original comparison map. -/
theorem cohomologyIso_hom (n : ℕ) :
    (cohomologyIso S r n).hom = cohomologyMap S r n := rfl

/-- The original comparison respects the identity on sections and both
canonical maps into zeroth right derived global sections. -/
theorem cohomologyMap_zero :
    Functor.whiskerRight (EtaleCohomology.sections S E').toRightDerivedZero
        (ModuleCat.restrictScalars r) ≫ cohomologyMap S r 0 =
      (sectionsIso S r).inv ≫ Functor.whiskerLeft (functor S r)
        (EtaleCohomology.sections S E).toRightDerivedZero :=
  derivedBaseChangeMap_zero (EtaleCohomology.sections S E') (EtaleCohomology.sections S E)
    (functor S r) (ModuleCat.restrictScalars r) (sectionsIso S r).inv

/-- The canonical degree-zero square is retained by the same isomorphism. -/
theorem cohomologyIso_zero :
    Functor.whiskerRight (EtaleCohomology.sections S E').toRightDerivedZero
        (ModuleCat.restrictScalars r) ≫ (cohomologyIso S r 0).hom =
      (sectionsIso S r).inv ≫ Functor.whiskerLeft (functor S r)
        (EtaleCohomology.sections S E).toRightDerivedZero :=
  cohomologyMap_zero S r

#print axioms isZero_cohomology_succ_restrict_godement
#print axioms isZero_cohomology_succ_restrict_injective
#print axioms cohomologyMap
#print axioms cohomologyMap_isIso
#print axioms cohomologyIso
#print axioms cohomologyIso_hom
#print axioms cohomologyMap_zero
#print axioms cohomologyIso_zero

end PrimeGap182.TypeIII.EtaleCoefficientRestriction
