import TypeIIIEtaleSkyscraperExact
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Actual direct image of a geometric skyscraper

For an arbitrary scheme morphism q : X → S, the original inverse-image
stalk comparison at a separably closed geometric point s identifies the
composite left adjoint with the stalk at s ≫ q.  Conjugating this actual
isomorphism through the original adjunctions identifies q_* of the
original skyscraper at s with the original skyscraper at s ≫ q.

The unit, counit, and ordinary adjunction formulas below retain those
same adjunctions and the same inverse-image stalk comparison.  No
direct-image comparison or exactness hypothesis on q is supplied.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleSkyscraperDirectImage

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable {X S : Scheme.{u}} (q : X ⟶ S)
  {K : Type u} [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ X)
  (E : Type u) [Ring E]

/-- The composite of the original inverse-image and skyscraper adjunctions. -/
def adjunction :
    EtaleInverseImage.functor q E ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E) ⊣
      EtaleSkyscraper.functor X (Scheme.pointSmallEtale s) E ⋙
        EtaleDirectImage.functor q E :=
  (EtaleInverseImage.adjunction q E).comp
    (EtaleSkyscraper.adjunction X (Scheme.pointSmallEtale s) E)

/-- The direct image of the actual geometric skyscraper is the actual
skyscraper at the composed geometric point. -/
def iso :
    EtaleSkyscraper.functor X (Scheme.pointSmallEtale s) E ⋙
        EtaleDirectImage.functor q E ≅
      EtaleSkyscraper.functor S (Scheme.pointSmallEtale (s ≫ q)) E :=
  conjugateIsoEquiv (adjunction q s E)
    (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E)
    (EtaleInverseImage.stalkIso q E s).symm

/-- Conjugating back recovers precisely the original inverse-image
stalk comparison, with its required inverse orientation. -/
theorem iso_conjugate :
    (conjugateIsoEquiv (adjunction q s E)
      (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E)).symm
        (iso q s E) = (EtaleInverseImage.stalkIso q E s).symm :=
  Equiv.symm_apply_apply _ _

/-- The comparison is compatible with the original adjunction units. -/
theorem unit_iso_hom (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    (adjunction q s E).unit.app F ≫
        (iso q s E).hom.app
          ((Scheme.pointSmallEtale s).sheafFiber.obj
            ((EtaleInverseImage.functor q E).obj F)) =
      (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E).unit.app F ≫
        (EtaleSkyscraper.functor S (Scheme.pointSmallEtale (s ≫ q)) E).map
          ((EtaleInverseImage.stalkIso q E s).inv.app F) :=
  unit_conjugateEquiv (adjunction q s E)
    (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E)
    (EtaleInverseImage.stalkIso q E s).inv F

/-- The comparison is compatible with the original adjunction counits. -/
theorem iso_hom_counit (M : ModuleCat.{u} E) :
    (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map ((iso q s E).hom.app M) ≫
        (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E).counit.app M =
      (EtaleInverseImage.stalkIso q E s).inv.app
          ((EtaleDirectImage.functor q E).obj
            ((EtaleSkyscraper.functor X (Scheme.pointSmallEtale s) E).obj M)) ≫
        (adjunction q s E).counit.app M :=
  conjugateEquiv_counit (adjunction q s E)
    (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E)
    (EtaleInverseImage.stalkIso q E s).inv M

/-- Ordinary adjunction transposition commutes with the same comparison. -/
theorem homEquiv_comp_iso
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (M : ModuleCat.{u} E)
    (h : (Scheme.pointSmallEtale s).sheafFiber.obj
      ((EtaleInverseImage.functor q E).obj F) ⟶ M) :
    (adjunction q s E).homEquiv F M h ≫ (iso q s E).hom.app M =
      (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E).homEquiv F M
        ((EtaleInverseImage.stalkIso q E s).inv.app F ≫ h) := by
  simp only [Adjunction.homEquiv_unit]
  rw [assoc, (iso q s E).hom.naturality h, ← assoc, unit_iso_hom]
  simp only [Functor.map_comp, assoc]

/-- Written as the two original ordinary adjunctions, direct-image
transposition followed by the skyscraper comparison is stalk transposition
after the original inverse-image stalk isomorphism. -/
theorem ordinary_homEquiv_comp_iso
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (M : ModuleCat.{u} E)
    (h : (EtaleInverseImage.functor q E).obj F ⟶
      (EtaleSkyscraper.functor X (Scheme.pointSmallEtale s) E).obj M) :
    (EtaleInverseImage.adjunction q E).homEquiv F
        ((EtaleSkyscraper.functor X (Scheme.pointSmallEtale s) E).obj M) h ≫
        (iso q s E).hom.app M =
      (EtaleSkyscraper.adjunction S (Scheme.pointSmallEtale (s ≫ q)) E).homEquiv F M
        ((EtaleInverseImage.stalkIso q E s).inv.app F ≫
          ((EtaleSkyscraper.adjunction X (Scheme.pointSmallEtale s) E).homEquiv
            ((EtaleInverseImage.functor q E).obj F) M).symm h) := by
  simpa only [adjunction, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply] using
      homEquiv_comp_iso q s E F M
        (((EtaleSkyscraper.adjunction X (Scheme.pointSmallEtale s) E).homEquiv
          ((EtaleInverseImage.functor q E).obj F) M).symm h)

#print axioms adjunction
#print axioms iso
#print axioms iso_conjugate
#print axioms unit_iso_hom
#print axioms iso_hom_counit
#print axioms homEquiv_comp_iso
#print axioms ordinary_homEquiv_comp_iso

end PrimeGap182.TypeIII.EtaleSkyscraperDirectImage
