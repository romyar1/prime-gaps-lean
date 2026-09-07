import TypeIIIDerivedBaseChangeComposition
import TypeIIIDerivedBaseChangeTransformation
import TypeIIIEtaleCoefficientRestrictionComposition
import TypeIIIEtaleCoefficientDerivedDirectImage

/-!
# Composition of the original relative coefficient comparisons

Restriction of coefficients commutes with the original direct-image
functor on its literal section modules.  Its ordinary composition square
uses exactly the original coefficient-restriction composition maps.
The proved pasting and transformation laws for the original derived
comparison then give the corresponding equality in every degree.
Neither the derived maps nor their composition isomorphisms are replaced.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {X S : Scheme.{u}} (q : X ⟶ S)
  {E₀ E₁ E₂ : Type u} [Ring E₀] [Ring E₁] [Ring E₂]
  (f : E₀ →+* E₁) (g : E₁ →+* E₂) (gf : E₀ →+* E₂) (hgf : gf = g.comp f)

/-- The original ordinary coefficient square respects the original
composition isomorphisms on both sites, on every section. -/
theorem directImageIso_comp_square' :
    (directImageIso q gf).hom ≫
        Functor.whiskerRight (compIso' X f g gf hgf).hom (EtaleDirectImage.functor q E₀) =
      Functor.whiskerLeft (EtaleDirectImage.functor q E₂) (compIso' S f g gf hgf).hom ≫
        derivedBaseChangeSquarePaste
          (EtaleDirectImage.functor q E₂) (EtaleDirectImage.functor q E₁)
          (EtaleDirectImage.functor q E₀)
          (functor X g) (functor X f) (functor S g) (functor S f)
          (directImageIso q g).hom (directImageIso q f).hom := by
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  ext U x
  rfl

/-- Successive original derived coefficient maps agree with the
original map for the specified composite coefficient homomorphism. -/
theorem derivedDirectImageMap_comp' (n : ℕ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (compIso' S f g gf hgf).hom.app ((EtaleDerivedDirectImage.functor q E₂ n).obj F) ≫
        (functor S f).map ((derivedDirectImageMap q g n).app F) ≫
        (derivedDirectImageMap q f n).app ((functor X g).obj F) =
      (derivedDirectImageMap q gf n).app F ≫
        (EtaleDerivedDirectImage.functor q E₀ n).map
          ((compIso' X f g gf hgf).hom.app F) := by
  have h := derivedBaseChangeMap_transformation_app
    (EtaleDirectImage.functor q E₂) (EtaleDirectImage.functor q E₀)
    (functor X gf) (functor X g ⋙ functor X f)
    (functor S gf) (functor S g ⋙ functor S f)
    (compIso' X f g gf hgf).hom (compIso' S f g gf hgf).hom
    (directImageIso q gf).hom
    (derivedBaseChangeSquarePaste
      (EtaleDirectImage.functor q E₂) (EtaleDirectImage.functor q E₁)
      (EtaleDirectImage.functor q E₀)
      (functor X g) (functor X f) (functor S g) (functor S f)
      (directImageIso q g).hom (directImageIso q f).hom)
    (directImageIso_comp_square' q f g gf hgf) n F
  rw [derivedBaseChangeMap_comp_app] at h
  exact h.symm

/-- The same composition formula for the literal composite ring map. -/
theorem derivedDirectImageMap_comp (n : ℕ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (compIso S f g).hom.app ((EtaleDerivedDirectImage.functor q E₂ n).obj F) ≫
        (functor S f).map ((derivedDirectImageMap q g n).app F) ≫
        (derivedDirectImageMap q f n).app ((functor X g).obj F) =
      (derivedDirectImageMap q (g.comp f) n).app F ≫
        (EtaleDerivedDirectImage.functor q E₀ n).map ((compIso X f g).hom.app F) :=
  derivedDirectImageMap_comp' q f g (g.comp f) rfl n F

/-- The packaged original isomorphisms retain this same composition law. -/
theorem derivedDirectImageIso_comp' (n : ℕ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (compIso' S f g gf hgf).hom.app ((EtaleDerivedDirectImage.functor q E₂ n).obj F) ≫
        (functor S f).map ((derivedDirectImageIso q g n).hom.app F) ≫
        (derivedDirectImageIso q f n).hom.app ((functor X g).obj F) =
      (derivedDirectImageIso q gf n).hom.app F ≫
        (EtaleDerivedDirectImage.functor q E₀ n).map
          ((compIso' X f g gf hgf).hom.app F) :=
  derivedDirectImageMap_comp' q f g gf hgf n F

#print axioms directImageIso_comp_square'
#print axioms derivedDirectImageMap_comp'
#print axioms derivedDirectImageMap_comp
#print axioms derivedDirectImageIso_comp'

end PrimeGap182.TypeIII.EtaleCoefficientRestriction
