import TypeIIIArtinSchreierDeck
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Module sheaves attached to the actual Artin--Schreier cover

The ambient sheaf is the sheafification of the free module presheaf on
the representable presheaf of the actual finite étale cover. Its stalk
is identified with the free module on the fiber of that cover by the
fiber and sheafification isomorphisms, without a stalk-comparison
hypothesis.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R)

section RingCoefficients

variable (E : Type u) [CommRing E]

/-- The actual module-valued point fiber functor preserves coefficient
scalars, by its colimit cocone and naturality. -/
theorem etaleModulePresheafFiber_linear
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    Functor.Linear E (Φ.presheafFiber (A := ModuleCat.{u} E)) := by
  constructor
  intro P Q g r
  apply Φ.presheafFiber_hom_ext
  intro X x
  simp only [Φ.toPresheafFiber_naturality, NatTrans.app_smul,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul]

/-- Free modules on maps to the actual Artin--Schreier site object. -/
def artinSchreierFreePresheaf :
    (Spec (.of R)).Etaleᵒᵖ ⥤ ModuleCat.{u} E :=
  (shrinkYoneda.{u}.obj (artinSchreierEtaleObject p f)) ⋙ ModuleCat.free E

/-- The sheafification of the free representable module presheaf. -/
def artinSchreierFreeSheaf :
    Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E) :=
  (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).obj
    (artinSchreierFreePresheaf p f E)

/-- An actual stalk of the ambient sheaf is the free module on the
fiber of the finite étale cover. -/
def artinSchreierFreeSheaf_stalkIso
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    (Φ.sheafFiber (A := ModuleCat.{u} E)).obj (artinSchreierFreeSheaf p f E) ≅
      (ModuleCat.free E).obj (Φ.fiber.obj (artinSchreierEtaleObject p f)) := by
  letI : (ModuleCat.free E).IsLeftAdjoint := (ModuleCat.adj E).isLeftAdjoint
  exact (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u} E)).app
      (artinSchreierFreePresheaf p f E) ≪≫
    (Φ.presheafFiberCompIso (ModuleCat.free E)).app
      (shrinkYoneda.{u}.obj (artinSchreierEtaleObject p f)) ≪≫
    (ModuleCat.free E).mapIso
      ((Φ.shrinkYonedaCompPresheafFiberIso).app (artinSchreierEtaleObject p f))

/-- Functoriality in an actual endomorphism of the finite étale cover. -/
def artinSchreierFreePresheafMap
    (g : artinSchreierEtaleObject p f ⟶ artinSchreierEtaleObject p f) :
    artinSchreierFreePresheaf p f E ⟶ artinSchreierFreePresheaf p f E :=
  Functor.whiskerRight (shrinkYoneda.{u}.map g) (ModuleCat.free E)

/-- Sheafification of the map induced by an actual cover endomorphism. -/
def artinSchreierFreeSheafMap
    (g : artinSchreierEtaleObject p f ⟶ artinSchreierEtaleObject p f) :
    artinSchreierFreeSheaf p f E ⟶ artinSchreierFreeSheaf p f E :=
  (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
    (artinSchreierFreePresheafMap p f E g)

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalk comparison intertwines actual cover endomorphisms with
the corresponding maps of the geometric fiber. -/
theorem artinSchreierFreeSheaf_stalk_naturality
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology)
    (g : artinSchreierEtaleObject p f ⟶ artinSchreierEtaleObject p f) :
    Φ.sheafFiber.map (artinSchreierFreeSheafMap p f E g) ≫
        (artinSchreierFreeSheaf_stalkIso p f E Φ).hom =
      (artinSchreierFreeSheaf_stalkIso p f E Φ).hom ≫
        (ModuleCat.free E).map (Φ.fiber.map g) := by
  let : (ModuleCat.free E).IsLeftAdjoint := (ModuleCat.adj E).isLeftAdjoint
  have h₁ := (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u} E)).hom.naturality
    (artinSchreierFreePresheafMap p f E g)
  have h₂ := (Φ.presheafFiberCompIso (ModuleCat.free E)).hom.naturality
    (shrinkYoneda.{u}.map g)
  have h₃ := congrArg (fun h => (ModuleCat.free E).map h)
    (Φ.shrinkYonedaCompPresheafFiberIso.hom.naturality g)
  simp only [Functor.map_comp] at h₃
  simp only [Functor.comp_map] at h₁ h₂ h₃
  dsimp only [Functor.whiskeringRight] at h₂
  dsimp only [artinSchreierFreeSheafMap, artinSchreierFreeSheaf,
    artinSchreierFreePresheafMap, artinSchreierFreePresheaf,
    artinSchreierFreeSheaf_stalkIso] at *
  change _ ≫ (_ ≫ _ ≫ _) = (_ ≫ _ ≫ _) ≫ _
  simp only [Iso.app_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  rw [h₁]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ ((ModuleCat.free E).map _), h₂]
  simp only [Category.assoc]
  rw [h₃]

end RingCoefficients

variable (E : Type u) [Field E]

/-- The positive-weight average on free generators.  A deck translation
acts on functions by the inverse translation, so this sign corresponds
to the character convention v(z+a) = ψ(a)v(z). -/
def artinSchreierCharacterPresheafAverage (ψ : AddChar (ZMod p) E) :
    artinSchreierFreePresheaf p f E ⟶ artinSchreierFreePresheaf p f E :=
  (p : E)⁻¹ • ∑ a : ZMod p,
    ψ a • artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a)

/-- The average is an actual sheaf morphism, obtained by sheafification. -/
def artinSchreierCharacterSheafAverage (ψ : AddChar (ZMod p) E) :
    artinSchreierFreeSheaf p f E ⟶ artinSchreierFreeSheaf p f E :=
  (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
    (artinSchreierCharacterPresheafAverage p f E ψ)

/-- The image of the explicit character average in the category of
module-valued sheaves on the actual small étale site.  The definition
does not assert a rank calculation or ℓ-adic cohomological properties. -/
def artinSchreierCharacterImageSheaf (ψ : AddChar (ZMod p) E) :
    Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E) :=
  Abelian.image (artinSchreierCharacterSheafAverage p f E ψ)

/-- Taking a stalk of the actual image sheaf gives the image of the
actual stalk endomorphism.  Exactness follows from the module-valued
point fiber functor; no image-comparison hypothesis is used. -/
def artinSchreierCharacterImageSheaf_stalkImageIso (ψ : AddChar (ZMod p) E)
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    (Φ.sheafFiber (A := ModuleCat.{u} E)).obj
        (artinSchreierCharacterImageSheaf p f E ψ) ≅
      Abelian.image (Φ.sheafFiber.map (artinSchreierCharacterSheafAverage p f E ψ)) :=
  Abelian.PreservesImage.iso Φ.sheafFiber (artinSchreierCharacterSheafAverage p f E ψ)

/-- The explicit average of the actual deck maps on the free geometric
fiber.  Its coefficients have the same positive sign as the presheaf
average. -/
def artinSchreierCharacterFreeFiberAverage (ψ : AddChar (ZMod p) E)
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    (ModuleCat.free E).obj (Φ.fiber.obj (artinSchreierEtaleObject p f)) ⟶
      (ModuleCat.free E).obj (Φ.fiber.obj (artinSchreierEtaleObject p f)) :=
  (p : E)⁻¹ • ∑ a : ZMod p,
    ψ a • (ModuleCat.free E).map (Φ.fiber.map (artinSchreierEtaleDeck p f a))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual sheaf-stalk average is conjugate to the explicit free
fiber average.  Both scalar compatibility and the deck comparison
are proved, rather than assumed. -/
theorem artinSchreierCharacterSheafAverage_stalk
    (ψ : AddChar (ZMod p) E)
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    Φ.sheafFiber.map (artinSchreierCharacterSheafAverage p f E ψ) ≫
        (artinSchreierFreeSheaf_stalkIso p f E Φ).hom =
      (artinSchreierFreeSheaf_stalkIso p f E Φ).hom ≫
        artinSchreierCharacterFreeFiberAverage p f E ψ Φ := by
  let := etaleModulePresheafFiber_linear E Φ
  let : (Φ.presheafFiber (A := ModuleCat.{u} E)).Additive :=
    { map_add := by
        intro P Q g h
        apply Φ.presheafFiber_hom_ext
        intro X x
        simp only [Φ.toPresheafFiber_naturality, NatTrans.app_add,
          Preadditive.add_comp, Preadditive.comp_add] }
  let F := presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E) ⋙
    Φ.sheafFiber
  let : F.Linear E := Functor.linear_of_iso E
    (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u} E)).symm
  let : F.Additive := Functor.additive_of_iso
    (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u} E)).symm
  change F.map (artinSchreierCharacterPresheafAverage p f E ψ) ≫ _ = _
  simp only [artinSchreierCharacterPresheafAverage,
    artinSchreierCharacterFreeFiberAverage, Functor.map_smul, Functor.map_sum,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum]
  apply congrArg (fun h => (p : E)⁻¹ • h)
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun h => ψ a • h)
    (artinSchreierFreeSheaf_stalk_naturality p f E Φ (artinSchreierEtaleDeck p f a))

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.etaleModulePresheafFiber_linear
#print axioms PrimeGap182.TypeIII.artinSchreierFreePresheaf
#print axioms PrimeGap182.TypeIII.artinSchreierFreeSheaf
#print axioms PrimeGap182.TypeIII.artinSchreierFreeSheaf_stalkIso
#print axioms PrimeGap182.TypeIII.artinSchreierFreePresheafMap
#print axioms PrimeGap182.TypeIII.artinSchreierFreeSheafMap
#print axioms PrimeGap182.TypeIII.artinSchreierFreeSheaf_stalk_naturality
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterPresheafAverage
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafAverage
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheaf
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheaf_stalkImageIso
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterFreeFiberAverage
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafAverage_stalk
