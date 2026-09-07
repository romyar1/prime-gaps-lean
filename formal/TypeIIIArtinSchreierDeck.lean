import TypeIIIArtinSchreierScheme
import TypeIIIArtinSchreierCover

/-!
# Deck transformations of the actual Artin--Schreier étale object

Each quotient automorphism x ↦ x+a induces a scheme automorphism over
the base, hence an automorphism of its object in the small étale site.
The actual geometric fiber functor sends this automorphism to
precomposition of quotient algebra homomorphisms by the translation.
Thus the passage through the spectrum functor fixes the action and its
sign before any sheaf or character projector is constructed.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry
open scoped Classical

section Deck

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] (f : R)

/-- The actual site endomorphism induced by the quotient translation. -/
def artinSchreierEtaleDeck (a : ZMod p) :
    artinSchreierEtaleObject p f ⟶ artinSchreierEtaleObject p f :=
  MorphismProperty.Over.homMk
    (artinSchreierSchemePoint p f (artinSchreierCover_translationHom p f a))
    (artinSchreierSchemePoint_over p f (artinSchreierCover_translationHom p f a))

/-- The underlying scheme morphism is precisely the spectrum of the
constructed algebra automorphism. -/
@[simp] theorem artinSchreierEtaleDeck_left (a : ZMod p) :
    (artinSchreierEtaleDeck p f a).left =
      Spec.map (CommRingCat.ofHom
        (artinSchreierCover_translation p f a).toAlgHom.toRingHom) := rfl

/-- Zero translation induces the identity in the actual étale category. -/
@[simp] theorem artinSchreierEtaleDeck_zero :
    artinSchreierEtaleDeck p f 0 = 𝟙 (artinSchreierEtaleObject p f) := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom
      (artinSchreierCover_translationHom p f 0).toRingHom) = 𝟙 _
  rw [artinSchreierCover_translationHom_zero]
  exact Spec.map_id _

/-- The site transformations obey the additive composition law. -/
theorem artinSchreierEtaleDeck_add (a b : ZMod p) :
    artinSchreierEtaleDeck p f a ≫ artinSchreierEtaleDeck p f b =
      artinSchreierEtaleDeck p f (a + b) := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom
        (artinSchreierCover_translationHom p f a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (artinSchreierCover_translationHom p f b).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (artinSchreierCover_translationHom p f (a + b)).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg
    (fun g : ArtinSchreierCover p R f →ₐ[R] ArtinSchreierCover p R f =>
      Spec.map (CommRingCat.ofHom g.toRingHom))
    (artinSchreierCover_translationHom_add p f a b)

/-- The genuine étale-site automorphism, with inverse translation by -a. -/
def artinSchreierEtaleDeckIso (a : ZMod p) :
    artinSchreierEtaleObject p f ≅ artinSchreierEtaleObject p f where
  hom := artinSchreierEtaleDeck p f a
  inv := artinSchreierEtaleDeck p f (-a)
  hom_inv_id := by
    rw [artinSchreierEtaleDeck_add, add_neg_cancel, artinSchreierEtaleDeck_zero]
  inv_hom_id := by
    rw [artinSchreierEtaleDeck_add, neg_add_cancel, artinSchreierEtaleDeck_zero]

@[simp] theorem artinSchreierEtaleDeckIso_hom (a : ZMod p) :
    (artinSchreierEtaleDeckIso p f a).hom = artinSchreierEtaleDeck p f a := rfl

@[simp] theorem artinSchreierEtaleDeckIso_inv (a : ZMod p) :
    (artinSchreierEtaleDeckIso p f a).inv = artinSchreierEtaleDeck p f (-a) := rfl

end Deck

section GeometricFiber

variable (p : ℕ) [Fact p.Prime] {R Ω : Type u} [CommRing R] [CharP R p]
  [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (f : R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual geometric fiber functor acts on quotient points by
precomposition with the algebra translation, with the positive sign. -/
theorem artinSchreierEtaleDeck_fiberPoint (a : ZMod p)
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
        (artinSchreierEtaleDeck p f a) (artinSchreierEtaleFiberPoint p f g) =
      artinSchreierEtaleFiberPoint p f
        (g.comp (artinSchreierCover_translationHom p f a)) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (artinSchreierCover_translationHom p f a).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (g.comp (artinSchreierCover_translationHom p f a)).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The proved equivalence between algebra homomorphisms and the actual
site fiber intertwines the two deck actions. -/
theorem artinSchreierHomEquivEtaleFiber_deck (a : ZMod p)
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
        (artinSchreierEtaleDeck p f a) (artinSchreierHomEquivEtaleFiber p f g) =
      artinSchreierHomEquivEtaleFiber p f
        (g.comp (artinSchreierCover_translationHom p f a)) :=
  artinSchreierEtaleDeck_fiberPoint p f a g

/-- In inverse coordinates every geometric site point is transformed by
precomposition with the same quotient translation. -/
theorem artinSchreierHomEquivEtaleFiber_symm_deck (a : ZMod p)
    (t : (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.obj
        (artinSchreierEtaleObject p f)) :
    (artinSchreierHomEquivEtaleFiber p f).symm
        ((Scheme.pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
            (artinSchreierEtaleDeck p f a) t) =
      ((artinSchreierHomEquivEtaleFiber p f).symm t).comp
        (artinSchreierCover_translationHom p f a) := by
  obtain ⟨g, rfl⟩ := (artinSchreierHomEquivEtaleFiber p f).surjective t
  rw [artinSchreierHomEquivEtaleFiber_deck]
  simp only [Equiv.symm_apply_apply]

end GeometricFiber

#print axioms artinSchreierEtaleDeck
#print axioms artinSchreierEtaleDeck_left
#print axioms artinSchreierEtaleDeck_zero
#print axioms artinSchreierEtaleDeck_add
#print axioms artinSchreierEtaleDeckIso
#print axioms artinSchreierEtaleDeckIso_hom
#print axioms artinSchreierEtaleDeckIso_inv
#print axioms artinSchreierEtaleDeck_fiberPoint
#print axioms artinSchreierHomEquivEtaleFiber_deck
#print axioms artinSchreierHomEquivEtaleFiber_symm_deck

end PrimeGap182.TypeIII
