import TypeIIIArtinSchreierDeck
import TypeIIIArtinSchreierGeometricFiber
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Functions on the actual geometric Artin--Schreier site fiber

The geometric fiber of the actual étale object is identified with the
literal polynomial roots.  Root existence and the prime-field torsor
prove nonemptiness and finiteness.  The free module on that site fiber
is consequently the module of functions on the root fiber.

The free functor pushes basis vectors forward.  Its deck transformation
by a therefore acts on functions by precomposition with translation by
-a.  This sign is proved from the actual geometric fiber functor.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry
open scoped Classical

section SiteFiber

variable (p : ℕ) [Fact p.Prime] (K Ω : Type u) [Field K] [CharP K p]
  [Field Ω] [IsSepClosed Ω] [Algebra K Ω] (f : K)

/-- The actual geometric fiber functor evaluated on the actual étale object. -/
abbrev ArtinSchreierSiteFiber : Type u :=
  (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj
      (artinSchreierEtaleObject p f)

/-- The site fiber is exactly the set of literal Artin--Schreier roots. -/
def artinSchreierSiteFiberEquivRoots :
    ArtinSchreierSiteFiber p K Ω f ≃ ArtinSchreierFiber p K Ω f :=
  (artinSchreierHomEquivEtaleFiber p f).symm.trans
    (artinSchreierHomEquivFiber p K Ω f)

/-- The root coordinate is evaluation of the actual scheme point's
coordinate homomorphism on the quotient generator. -/
@[simp] theorem artinSchreierSiteFiberEquivRoots_val
    (t : ArtinSchreierSiteFiber p K Ω f) :
    (artinSchreierSiteFiberEquivRoots p K Ω f t : Ω) =
      (Spec.preimage t.left).hom (artinSchreierRoot p f) := rfl

/-- The actual fiber permutation induced by the deck isomorphism. -/
def artinSchreierSiteFiberDeckEquiv (a : ZMod p) :
    ArtinSchreierSiteFiber p K Ω f ≃ ArtinSchreierSiteFiber p K Ω f :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.mapIso
      (artinSchreierEtaleDeckIso p f a)).toEquiv

@[simp] theorem artinSchreierSiteFiberDeckEquiv_apply (a : ZMod p)
    (t : ArtinSchreierSiteFiber p K Ω f) :
    artinSchreierSiteFiberDeckEquiv p K Ω f a t =
      (Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.map
          (artinSchreierEtaleDeck p f a) t := rfl

variable [CharP Ω p] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω]

/-- The actual geometric site action is positive translation on roots. -/
theorem artinSchreierSiteFiberEquivRoots_deck (a : ZMod p)
    (t : ArtinSchreierSiteFiber p K Ω f) :
    artinSchreierSiteFiberEquivRoots p K Ω f
        ((Scheme.pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.map
            (artinSchreierEtaleDeck p f a) t) =
      artinSchreierFiberTranslate p K Ω f a
        (artinSchreierSiteFiberEquivRoots p K Ω f t) := by
  change artinSchreierHomEquivFiber p K Ω f
      ((artinSchreierHomEquivEtaleFiber p f).symm _) = _
  rw [artinSchreierHomEquivEtaleFiber_symm_deck]
  exact artinSchreierHomEquivFiber_translation p K Ω f a
    ((artinSchreierHomEquivEtaleFiber p f).symm t)

/-- Transporting a translated root back to the site gives the actual
fiber-functor action on the corresponding point. -/
theorem artinSchreierSiteFiberEquivRoots_symm_translate (a : ZMod p)
    (z : ArtinSchreierFiber p K Ω f) :
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.map
        (artinSchreierEtaleDeck p f a)
        ((artinSchreierSiteFiberEquivRoots p K Ω f).symm z) =
      (artinSchreierSiteFiberEquivRoots p K Ω f).symm
        (artinSchreierFiberTranslate p K Ω f a z) := by
  apply (artinSchreierSiteFiberEquivRoots p K Ω f).injective
  rw [artinSchreierSiteFiberEquivRoots_deck, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

end SiteFiber

section FiniteFunctions

variable (p : ℕ) [Fact p.Prime] (K Ω : Type u) [Field K] [CharP K p]
  [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [Algebra K Ω] [Algebra (ZMod p) Ω] (f : K)

omit [Algebra (ZMod p) Ω] in
/-- Existence of a root proves nonemptiness of the actual site fiber. -/
theorem artinSchreierSiteFiber_nonempty :
    Nonempty (ArtinSchreierSiteFiber p K Ω f) :=
  ⟨(artinSchreierSiteFiberEquivRoots p K Ω f).symm
    (artinSchreierGeometricRoot p K Ω f)⟩

/-- The actual geometric site fiber has exactly p elements. -/
theorem artinSchreierSiteFiber_card :
    Nat.card (ArtinSchreierSiteFiber p K Ω f) = p := by
  rw [Nat.card_congr (artinSchreierSiteFiberEquivRoots p K Ω f),
    artinSchreierFiber_card]

/-- Finiteness is proved for the actual site fiber. -/
theorem artinSchreierSiteFiber_finite :
    Finite (ArtinSchreierSiteFiber p K Ω f) :=
  Nat.finite_of_card_ne_zero (by
    rw [artinSchreierSiteFiber_card]
    exact (Fact.out : p.Prime).ne_zero)

omit [CharP K p] in
/-- The proved root count supplies the finite-function-space interface. -/
theorem artinSchreierFiber_finite :
    Finite (ArtinSchreierFiber p K Ω f) :=
  Nat.finite_of_card_ne_zero (by
    rw [artinSchreierFiber_card]
    exact (Fact.out : p.Prime).ne_zero)

variable (E : Type u) [CommRing E]

/-- The actual free module on the site fiber is the module of all
functions on the finite polynomial-root fiber. -/
def artinSchreierSiteFreeEquivFunctions :
    (ModuleCat.free E).obj (ArtinSchreierSiteFiber p K Ω f) ≃ₗ[E]
      (ArtinSchreierFiber p K Ω f → E) := by
  letI := artinSchreierFiber_finite p K Ω f
  exact (Finsupp.domLCongr (artinSchreierSiteFiberEquivRoots p K Ω f)).trans
    (Finsupp.linearEquivFunOnFinite E E (ArtinSchreierFiber p K Ω f))

/-- The equivalence reads the coefficient of the corresponding site point. -/
@[simp] theorem artinSchreierSiteFreeEquivFunctions_apply
    (v : (ModuleCat.free E).obj (ArtinSchreierSiteFiber p K Ω f))
    (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierSiteFreeEquivFunctions p K Ω f E v z =
      Finsupp.toFun (v : ArtinSchreierSiteFiber p K Ω f →₀ E)
        ((artinSchreierSiteFiberEquivRoots p K Ω f).symm z) := rfl

variable [Algebra (ZMod p) K] [IsScalarTower (ZMod p) K Ω]

/-- Pushing basis vectors forward by the actual deck map acts on
function coefficients by translation by the negative parameter. -/
theorem artinSchreierSiteFreeEquivFunctions_deck_apply (a : ZMod p)
    (v : (ModuleCat.free E).obj (ArtinSchreierSiteFiber p K Ω f))
    (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierSiteFreeEquivFunctions p K Ω f E
        ((ModuleCat.free E).map
          ((Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.map
              (artinSchreierEtaleDeck p f a)) v) z =
      artinSchreierSiteFreeEquivFunctions p K Ω f E v
        (artinSchreierFiberTranslate p K Ω f (-a) z) := by
  rw [artinSchreierSiteFreeEquivFunctions_apply,
    artinSchreierSiteFreeEquivFunctions_apply]
  let d := artinSchreierSiteFiberDeckEquiv p K Ω f a
  have hi :
      d ((artinSchreierSiteFiberEquivRoots p K Ω f).symm
        (artinSchreierFiberTranslate p K Ω f (-a) z)) =
        (artinSchreierSiteFiberEquivRoots p K Ω f).symm z := by
    rw [artinSchreierSiteFiberDeckEquiv_apply,
      artinSchreierSiteFiberEquivRoots_symm_translate,
      ← artinSchreierFiberTranslate_add, add_neg_cancel,
      artinSchreierFiberTranslate_zero]
  have h := Finsupp.mapDomain_apply d.injective v
    ((artinSchreierSiteFiberEquivRoots p K Ω f).symm
      (artinSchreierFiberTranslate p K Ω f (-a) z))
  rw [hi] at h
  exact h

/-- The full function-space conjugacy, with its proved inverse sign. -/
theorem artinSchreierSiteFreeEquivFunctions_deck (a : ZMod p)
    (v : (ModuleCat.free E).obj (ArtinSchreierSiteFiber p K Ω f)) :
    artinSchreierSiteFreeEquivFunctions p K Ω f E
        ((ModuleCat.free E).map
          ((Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.map
              (artinSchreierEtaleDeck p f a)) v) =
      fun z => artinSchreierSiteFreeEquivFunctions p K Ω f E v
        (artinSchreierFiberTranslate p K Ω f (-a) z) := by
  funext z
  exact artinSchreierSiteFreeEquivFunctions_deck_apply p K Ω f E a v z

end FiniteFunctions

#print axioms ArtinSchreierSiteFiber
#print axioms artinSchreierSiteFiberEquivRoots
#print axioms artinSchreierSiteFiberEquivRoots_val
#print axioms artinSchreierSiteFiberDeckEquiv
#print axioms artinSchreierSiteFiberDeckEquiv_apply
#print axioms artinSchreierSiteFiberEquivRoots_deck
#print axioms artinSchreierSiteFiberEquivRoots_symm_translate
#print axioms artinSchreierSiteFiber_nonempty
#print axioms artinSchreierSiteFiber_card
#print axioms artinSchreierSiteFiber_finite
#print axioms artinSchreierFiber_finite
#print axioms artinSchreierSiteFreeEquivFunctions
#print axioms artinSchreierSiteFreeEquivFunctions_apply
#print axioms artinSchreierSiteFreeEquivFunctions_deck_apply
#print axioms artinSchreierSiteFreeEquivFunctions_deck

end PrimeGap182.TypeIII
