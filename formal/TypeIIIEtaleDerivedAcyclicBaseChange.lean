import TypeIIIDerivedBaseChangeAcyclic
import TypeIIIEtaleDerivedBaseChange

/-!
# The acyclic criterion for the actual small étale base-change map

The actual ordinary pullback mate is assumed invertible, and the actual
pullback of each injective sheaf is assumed acyclic for the direct image
on the cartesian fiber.  The proved acyclic-resolution theorem then makes
the existing derived pullback map invertible in every nonnegative degree.

All sheaf-category, exactness, injective-resolution, and derived-category
requirements are supplied by the existing constructions.  The two geometric
premises remain explicit.  In particular, this criterion does not deduce
either premise from properness.  The degree-zero square uses the original
ordinary mate and the canonical resolution augmentations.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable {X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S) (E : Type u) [Ring E]

set_option backward.isDefEq.respectTransparency false in
/-- The original derived pullback map satisfies the canonical degree-zero
square for every actual cartesian scheme square. -/
theorem pullbackBaseChangeMap_zero :
    Functor.whiskerRight (EtaleDirectImage.functor q E).toRightDerivedZero
        (EtaleInverseImage.functor g E) ≫
      EtaleDerivedBaseChange.pullbackBaseChangeMap q g E 0 =
    EtaleInverseImage.pullbackBaseChangeMap q g E ≫
      Functor.whiskerLeft (EtaleInverseImage.functor (pullback.fst q g) E)
        (EtaleDirectImage.functor (pullback.snd q g) E).toRightDerivedZero :=
  derivedBaseChangeMap_zero (EtaleDirectImage.functor q E)
    (EtaleDirectImage.functor (pullback.snd q g) E)
    (EtaleInverseImage.functor (pullback.fst q g) E) (EtaleInverseImage.functor g E)
    (EtaleInverseImage.pullbackBaseChangeMap q g E)

variable [IsIso (EtaleInverseImage.pullbackBaseChangeMap q g E)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Acyclicity of the actual pulled-back injectives and invertibility of the
original ordinary mate suffice for the same derived map to be invertible. -/
theorem pullbackBaseChangeMap_isIso_of_acyclic
    (h : ∀ (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)), Injective J →
      ∀ m : ℕ, IsZero
        ((EtaleDerivedDirectImage.functor (pullback.snd q g) E (m + 1)).obj
          ((EtaleInverseImage.functor (pullback.fst q g) E).obj J)))
    (n : ℕ) : IsIso (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n) := by
  let := HasDerivedCategory.standard
    (Sheaf (pullback q g).smallEtaleTopology (ModuleCat.{u} E))
  let := HasDerivedCategory.standard
    (Sheaf S'.smallEtaleTopology (ModuleCat.{u} E))
  rw [EtaleDerivedBaseChange.pullbackBaseChangeMap_eq]
  exact derivedBaseChangeMap_isIso_of_acyclic (EtaleDirectImage.functor q E)
    (EtaleDirectImage.functor (pullback.snd q g) E)
    (EtaleInverseImage.functor (pullback.fst q g) E) (EtaleInverseImage.functor g E)
    (EtaleInverseImage.pullbackBaseChangeMap q g E) h n

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism whose forward map is the existing actual derived pullback map. -/
def pullbackBaseChangeIso
    (h : ∀ (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)), Injective J →
      ∀ m : ℕ, IsZero
        ((EtaleDerivedDirectImage.functor (pullback.snd q g) E (m + 1)).obj
          ((EtaleInverseImage.functor (pullback.fst q g) E).obj J)))
    (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙ EtaleInverseImage.functor g E ≅
      EtaleInverseImage.functor (pullback.fst q g) E ⋙
        EtaleDerivedDirectImage.functor (pullback.snd q g) E n := by
  have : IsIso (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n) :=
    pullbackBaseChangeMap_isIso_of_acyclic q g E h n
  exact asIso (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n)

/-- No replacement natural transformation is used in the packaged isomorphism. -/
theorem pullbackBaseChangeIso_hom
    (h : ∀ (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)), Injective J →
      ∀ m : ℕ, IsZero
        ((EtaleDerivedDirectImage.functor (pullback.snd q g) E (m + 1)).obj
          ((EtaleInverseImage.functor (pullback.fst q g) E).obj J)))
    (n : ℕ) :
    (pullbackBaseChangeIso q g E h n).hom =
      EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n := rfl

/-- The packaged isomorphism retains the original ordinary mate and canonical
maps to zeroth derived direct image. -/
theorem pullbackBaseChangeIso_zero
    (h : ∀ (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)), Injective J →
      ∀ m : ℕ, IsZero
        ((EtaleDerivedDirectImage.functor (pullback.snd q g) E (m + 1)).obj
          ((EtaleInverseImage.functor (pullback.fst q g) E).obj J))) :
    Functor.whiskerRight (EtaleDirectImage.functor q E).toRightDerivedZero
        (EtaleInverseImage.functor g E) ≫
      (pullbackBaseChangeIso q g E h 0).hom =
    EtaleInverseImage.pullbackBaseChangeMap q g E ≫
      Functor.whiskerLeft (EtaleInverseImage.functor (pullback.fst q g) E)
        (EtaleDirectImage.functor (pullback.snd q g) E).toRightDerivedZero :=
  pullbackBaseChangeMap_zero q g E

end PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange

#print axioms PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange.pullbackBaseChangeMap_zero
#print axioms PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange.pullbackBaseChangeMap_isIso_of_acyclic
#print axioms PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange.pullbackBaseChangeIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange.pullbackBaseChangeIso_hom
#print axioms PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange.pullbackBaseChangeIso_zero
