import TypeIIIEtaleOpenBaseChange
import TypeIIIKloostermanCompactification
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Extension by zero commutes with arbitrary inverse image

For an open immersion g and an arbitrary scheme morphism q, the
existing extension-by-zero functor followed by inverse image along q
is canonically isomorphic to inverse image on the open followed by
extension by zero into the cartesian source.

The two actual composite adjunctions have right adjoints q_* followed
by g^*, and g'^* followed by q'_*.  Their comparison is the already
proved original open base-change map.  Conjugating that isomorphism
constructs the comparison of the unchanged left adjoints.  The
conjugation identity records this relation explicitly.

The final specializations retain the original Kloosterman phase
extension by zero and literal scheme pullbacks.  This is an underived
compatibility, with no proper base-change or cohomological claim.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X U S : Scheme.{u}} (q : X ⟶ S) (g : U ⟶ S)
  [Etale g] (E : Type u) [Ring E]

/-- The actual adjunction for extension by zero followed by inverse image. -/
def sourceAdjunction :
    EtaleExtensionByZero.functor S (Scheme.Etale.mk g) E ⋙
        EtaleInverseImage.functor q E ⊣
      EtaleDirectImage.functor q E ⋙ EtaleInverseImage.functor g E :=
  (EtaleRestrictionInverseImage.extensionAdjunction S (Scheme.Etale.mk g) E).comp
    (EtaleInverseImage.adjunction q E)

/-- The actual adjunction for inverse image on the open followed by
extension by zero into the literal cartesian source. -/
def targetAdjunction :
    EtaleInverseImage.functor (pullback.snd q g) E ⋙
        EtaleExtensionByZero.functor X (Scheme.Etale.mk (pullback.fst q g)) E ⊣
      EtaleInverseImage.functor (pullback.fst q g) E ⋙
        EtaleDirectImage.functor (pullback.snd q g) E :=
  (EtaleInverseImage.adjunction (pullback.snd q g) E).comp
    (EtaleRestrictionInverseImage.extensionAdjunction X
      (Scheme.Etale.mk (pullback.fst q g)) E)

variable [Mono g]

/-- Actual extension by zero commutes with arbitrary inverse image,
by conjugating the proved open base-change isomorphism. -/
def iso :
    EtaleExtensionByZero.functor S (Scheme.Etale.mk g) E ⋙
        EtaleInverseImage.functor q E ≅
      EtaleInverseImage.functor (pullback.snd q g) E ⋙
        EtaleExtensionByZero.functor X (Scheme.Etale.mk (pullback.fst q g)) E :=
  ((conjugateIsoEquiv (sourceAdjunction q g E) (targetAdjunction q g E)).symm
    (EtaleOpenBaseChange.pullbackBaseChangeIso q g E)).symm

/-- Conjugation recovers the original proved open base-change isomorphism. -/
theorem iso_conjugate :
    conjugateIsoEquiv (sourceAdjunction q g E) (targetAdjunction q g E)
        (iso q g E).symm = EtaleOpenBaseChange.pullbackBaseChangeIso q g E :=
  Equiv.apply_symm_apply _ _

/-- On forward right-adjoint maps, this is precisely the original canonical mate. -/
theorem iso_conjugate_hom :
    (conjugateIsoEquiv (sourceAdjunction q g E) (targetAdjunction q g E)
        (iso q g E).symm).hom = EtaleInverseImage.pullbackBaseChangeMap q g E :=
  congrArg Iso.hom (iso_conjugate q g E)

end PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) (E : Type) [Ring E]

/-- The unchanged phase extension by zero commutes with inverse image
along any actual morphism into its original compactification. -/
def kloostermanPhaseExtensionByZero_inverseImageIso {T : Scheme.{0}}
    (q : T ⟶ kloostermanCompactificationScheme p) :
    kloostermanPhaseExtensionByZero p E ⋙ EtaleInverseImage.functor q E ≅
      EtaleInverseImage.functor
          (pullback.snd q (kloostermanCompactificationOpenImmersion p)) E ⋙
        EtaleExtensionByZero.functor T
          (Scheme.Etale.mk (pullback.fst q (kloostermanCompactificationOpenImmersion p))) E :=
  EtaleOpenExtensionBaseChange.iso q (kloostermanCompactificationOpenImmersion p) E

/-- In particular, arbitrary change of the original parameter base
commutes with the original phase extension by zero, on the literal
pulled-back compactification and its literal pulled-back open. -/
def kloostermanPhaseExtensionByZero_parameterBaseChangeIso {T : Scheme.{0}}
    (s : T ⟶ Spec (.of (Polynomial (ZMod p)))) :
    kloostermanPhaseExtensionByZero p E ⋙
        EtaleInverseImage.functor (pullback.fst (kloostermanCompactificationProjection p) s) E ≅
      EtaleInverseImage.functor
          (pullback.snd (pullback.fst (kloostermanCompactificationProjection p) s)
            (kloostermanCompactificationOpenImmersion p)) E ⋙
        EtaleExtensionByZero.functor (pullback (kloostermanCompactificationProjection p) s)
          (Scheme.Etale.mk
            (pullback.fst (pullback.fst (kloostermanCompactificationProjection p) s)
              (kloostermanCompactificationOpenImmersion p))) E :=
  kloostermanPhaseExtensionByZero_inverseImageIso p E
    (pullback.fst (kloostermanCompactificationProjection p) s)

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange.sourceAdjunction
#print axioms PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange.targetAdjunction
#print axioms PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange.iso
#print axioms PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange.iso_conjugate
#print axioms PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange.iso_conjugate_hom
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_inverseImageIso
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_parameterBaseChangeIso
