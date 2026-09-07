import TypeIIIDerivedBaseChange
import TypeIIIEtaleDerivedDirectImage
import TypeIIIEtaleInverseImageComposition
import TypeIIIEtaleInverseImageStalk

/-!
# The actual derived base-change morphism on the small étale site

The existing ordinary mate and the proved exactness of inverse image
specialize the generic resolution construction to the actual module
sheaves.  All injective-resolution existence and exactness requirements
are discharged by proved instances.  The cartesian specialization uses
the literal scheme pullback, and the final construction applies it to
the unchanged Kloosterman compactification and existing extension by zero.

These are natural morphisms.  This module does not assert their
invertibility, a proper-base-change theorem, or an adic comparison.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleDerivedBaseChange

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

section Square

variable {X' X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S)
  (q' : X' ⟶ S') (g' : X' ⟶ X) (h : g' ≫ q = q' ≫ g) (E : Type u) [Ring E]

/-- The actual ordinary mate and actual exact-resolution comparison on homotopy categories. -/
def resolutionMap :
    EtaleDerivedDirectImage.toHomotopyCategory q E ⋙
        (EtaleInverseImage.functor g E).mapHomotopyCategory (ComplexShape.up ℕ) ⟶
      EtaleInverseImage.functor g' E ⋙ EtaleDerivedDirectImage.toHomotopyCategory q' E :=
  derivedBaseChangeResolutionMap (EtaleDirectImage.functor q E)
    (EtaleDirectImage.functor q' E) (EtaleInverseImage.functor g' E)
    (EtaleInverseImage.functor g E) (EtaleInverseImage.baseChangeMap q g q' g' h E)

/-- Its component is the class of the actual chain map on the chosen injective resolution. -/
theorem resolutionMap_app (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (resolutionMap q g q' g' h E).app F =
      (HomotopyCategory.quotient
        (Sheaf S'.smallEtaleTopology (ModuleCat.{u} E)) (ComplexShape.up ℕ)).map
          (derivedBaseChangeChainMap (EtaleDirectImage.functor q E)
            (EtaleDirectImage.functor q' E) (EtaleInverseImage.functor g' E)
            (EtaleInverseImage.functor g E) (EtaleInverseImage.baseChangeMap q g q' g' h E)
            (injectiveResolution F)) :=
  derivedBaseChangeResolutionMap_app (EtaleDirectImage.functor q E)
    (EtaleDirectImage.functor q' E) (EtaleInverseImage.functor g' E)
    (EtaleInverseImage.functor g E) (EtaleInverseImage.baseChangeMap q g q' g' h E) F

/-- The genuine natural morphism `g* Rⁿq_* → Rⁿq'_* g'*` for the actual commuting square. -/
def baseChangeMap (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙ EtaleInverseImage.functor g E ⟶
      EtaleInverseImage.functor g' E ⋙ EtaleDerivedDirectImage.functor q' E n :=
  derivedBaseChangeMap (EtaleDirectImage.functor q E)
    (EtaleDirectImage.functor q' E) (EtaleInverseImage.functor g' E)
    (EtaleInverseImage.functor g E) (EtaleInverseImage.baseChangeMap q g q' g' h E) n

/-- The component transports homology by actual inverse image and applies the resolution map. -/
theorem baseChangeMap_app (n : ℕ) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (baseChangeMap q g q' g' h E n).app F =
      (exactFunctorHomotopyHomologyIso (EtaleInverseImage.functor g E)
        (ComplexShape.up ℕ) n).inv.app
          ((EtaleDerivedDirectImage.toHomotopyCategory q E).obj F) ≫
        (HomotopyCategory.homologyFunctor
          (Sheaf S'.smallEtaleTopology (ModuleCat.{u} E)) (ComplexShape.up ℕ) n).map
            ((resolutionMap q g q' g' h E).app F) := rfl

end Square

section ActualPullback

variable {X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S) (E : Type u) [Ring E]

/-- The derived base-change morphism for the literal cartesian square of schemes. -/
def pullbackBaseChangeMap (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙ EtaleInverseImage.functor g E ⟶
      EtaleInverseImage.functor (pullback.fst q g) E ⋙
        EtaleDerivedDirectImage.functor (pullback.snd q g) E n :=
  baseChangeMap q g (pullback.snd q g) (pullback.fst q g)
    (pullback.condition (f := q) (g := g)) E n

/-- The cartesian construction uses the already proved actual ordinary pullback mate. -/
theorem pullbackBaseChangeMap_eq (n : ℕ) :
    pullbackBaseChangeMap q g E n =
      derivedBaseChangeMap (EtaleDirectImage.functor q E)
        (EtaleDirectImage.functor (pullback.snd q g) E)
        (EtaleInverseImage.functor (pullback.fst q g) E)
        (EtaleInverseImage.functor g E) (EtaleInverseImage.pullbackBaseChangeMap q g E) n := rfl

end ActualPullback

end PrimeGap182.TypeIII.EtaleDerivedBaseChange

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) {T : Scheme.{0}}
  (g : T ⟶ Spec (.of (Polynomial (ZMod p)))) (E : Type) [Ring E]

/-- The actual derived pullback morphism for the original compactification,
applied to the existing extension by zero. -/
def kloostermanCompactifiedDerivedBaseChange (n : ℕ) :
    kloostermanCompactifiedDerivedImage p E n ⋙ EtaleInverseImage.functor g E ⟶
      kloostermanPhaseExtensionByZero p E ⋙
        EtaleInverseImage.functor (pullback.fst (kloostermanCompactificationProjection p) g) E ⋙
          EtaleDerivedDirectImage.functor
            (pullback.snd (kloostermanCompactificationProjection p) g) E n :=
  Functor.whiskerLeft (kloostermanPhaseExtensionByZero p E)
    (EtaleDerivedBaseChange.pullbackBaseChangeMap (kloostermanCompactificationProjection p) g E n)

/-- Its component is exactly the actual pullback morphism on the unchanged extended sheaf. -/
theorem kloostermanCompactifiedDerivedBaseChange_app (n : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    (kloostermanCompactifiedDerivedBaseChange p g E n).app F =
      (EtaleDerivedBaseChange.pullbackBaseChangeMap
        (kloostermanCompactificationProjection p) g E n).app
          ((kloostermanPhaseExtensionByZero p E).obj F) := rfl

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.resolutionMap
#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.resolutionMap_app
#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.baseChangeMap
#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.baseChangeMap_app
#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.pullbackBaseChangeMap
#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.pullbackBaseChangeMap_eq
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedBaseChange
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedBaseChange_app
