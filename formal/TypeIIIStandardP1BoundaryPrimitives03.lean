import TypeIIIStandardGmTraceFromFaithfulArithmeticOperations02
import TypeIIIArithmeticBoundaryRecordsFromGuardedFiniteFiberOperations01

/-! Independently specified standard P1 localization primitives.
These data contain no native C/U/J/H/Weil operations. The interpretation
predicate is prescribed to mean continuous constructible Qbar2 coefficients,
the genuine Gm open in P1, its closed-stalk localization diagram and actual
geometric inertia/Weil fibers, followed by the SAME fixed Qbar2-to-C embedding.
Its existence remains an external MODEL cut. Published theorems are separate
from primitives and interpretation; no native finished boundary record occurs.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.StandardP1BoundaryPrimitives
open StandardGmTraceFromFaithfulArithmeticOperations PublishedPhysicalConstruction
open ArithmeticBoundaryFromCanonicalLocalization LocalWeilAction
open ArithmeticDualFromCanonicalEvaluation
universe nu g t

/-- Standard independent operations on every finite field of odd characteristic.
The connecting transformation is the canonical localization transgression;
it is standard primitive data, never a native connecting-map callback. -/
structure Primitives (S : StandardGmPrimitives.{nu}) where
  [specAbelian : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Abelian (S.Spec E h2)]
  [curveMonoidal : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    MonoidalCategory (S.Curve E h2)]
  curve : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    CurveData (S.Curve E h2) Unit
  dual : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    (S.Curve E h2)ᵒᵖ ⥤ S.Curve E h2
  evaluation : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (A : S.Curve E h2), (dual E h2).obj (op A) ⊗ A ⟶ 𝟙_ (S.Curve E h2)
  OriginGroup : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0), Type g
  InfinityGroup : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0), Type t
  [originGroup : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Group (OriginGroup E h2)]
  [infinityGroup : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Group (InfinityGroup E h2)]
  origin : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    S.Curve E h2 ⥤ FDRep ℂ (OriginGroup E h2)
  infinity : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    S.Curve E h2 ⥤ FDRep ℂ (InfinityGroup E h2)
  [originMonoidal : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    (origin E h2).Monoidal]
  originConjugation : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    OriginGroup E h2 →* OriginGroup E h2
  originWeil : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    LocalWeilAction.Data.{0,nu,g} (origin E h2) (originConjugation E h2)
  infinityConjugation : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    InfinityGroup E h2 →* InfinityGroup E h2
  infinityWeil : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    LocalWeilAction.Data.{0,nu,t} (infinity E h2) (infinityConjugation E h2)
  ordinary : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    S.Curve E h2 ⥤ S.Spec E h2
  support : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    S.compact E h2 1 ⟶ ordinary E h2
  boundary : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    S.Curve E h2 ⥤ S.Spec E h2
  closedStalkComparison : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (A : S.Curve E h2),
    (S.fiber E h2).obj ((boundary E h2).obj A) ≃ₗ[ℂ]
      (Representation.invariants ((origin E h2).obj A).ρ ×
       Representation.invariants ((infinity E h2).obj A).ρ)
  localizationConnecting : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    boundary E h2 ⟶ S.compact E h2 1
  globalSections : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    S.Curve E h2 → ModuleCat.{0} ℂ
  globalBoundary : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (A : S.Curve E h2), globalSections E h2 A →ₗ[ℂ]
      (S.fiber E h2).obj ((boundary E h2).obj A)
  projective : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    S.Curve E h2 → ModuleCat.{0} ℂ
  compactToProjective : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (A : S.Curve E h2), (S.fiber E h2).obj ((S.compact E h2 1).obj A) →ₗ[ℂ]
      projective E h2 A
  leray : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (A : S.Curve E h2), projective E h2 A →ₗ[ℂ]
      (S.fiber E h2).obj ((ordinary E h2).obj A)

attribute [instance] Primitives.originGroup Primitives.infinityGroup Primitives.originMonoidal
variable {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,g,t} S)
  (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)

/-- Standard compact/ordinary/support H1 are literal primitive functors. -/
def cohomology : CohomologyData (S.Curve E h2) (S.Spec E h2) where
  compact := (S.compact E h2 1).obj
  ordinary := (B.ordinary E h2).obj
  comparison := (B.support E h2).app

/-- Assemble only the standard canonical operation diagram; no laws are fields. -/
def localization : LocalizationData (cohomology B E h2) (S.fiber E h2)
    (B.origin E h2) (B.infinity E h2) where
  boundaryObject := (B.boundary E h2).obj
  comparison := B.closedStalkComparison E h2
  connecting := (B.localizationConnecting E h2).app
  globalSections := B.globalSections E h2
  globalBoundary := B.globalBoundary E h2
  projective := B.projective E h2
  compactToProjective := B.compactToProjective E h2
  leray := B.leray E h2

/-- Individually prescribed general standard theorems, separate from MODEL.
The interpretation reads only S/B and actual standard coefficient geometry.
It contains NO native operator, native J/Weil, delta or finished record. -/
structure PublishedTheorems
    (interpretation : ∀ S : StandardGmPrimitives.{nu}, Primitives.{nu,g,t} S → Prop) : Prop where
  localization : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,g,t} S),
    interpretation S B → ∀ (p : ℕ) [Fact p.Prime] (h2p : 2 ≠ p)
      (E : Type) [Field E] [Fintype E] [CharP E p] (h2 : (2 : E) ≠ 0),
      LocalizationLaws (B.curve E h2) (StandardP1BoundaryPrimitives.localization B E h2) p h2p
  positive : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,g,t} S),
    interpretation S B → ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
      (A : S.Curve E h2), (B.curve E h2).Isoclinic A 1 →
      Representation.invariants ((B.infinity E h2).obj A).ρ = ⊥
  rigid : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,g,t} S),
    interpretation S B → ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
      letI := B.curveMonoidal E h2
      letI := B.originMonoidal E h2
      ∀ (A : S.Curve E h2), (B.curve E h2).Lisse A →
      Function.Bijective (canonicalDualMap (B.origin E h2) (B.dual E h2) (B.evaluation E h2) A)
  localStalkAction : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,g,t} S),
    interpretation S B → ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
      (A : S.Curve E h2) (x : (S.fiber E h2).obj ((B.boundary E h2).obj A)),
      B.closedStalkComparison E h2 A (((S.geometricFrobenius E h2).app ((B.boundary E h2).obj A)).hom x) =
        (ArithmeticBoundaryFromInvariantFunctors.invariantAction ((B.origin E h2).obj A)
          ((B.originWeil E h2).localFrobenius.action A) (B.originConjugation E h2)
          ((B.originWeil E h2).covariance A)
          (B.closedStalkComparison E h2 A x).1,
         ArithmeticBoundaryFromInvariantFunctors.invariantAction ((B.infinity E h2).obj A)
          ((B.infinityWeil E h2).localFrobenius.action A) (B.infinityConjugation E h2)
          ((B.infinityWeil E h2).covariance A)
          (B.closedStalkComparison E h2 A x).2)

end PrimeGap182.TypeIII.StandardP1BoundaryPrimitives
