import TypeIIIArithmeticSourceMaps
import TypeIIIFourierSourcePullbacks
import TypeIIIGenericPhysicalEntry

/-!
# One inverse-image system for the source and parameter schemes

The index lists the actual schemes used by the construction, including
arithmetic curve fibers. General inverse-image functors, identity and
composition isomorphisms, and exact monoidal structure remain published
background inputs. All geometric, arithmetic and parameter pullbacks below
are restrictions of this same system. No primitive source or family estimate
is part of the system.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.SourceInverseImageSystem

open StartingSourceMaps GenericSourceSpecialization FourierSourceMaps
open FourierSourcePullbacks GenericCurvePullback PublishedPhysicalConstruction

inductive Space (K : Type) [Field K] where
  | line | source | genericCurve | localCurve | parameter | torus
  | arithmetic (E : Type) [Field E] [Algebra K E]

variable (K : Type) [Field K]

def scheme : Space K → Scheme
  | .line => affineLine K
  | .source => sourceScheme K
  | .genericCurve => genericScheme K
  | .localCurve => localScheme K
  | .parameter => parameterScheme K
  | .torus => PhysicalTorusMorphism.torusScheme K
  | @Space.arithmetic _ _ E fieldE _ => by
    letI := fieldE
    exact ArithmeticSourceMaps.fiberScheme E

universe v w

/-- A general inverse-image system on these schemes. Each fiber is an
ambient abelian monoidal sheaf category; the particular cohomology,
ramification, trace and source laws are separate inputs. -/
structure System where
  Obj : Space K → Type v
  [category : ∀ X, Category.{w} (Obj X)]
  [abelian : ∀ X, Abelian (Obj X)]
  [monoidal : ∀ X, MonoidalCategory (Obj X)]
  pull : ∀ {X Y}, (scheme K X ⟶ scheme K Y) → Obj Y ⥤ Obj X
  identity : ∀ X, pull (X := X) (Y := X) (𝟙 (scheme K X)) ≅ 𝟭 (Obj X)
  composition : ∀ {X Y Z} (f : scheme K X ⟶ scheme K Y) (g : scheme K Y ⟶ scheme K Z),
    pull g ⋙ pull f ≅ pull (X := X) (Y := Z) (f ≫ g)
  [pullMonoidal : ∀ {X Y} (f : scheme K X ⟶ scheme K Y), (pull f).Monoidal]
  [pullAdditive : ∀ {X Y} (f : scheme K X ⟶ scheme K Y), (pull f).Additive]
  [pullLimits : ∀ {X Y} (f : scheme K X ⟶ scheme K Y), PreservesFiniteLimits (pull f)]
  [pullColimits : ∀ {X Y} (f : scheme K X ⟶ scheme K Y), PreservesFiniteColimits (pull f)]

attribute [instance] System.category System.abelian System.monoidal
  System.pullMonoidal System.pullAdditive System.pullLimits System.pullColimits

variable {K} (B : System.{v,w} K)

abbrev System.geometricPullbacks :
    PullbackComposition (Line := B.Obj .line) (Input := B.Obj .source)
      (GenericInput := B.Obj .genericCurve) K where
  original f := B.pull (X := .source) (Y := .line) f
  generic f := B.pull (X := .genericCurve) (Y := .line) f
  along f := B.pull (X := .genericCurve) (Y := .source) f
  composition g f := B.composition (X := .genericCurve) (Y := .source) (Z := .line) g f

abbrev System.localPullbacks : LocalPullbacks (L := B.Obj .localCurve) K B.geometricPullbacks where
  restriction f := B.pull (X := .localCurve) (Y := .line) f
  fromLocal f := B.pull (X := .genericCurve) (Y := .localCurve) f
  localEnd f := B.pull (X := .localCurve) (Y := .localCurve) f
  localEnd_id := B.identity .localCurve
  localComposition g f := B.composition (X := .genericCurve) (Y := .localCurve) (Z := .line) g f
  localEndComposition g f := B.composition (X := .genericCurve) (Y := .localCurve) (Z := .localCurve) g f

abbrev System.arithmeticCategory (E : Type) [Field E] [Algebra K E] : Type v :=
  B.Obj (.arithmetic E)

abbrev System.arithmeticPullbacks (E : Type) [Field E] [Algebra K E] :
    ArithmeticSourceMaps.Pullbacks (Local := B.arithmeticCategory E) K E
      B.geometricPullbacks.original where
  specialized f := B.pull (X := .arithmetic E) (Y := .line) f
  along f := B.pull (X := .arithmetic E) (Y := .source) f
  localEnd f := B.pull (X := .arithmetic E) (Y := .arithmetic E) f
  composition g f := B.composition (X := .arithmetic E) (Y := .source) (Z := .line) g f
  scalarComposition g f := B.composition (X := .arithmetic E) (Y := .arithmetic E) (Z := .line) g f

abbrev System.parameterPullback (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K) :
    B.Obj .torus ⥤ B.Obj .parameter := B.pull (X := .parameter) (Y := .torus) f

variable {p : ℕ} [Fact p.Prime] (S : System.{v,w} (ZMod p))

abbrev System.torusOperations : TorusOperationData p (S.Obj .torus) where
  pullback f := S.pull (X := .torus) (Y := .torus) f

/-- The radial/physical composition is the same inverse-image compositor. -/
def System.parameterComposition :
    GenericPhysicalEntry.BasePullbackComposition S.torusOperations S.parameterPullback where
  comparison f g := (S.composition (X := .parameter) (Y := .torus) (Z := .torus) f g).symm

end PrimeGap182.TypeIII.SourceInverseImageSystem

#print axioms PrimeGap182.TypeIII.SourceInverseImageSystem.System.geometricPullbacks
#print axioms PrimeGap182.TypeIII.SourceInverseImageSystem.System.localPullbacks
#print axioms PrimeGap182.TypeIII.SourceInverseImageSystem.System.arithmeticPullbacks
#print axioms PrimeGap182.TypeIII.SourceInverseImageSystem.System.torusOperations
#print axioms PrimeGap182.TypeIII.SourceInverseImageSystem.System.parameterComposition
