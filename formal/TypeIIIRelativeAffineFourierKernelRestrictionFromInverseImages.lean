import TypeIIIRelativeAffineFourierKernelFromActualCoordinates
import TypeIIIExactInverseImagesToDerived
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
The actual full relative source pullback/tensor kernel restricts to the
existing punctured universal pullback/tensor recipe. The whole natural
isomorphism uses only SAME ordinary inverse-image composition, monoidality,
and the proved coordinate identities. No selected kernel comparison or
ordinary extension exactness is assumed. Assignment to the independent
middle/full-Fourier ambient dictionaries is a separate remaining application.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.RelativeAffineFourierKernelRestrictionFromInverseImages
open GenericSourceSpecialization GenericRelativeAffineLineCoordinates
open FourierSourceMaps FourierNormalizationMaps PublishedPhaseApplication
open RelativeAffineFourierKernelFromActualCoordinates

universe mu
variable (K : Type) [Field K]
  (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : ExactInverseImagesToDerived.OrdinarySystem (fun X : Scheme.{0} => X) C)

def kernelFunctor (as : C (StartingSourceMaps.affineLine K)) :
    C (StartingSourceMaps.affineLine (PhaseField K)) ⥤ C (relativeAffineScheme K) :=
  U.pull (sourceMorphism K) ⋙ tensorRight ((U.pull (kernelMorphism K)).obj as)

def puncturedKernelFunctor (as : C (StartingSourceMaps.affineLine K)) :
    C (localScheme K) ⥤ C (genericScheme K) :=
  U.pull (projectionMorphism K) ⋙ tensorRight ((U.pull (universalKernelMorphism K)).obj as)

def sourceOpenPullIso :
    U.pull (sourceMorphism K) ⋙ U.pull (relativeOpenMorphism K) ≅
      U.pull (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) ⋙
        U.pull (projectionMorphism K) :=
  U.composition (relativeOpenMorphism K) (sourceMorphism K) ≪≫
    eqToIso (congrArg (fun f => U.pull f) (open_comp_sourceMorphism K)) ≪≫
      (U.composition (projectionMorphism K)
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K))).symm

def kernelOpenPullIso :
    U.pull (kernelMorphism K) ⋙ U.pull (relativeOpenMorphism K) ≅
      U.pull (universalKernelMorphism K) :=
  U.composition (relativeOpenMorphism K) (kernelMorphism K) ≪≫
    eqToIso (congrArg (fun f => U.pull f) (open_comp_kernelMorphism K))

variable [(U.pull (relativeOpenMorphism K)).Monoidal]

/-- A whole ALL-source-object natural isomorphism for the SAME full kernel,
including the original AS line object when instantiated at the prime. -/
def kernelRestrictionIso (as : C (StartingSourceMaps.affineLine K)) :
    kernelFunctor K C U as ⋙ U.pull (relativeOpenMorphism K) ≅
      U.pull (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) ⋙
        puncturedKernelFunctor K C U as :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (U.pull (sourceMorphism K))
      (Functor.Monoidal.commTensorRight (U.pull (relativeOpenMorphism K))
        ((U.pull (kernelMorphism K)).obj as)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sourceOpenPullIso K C U) _ ≪≫
    Functor.isoWhiskerLeft
      (U.pull (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) ⋙
        U.pull (projectionMorphism K))
      ((tensoringRight (C (genericScheme K))).mapIso ((kernelOpenPullIso K C U).app as)) ≪≫
    Functor.associator _ _ _

end PrimeGap182.TypeIII.RelativeAffineFourierKernelRestrictionFromInverseImages
