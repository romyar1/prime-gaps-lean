import TypeIIIAlgebraicConstantFieldCommonTraitTransport02
import TypeIIICanonicalLocalWeilFiberFromGroupDictionaryRoot05
import Mathlib.Algebra.Group.ULift

/-! Pure conditional common arithmetic trait cone. Two individual dictionaries
identify independently interpreted standard origin/infinity groups with the
positive completed traits. Their geometric meaning and existence stay MODEL
cuts. Every native group/fiber/Weil representation is computed from them using
SAME finite-field scalar algebra and actual monoidal realization structures.
No arbitrary old native choice is identified, no standard degree/normal form
law is assumed, and no completed boundary record family is a premise. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct MonoidalCategory
namespace PrimeGap182.TypeIII.NativeCommonArithmeticTraitWeilCone
open NativeWildRecognitionFromFixedGeometricTraits
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open LocalWeilAction
universe u v nu g t

abbrev OriginTraitDictionary (S : StandardGmPrimitives.{nu})
    (B : Primitives.{nu,0,0} S) :=
  ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    B.OriginGroup E h2 ≃* TraitGroup (AlgebraicClosure E)

abbrev InfinityTraitDictionary (S : StandardGmPrimitives.{nu})
    (B : Primitives.{nu,0,0} S) :=
  ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    B.InfinityGroup E h2 ≃* TraitGroup (AlgebraicClosure E)

abbrev CommonOrigin (K : Type) [Field K] :=
  ULift.{g,0} (TraitGroup (AlgebraicClosure K))

abbrev CommonInfinity (K : Type) [Field K] :=
  ULift.{t,0} (TraitGroup (AlgebraicClosure K))

variable (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E]
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (originTrait : OriginTraitDictionary S B)
  (infinityTrait : InfinityTraitDictionary S B) (h2 : (2 : E) ≠ 0)

def commonCoefficientEquiv :
    TraitGroup (AlgebraicClosure K) ≃* TraitGroup (AlgebraicClosure E) := by
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  exact AlgebraicConstantFieldCommonTraitTransport.coefficientGroupEquiv K E

def originEquiv : CommonOrigin.{g} K ≃* B.OriginGroup E h2 :=
  (MulEquiv.ulift : CommonOrigin.{g} K ≃* TraitGroup (AlgebraicClosure K)).trans
    (commonCoefficientEquiv K E) |>.trans (originTrait E h2).symm

def infinityEquiv : CommonInfinity.{t} K ≃* B.InfinityGroup E h2 :=
  (MulEquiv.ulift : CommonInfinity.{t} K ≃* TraitGroup (AlgebraicClosure K)).trans
    (commonCoefficientEquiv K E) |>.trans (infinityTrait E h2).symm

abbrev CommonWeil := ULift.{g,0} ((B.originWeil E h2).Weil)

def weilEquiv : CommonWeil.{nu,g} E B h2 ≃* (B.originWeil E h2).Weil :=
  MulEquiv.ulift

variable {Local : Type u} [Category.{v} Local]
  (realization : Local ⥤ S.Curve E h2)

def fiber : Local ⥤ FDRep ℂ (CommonOrigin.{g} K) :=
  CanonicalLocalWeilFiberFromGroupDictionary.fiber realization (B.origin E h2)
    (originEquiv K E B originTrait h2)

def conjugation : CommonOrigin.{g} K →* CommonOrigin.{g} K :=
  CanonicalLocalWeilFiberFromGroupDictionary.conjugation (B.originConjugation E h2)
    (originEquiv K E B originTrait h2)

def weilData : Data (fiber K E B originTrait h2 realization)
    (conjugation K E B originTrait h2) :=
  CanonicalLocalWeilFiberFromGroupDictionary.weilData realization (B.origin E h2)
    (B.originConjugation E h2) (B.originWeil E h2)
    (originEquiv K E B originTrait h2) (weilEquiv E B h2)

variable [MonoidalCategory Local]
  (realizationMonoidal :
    letI : MonoidalCategory (S.Curve E h2) := B.curveMonoidal E h2
    realization.Monoidal)

abbrev fiberMonoidal : (fiber K E B originTrait h2 realization).Monoidal := by
  letI : MonoidalCategory (S.Curve E h2) := B.curveMonoidal E h2
  letI : realization.Monoidal := realizationMonoidal
  exact CanonicalLocalWeilFiberFromGroupDictionary.fiberMonoidal realization (B.origin E h2)
    (originEquiv K E B originTrait h2)

/-- Exact original primitive record. The whole-Weil equation is reflexive for
these computed representations, and needs no degree/normal-form/injectivity cut. -/
def primitiveData :
    letI : MonoidalCategory (S.Curve E h2) := B.curveMonoidal E h2
    letI : realization.Monoidal := realizationMonoidal
    letI : (fiber K E B originTrait h2 realization).Monoidal :=
      fiberMonoidal K E B originTrait h2 realization realizationMonoidal
    ArithmeticBoundaryPrimitiveWeilRealization.PrimitiveData
    (Gi := CommonInfinity.{t} K) (StandardGi := B.InfinityGroup E h2)
    (fiber K E B originTrait h2 realization) (conjugation K E B originTrait h2)
    (weilData K E B originTrait h2 realization) realization (B.origin E h2)
    (B.originConjugation E h2) (B.originWeil E h2) := by
  letI : MonoidalCategory (S.Curve E h2) := B.curveMonoidal E h2
  letI : realization.Monoidal := realizationMonoidal
  letI : (fiber K E B originTrait h2 realization).Monoidal :=
    fiberMonoidal K E B originTrait h2 realization realizationMonoidal
  exact {
  originGroup := originEquiv K E B originTrait h2
  infinityGroup := infinityEquiv K E B infinityTrait h2
  coefficient := CanonicalLocalWeilFiberFromGroupDictionary.coefficientIso realization
    (B.origin E h2) (originEquiv K E B originTrait h2)
  coefficientUnit := (CanonicalLocalWeilFiberFromGroupDictionary.chosenLiftData.{u,v,0,nu,g,0,t,0} realization
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (originEquiv K E B originTrait h2) (infinityEquiv K E B infinityTrait h2)
    (weilEquiv E B h2)).coefficientUnit
  coefficientTensor := (CanonicalLocalWeilFiberFromGroupDictionary.chosenLiftData.{u,v,0,nu,g,0,t,0} realization
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (originEquiv K E B originTrait h2) (infinityEquiv K E B infinityTrait h2)
    (weilEquiv E B h2)).coefficientTensor
  weilMap := (weilEquiv E B h2).toMonoidHom
  inertia_eq := (CanonicalLocalWeilFiberFromGroupDictionary.chosenLiftData.{u,v,0,nu,g,0,t,0} realization
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (originEquiv K E B originTrait h2) (infinityEquiv K E B infinityTrait h2)
    (weilEquiv E B h2)).inertia_eq
  frobenius_eq := (CanonicalLocalWeilFiberFromGroupDictionary.chosenLiftData.{u,v,0,nu,g,0,t,0} realization
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (originEquiv K E B originTrait h2) (infinityEquiv K E B infinityTrait h2)
    (weilEquiv E B h2)).frobenius_eq
  wholeWeil := CanonicalLocalWeilFiberFromGroupDictionary.wholeWeil.{u,v,0,nu,g,0} realization
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (originEquiv K E B originTrait h2) (weilEquiv E B h2)

  }

end PrimeGap182.TypeIII.NativeCommonArithmeticTraitWeilCone
