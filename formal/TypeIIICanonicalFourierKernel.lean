import TypeIIIFourierSourcePullbacks
import TypeIIIPulledCurveInput

/-!
# The original canonical input specializes to the exact Fourier kernel

Both inputs are constructed from the same two primitive source objects.
The three source comparisons follow from actual scheme-map identities
and general inverse-image composition. Tensor/dual compatibility then
identifies the complete pulled original input with the canonical local
correlation and its normalized additive kernel. No individual source
specialization or completed-kernel isomorphism is supplied as a premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CanonicalFourierKernel

open PublishedPhysicalConstruction CanonicalCurveInput CanonicalLocalCorrelation
open GenericSourceSpecialization FourierSourceMaps FourierSourcePullbacks PulledCurveInput
open FourierStalkFromSources PublishedPhaseApplication

universe u v w z a b c d e f g h i
variable (K : Type u) [Field K]
  {Line : Type v} [Category.{w} Line] {Input : Type z} [Category.{a} Input]
  {GenericInput : Type b} [Category.{c} GenericInput] [MonoidalCategory GenericInput]
  {L : Type d} [Category.{e} L] [MonoidalCategory L]
  (P : GenericSourceSpecialization.PullbackComposition
    (Line := Line) (Input := Input) (GenericInput := GenericInput) K)
  (R : LocalPullbacks (L := L) K P)
  {Point : Type h} {GenericPoint : Type i}
  (D : CurveData Input Point) (DG : CurveData GenericInput GenericPoint)
  (LG : LineGeometry Line)
  (SR : ScalarPullbackRules (originalPullbackData K P) LG D)
  (kl as : Line) (hkl : Kl3Properties LG kl) (has : ASProperties LG as)

def canonicalOriginalInput : KloostermanInputData D :=
  canonicalInput (originalPullbackData K P) LG SR kl as hkl has

variable (alpha m n : Kˣ)
  (RP : PullbackProperties D DG (P.along (specializationMorphism K alpha m n)))

def canonicalPulledInput : KloostermanInputData DG :=
  pulledInput D DG (P.along (specializationMorphism K alpha m n)) RP
    (canonicalOriginalInput K P D LG SR kl as hkl has)

variable {Q : Type f} [Category.{g} Q] (dualLocal : L → L) (middle : L ⥤ Q)
  [(localSpecialization K P R).Monoidal] (dualGeneric : GenericInputᵒᵖ ⥤ GenericInput)
  (T : SpecializationCompatibility (D := DG)
    (localSheafOperations K P R dualLocal middle) (localSpecialization K P R) dualGeneric)

/-- The constructed target input has the exact correlation/kernel
recipe. All three individual source isomorphisms are derived here. -/
def canonicalKernelIso :
    (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP).input ≅
      DG.tensor
        ((localSpecialization K P R).obj
          (CanonicalLocalCorrelation.correlation (localSheafOperations K P R dualLocal middle)
            (localSource K P R kl) (lambdaUnit K m n)))
        (additiveSource K P as (scaleUnit K alpha m)) :=
  inputTensorIso (localSheafOperations K P R dualLocal middle) (localSpecialization K P R) dualGeneric T
    (inputTensorIso (localSheafOperations K P R dualLocal middle) (localSpecialization K P R) dualGeneric T
      (firstSourceIso K P R alpha m n kl)
      (inputDualIso (localSheafOperations K P R dualLocal middle) (localSpecialization K P R) dualGeneric T
        (secondSourceIso K P R alpha m n kl)) ≪≫
      specializedCorrelationIso (localSheafOperations K P R dualLocal middle)
        (localSpecialization K P R) dualGeneric T (localSource K P R kl) (lambdaUnit K m n))
    (additiveSourceIso K P alpha m n as)

/-- Match the precise angularUnit and radialScale parameters used by
the existing local Fourier and CoreLocalData constructors. -/
def canonicalKernelIso_standard :
    (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP).input ≅
      DG.tensor
        ((localSpecialization K P R).obj
          (CanonicalLocalCorrelation.correlation (localSheafOperations K P R dualLocal middle)
            (localSource K P R kl) (angularUnit (m : K) (n : K) m.ne_zero n.ne_zero)))
        (additiveSource K P as (Units.mk0 (radialScale (alpha : K) (m : K))
          (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero))) := by
  simpa only [lambdaUnit_eq_angularUnit, scaleUnit_eq_radialScale] using
    canonicalKernelIso K P R D DG LG SR kl as hkl has alpha m n RP dualLocal middle dualGeneric T

variable [MonoidalCategory Input]
  [(P.along (specializationMorphism K alpha m n)).Monoidal]
  (tensorSource : ∀ A B, D.tensor A B ≅ A ⊗ B)

/-- This starts with inverse image of the ORIGINAL canonical input.
The comparison includes its tensor and dual, not only its factors. -/
def pulledOriginalKernelIso :
    (P.along (specializationMorphism K alpha m n)).obj
      (canonicalOriginalInput K P D LG SR kl as hkl has).input ≅
      DG.tensor
        ((localSpecialization K P R).obj
          (CanonicalLocalCorrelation.correlation (localSheafOperations K P R dualLocal middle)
            (localSource K P R kl) (angularUnit (m : K) (n : K) m.ne_zero n.ne_zero)))
        (additiveSource K P as (Units.mk0 (radialScale (alpha : K) (m : K))
          (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero))) :=
  pulledInputIso D DG (P.along (specializationMorphism K alpha m n)) RP tensorSource T.tensor
    (canonicalOriginalInput K P D LG SR kl as hkl has) ≪≫
    canonicalKernelIso_standard K P R D DG LG SR kl as hkl has alpha m n RP dualLocal middle dualGeneric T

end PrimeGap182.TypeIII.CanonicalFourierKernel

#print axioms PrimeGap182.TypeIII.CanonicalFourierKernel.canonicalOriginalInput
#print axioms PrimeGap182.TypeIII.CanonicalFourierKernel.canonicalPulledInput
#print axioms PrimeGap182.TypeIII.CanonicalFourierKernel.canonicalKernelIso
#print axioms PrimeGap182.TypeIII.CanonicalFourierKernel.canonicalKernelIso_standard
#print axioms PrimeGap182.TypeIII.CanonicalFourierKernel.pulledOriginalKernelIso
