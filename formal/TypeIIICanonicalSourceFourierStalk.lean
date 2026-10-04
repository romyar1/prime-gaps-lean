import TypeIIICanonicalFourierKernel
import TypeIIIFourierStalkInertia

/-!
# The canonical source construction's inertia-equivariant Fourier stalk

The general Fourier-base-change map uses the literal normalized AS
pullback, chosen from the same primitive source. All three individual
source specializations are then derived from the actual scheme maps and
inverse-image composition. The resulting Fourier-stalk equivalence has
no supplied family source-specialization premises.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CanonicalSourceFourierStalk

open PublishedPhysicalConstruction CanonicalCurveInput CanonicalLocalCorrelation
open GenericSourceSpecialization FourierSourceMaps FourierSourcePullbacks PulledCurveInput
open FourierStalkFromSources FourierStalkInertia PublishedPhaseApplication PublishedLocalConstruction
open CanonicalFourierKernel BoundaryFromSourceModels MiddleFromLocalization

universe u v w z a b c d e f g h i j k l o t
variable (K : Type u) [Field K]
  {Line : Type v} [Category.{w} Line] {Input : Type z} [Category.{a} Input]
  {GenericInput : Type b} [Category.{c} GenericInput] [MonoidalCategory GenericInput]
  {L : Type d} [Category.{e} L] [MonoidalCategory L]
  (P : GenericSourceSpecialization.PullbackComposition
    (Line := Line) (Input := Input) (GenericInput := GenericInput) K)
  (R : LocalPullbacks (L := L) K P)
  {Point : Type h} {GenericPoint : Type i}
  (D : CurveData Input Point) (DG : CurveData GenericInput GenericPoint)
  (LG : LineGeometry Line) (SR : ScalarPullbackRules (originalPullbackData K P) LG D)
  (kl as : Line) (hkl : Kl3Properties LG kl) (has : ASProperties LG as)
  {Q : Type f} [Category.{g} Q] (dualLocal : L → L) (middle : L ⥤ Q)
  [(localSpecialization K P R).Monoidal] (dualGeneric : GenericInputᵒᵖ ⥤ GenericInput)
  (T : SpecializationCompatibility (D := DG)
    (localSheafOperations K P R dualLocal middle) (localSpecialization K P R) dualGeneric)
  {C : Type j} [Category.{k} C] [Abelian C] {H : CohomologyData GenericInput C}
  {F : C ⥤ ModuleCat.{j} ℂ} {BS : BoundarySequence DG H F}
  {G0 : Type l} [Group G0] {Ginf : Type o} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) DG H F BS)
  (M : CompactificationData Z) (MR : CompactificationRules Z M)
  {I : Type t} [Group I] {Outer : Type c} [Group Outer]
  {LF : LocalFourierData K ℂ I Outer} (FO : FiniteOriginData Q LF)

/- General compact Fourier base change for every local input, with the
same chosen primitive AS source in the literal kernel map. -/
variable (FC : ∀ (s : PhaseField K) (hs : s ≠ 0) (A : L),
    ((FO.origin s hs (middle.obj A)).V ≃ₗ[ℂ]
      M.affine.obj (DG.tensor ((localSpecialization K P R).obj A)
        (additiveSource K P as (Units.mk0 s hs)))))

def canonicalFourierBaseChange :
    FourierBaseChange Z M (localSheafOperations K P R dualLocal middle)
      (localSpecialization K P R) FO where
  additive s hs := additiveSource K P as (Units.mk0 s hs)
  comparison s hs A := FC s hs A

variable (RF : FunctorInertia F Outer) (RM : FunctorInertia M.affine Outer)
  (RI : LocalizationInertia Z M RF RM)
  (BI : FourierInertia Z M RM (localSheafOperations K P R dualLocal middle)
    (localSpecialization K P R) FO (canonicalFourierBaseChange K P R DG as dualLocal middle Z M FO FC))
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (CRG : CurveRules DG) (alpha m n : Kˣ)
  (RP : PullbackProperties D DG (P.along (specializationMorphism K alpha m n)))

/-- The actual canonical pulled input's parabolic representation is the
Fourier representation at the exact standard parameters. The three
individual source identifications are conclusions of the map proofs. -/
def canonicalCoreFourierInertiaEquiv :
    Representation.Equiv
      (RF.rho (parabolicCore H (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP).input))
      (FO.origin (radialScale (alpha : K) (m : K))
        (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero)
        (perverseCorrelation (localSheafOperations K P R dualLocal middle)
          (localSource K P R kl) (angularUnit (m : K) (n : K) m.ne_zero n.ne_zero))).ρ :=
  coreStalkFourierInertiaEquiv Z M MR RF RM RI (localSheafOperations K P R dualLocal middle)
    (localSpecialization K P R) dualGeneric T FO
    (canonicalFourierBaseChange K P R DG as dualLocal middle Z M FO FC) BI
    (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP) CRG
    (localSource K P R kl) (angularUnit (m : K) (n : K) m.ne_zero n.ne_zero)
    (radialScale (alpha : K) (m : K))
    (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero)
    (firstSourceIso K P R alpha m n kl)
    (secondSourceIso K P R alpha m n kl ≪≫
      eqToIso (congrArg (fun lambda => (localSpecialization K P R).obj
        ((R.localEnd (FourierSourceMaps.scalarMorphism K lambda)).obj (localSource K P R kl)))
        (lambdaUnit_eq_angularUnit K m n)))
    (additiveSourceIso K P alpha m n as ≪≫
      eqToIso (congrArg (additiveSource K P as) (scaleUnit_eq_radialScale K alpha m)))

end PrimeGap182.TypeIII.CanonicalSourceFourierStalk

#print axioms PrimeGap182.TypeIII.CanonicalSourceFourierStalk.canonicalFourierBaseChange
#print axioms PrimeGap182.TypeIII.CanonicalSourceFourierStalk.canonicalCoreFourierInertiaEquiv
