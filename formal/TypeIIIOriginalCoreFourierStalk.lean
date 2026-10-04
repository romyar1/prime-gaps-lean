import TypeIIICanonicalSourceFourierStalk
import TypeIIIGenericCanonicalCore

/-!
# Original global parabolic core to its canonical Fourier representation

The curve inverse image used by compact base change is literally the one
used by the canonical source construction. Compact-cohomology functoriality
is taken from the same functorial support map used for input transport.
The proved Cartesian square, original parabolic base change, input
transport and source-derived Fourier comparison now compose equivariantly.

The arithmetic sign is still present in the separate physical entry and
is not discarded here. This endpoint concerns the original unsigned core.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.OriginalCoreFourierStalk

open PublishedPhysicalConstruction CanonicalCurveInput CanonicalLocalCorrelation
open GenericSourceSpecialization FourierSourceMaps FourierSourcePullbacks PulledCurveInput
open FourierStalkFromSources FourierStalkInertia PublishedPhaseApplication PublishedLocalConstruction
open CanonicalFourierKernel BoundaryFromSourceModels MiddleFromLocalization
open CanonicalSourceFourierStalk CohomologyInputTransport GenericCanonicalCore
open StartingSourceMaps GenericCurvePullback GenericCohomologyBaseChange OrdinaryBaseChangeFromDuality

universe u v w z a b c d e f g h i j k l o t x y
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
variable (RF : FunctorInertia F Outer) (RM : FunctorInertia M.affine Outer)
  (RI : LocalizationInertia Z M RF RM)
  (BI : FourierInertia Z M RM (localSheafOperations K P R dualLocal middle)
    (localSpecialization K P R) FO (canonicalFourierBaseChange K P R DG as dualLocal middle Z M FO FC))
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (CRG : CurveRules DG) (alpha m n : Kˣ)
  (RP : PullbackProperties D DG (P.along (specializationMorphism K alpha m n)))


variable {C0 : Type x} [Category.{y} C0] [Abelian C0]
  {H0 : CohomologyData Input C0} {P0 : ParameterData C0}
  (CR : CurveRules D) (GC : CohomologyRules D H0 P0)
  (DT0 : C0ᵒᵖ ⥤ C0) (S0 : RelativeDuality D (H := H0) (P := P0) DT0)
  {PG : ParameterData C} (GC' : CompactLissityRules DG (H := H) (P := PG))
  (DTG : Cᵒᵖ ⥤ C) (SG : RelativeDuality DG (H := H) (P := PG) DTG)
  (HC : FunctorialCohomology H)
  (BP : (parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K) → C0 ⥤ C)

/-- Share the actual curve inverse image with the source construction. -/
abbrev sourceInverseImages :
    InverseImages K (Input := Input) (Input' := GenericInput) (C := C0) (C' := C) where
  base := BP
  curve := P.along

/-- Use the compact functor of the same support-forgetting realization. -/
def realizedCompactFunctor : CompactFunctor (H' := H) where
  functor := HC.compact
  objectIso := HC.compactObject

variable (CB : ∀ (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (g : genericScheme K ⟶ sourceScheme K),
    CoordinateBaseChange K g f →
      CompactBaseChange D DT0 DG DTG (BP f) (P.along g).obj (H := H0) (H' := H) (P := P0))
  (PN : ∀ (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (g : genericScheme K ⟶ sourceScheme K)
    (sq : CoordinateBaseChange K g f),
    CompactPairingBaseChange D CR GC DT0 S0 DG DTG SG (BP f) (P.along g).obj
      (realizedCompactFunctor HC) (CB f g sq))
  [MonoidalCategory Input] [(P.along (specializationMorphism K alpha m n)).Monoidal]
  (tensorSource : ∀ A B, D.tensor A B ≅ A ⊗ B)
  [(BP (radialParameterMorphism K alpha m n)).Additive]
  [PreservesFiniteLimits (BP (radialParameterMorphism K alpha m n))]
  [PreservesFiniteColimits (BP (radialParameterMorphism K alpha m n))]

/-- The ORIGINAL global core restricts to the exact canonical Fourier
representation. Its input, parabolic-image and source-specialization
identifications are all derived, rather than supplied family premises. -/
def originalCoreFourierInertiaEquiv :
    Representation.Equiv
      (RF.rho ((BP (radialParameterMorphism K alpha m n)).obj
        (parabolicCore H0 (canonicalOriginalInput K P D LG SR kl as hkl has).input)))
      (FO.origin (radialScale (alpha : K) (m : K))
        (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero)
        (perverseCorrelation (localSheafOperations K P R dualLocal middle)
          (localSource K P R kl) (angularUnit (m : K) (n : K) m.ne_zero n.ne_zero))).ρ :=
  (RF.mapEquiv (genericCanonicalCoreIso K D CR GC DT0 S0 DG CRG GC' DTG SG
    (realizedCompactFunctor HC) (sourceInverseImages K P BP) CB PN alpha m n RP
    tensorSource T.tensor HC (canonicalOriginalInput K P D LG SR kl as hkl has))).trans
      (canonicalCoreFourierInertiaEquiv K P R D DG LG SR kl as hkl has dualLocal middle
        dualGeneric T Z M MR FO FC RF RM RI BI CRG alpha m n RP)

end PrimeGap182.TypeIII.OriginalCoreFourierStalk

#print axioms PrimeGap182.TypeIII.OriginalCoreFourierStalk.sourceInverseImages
#print axioms PrimeGap182.TypeIII.OriginalCoreFourierStalk.realizedCompactFunctor
#print axioms PrimeGap182.TypeIII.OriginalCoreFourierStalk.originalCoreFourierInertiaEquiv
