import TypeIIIOriginalCoreFourierStalk
import TypeIIIPhysicalUnsignedInertia
import TypeIIIPhysicalTensorComparison

/-!
# Fourier identifications for the four original physical entries

The actual generic radial inverse-image functor is followed by the same
finite-dimensional inertia functor throughout. The constant sign is
removed by its degree-zero action on geometric inertia, and the original
core comparison is then applied. The four individual core comparisons
are constructed from this single formula, not supplied as hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.PhysicalEntryFourier

open PublishedPhysicalConstruction CanonicalCurveInput CanonicalLocalCorrelation
open GenericSourceSpecialization FourierSourceMaps FourierSourcePullbacks PulledCurveInput
open FourierStalkFromSources FourierStalkInertia PublishedPhaseApplication PublishedLocalConstruction
open CanonicalFourierKernel BoundaryFromSourceModels MiddleFromLocalization
open CanonicalSourceFourierStalk CohomologyInputTransport GenericCanonicalCore
open StartingSourceMaps GenericCurvePullback GenericCohomologyBaseChange OrdinaryBaseChangeFromDuality
open OriginalCoreFourierStalk GenericPhysicalEntry ConstantSignInertia PhysicalUnsignedInertia
open PhysicalTensorComparison PublishedApplicationBridge PublishedTypeIII

universe v w z a b c d e f g h i k l o t x y q r
variable {p : ℕ} [Fact p.Prime]
  {Line : Type v} [Category.{w} Line] {Input : Type z} [Category.{a} Input]
  {GenericInput : Type b} [Category.{c} GenericInput] [MonoidalCategory GenericInput]
  {L : Type d} [Category.{e} L] [MonoidalCategory L]
  (P : GenericSourceSpecialization.PullbackComposition
    (Line := Line) (Input := Input) (GenericInput := GenericInput) (ZMod p))
  (R : LocalPullbacks (L := L) (ZMod p) P)
  {Point : Type h} {GenericPoint : Type i}
  (D : CurveData Input Point) (DG : CurveData GenericInput GenericPoint)
  (LG : LineGeometry Line) (SR : ScalarPullbackRules (originalPullbackData (ZMod p) P) LG D)
  (kl as : Line) (hkl : Kl3Properties LG kl) (has : ASProperties LG as)
  {Q : Type f} [Category.{g} Q] (dualLocal : L → L) (middle : L ⥤ Q)
  [(localSpecialization (ZMod p) P R).Monoidal] (dualGeneric : GenericInputᵒᵖ ⥤ GenericInput)
  (T : SpecializationCompatibility (D := DG)
    (localSheafOperations (ZMod p) P R dualLocal middle) (localSpecialization (ZMod p) P R) dualGeneric)
  {Outer : Type c} [Group Outer]
  {C : Type} [Category.{k} C] [Abelian C] [MonoidalCategory C] {H : CohomologyData GenericInput C}
  (J : C ⥤ FDRep ℂ Outer) [J.Monoidal] {BS : BoundarySequence DG H (J ⋙ forgetInertia Outer)}
  {G0 : Type l} [Group G0] {Ginf : Type o} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) DG H (J ⋙ forgetInertia Outer) BS)
  (M : CompactificationData Z) (MR : CompactificationRules Z M)
  {I : Type t} [Group I]
  {LF : LocalFourierData (ZMod p) ℂ I Outer} (FO : FiniteOriginData Q LF)

/- General compact Fourier base change for every local input, with the
same chosen primitive AS source in the literal kernel map. -/
variable (FC : ∀ (s : PhaseField (ZMod p)) (hs : s ≠ 0) (A : L),
    ((FO.origin s hs (middle.obj A)).V ≃ₗ[ℂ]
      M.affine.obj (DG.tensor ((localSpecialization (ZMod p) P R).obj A)
        (additiveSource (ZMod p) P as (Units.mk0 s hs)))))
variable (RM : FunctorInertia M.affine Outer)
  (RI : LocalizationInertia Z M (FunctorInertia.ofFDRepFunctor J) RM)
  (BI : FourierInertia Z M RM (localSheafOperations (ZMod p) P R dualLocal middle)
    (localSpecialization (ZMod p) P R) FO (canonicalFourierBaseChange (ZMod p) P R DG as dualLocal middle Z M FO FC))
  [(J ⋙ forgetInertia Outer).Additive] [PreservesFiniteLimits (J ⋙ forgetInertia Outer)] [PreservesFiniteColimits (J ⋙ forgetInertia Outer)]
  (CRG : CurveRules DG)
  (RP : ∀ alpha m n : (ZMod p)ˣ, PullbackProperties D DG (P.along (specializationMorphism (ZMod p) alpha m n)))


variable {C0 : Type x} [Category.{y} C0] [Abelian C0] [MonoidalCategory C0]
  {H0 : CohomologyData Input C0} {P0 : ParameterData C0}
  (CR : CurveRules D) (GC : CohomologyRules D H0 P0)
  (DT0 : C0ᵒᵖ ⥤ C0) (S0 : RelativeDuality D (H := H0) (P := P0) DT0)
  {PG : ParameterData C} (GC' : CompactLissityRules DG (H := H) (P := PG))
  (DTG : Cᵒᵖ ⥤ C) (SG : RelativeDuality DG (H := H) (P := PG) DTG)
  (HC : FunctorialCohomology H)
  (BP : (parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p)) → C0 ⥤ C)

variable (CB : ∀ (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p))
    (g : genericScheme (ZMod p) ⟶ sourceScheme (ZMod p)),
    CoordinateBaseChange (ZMod p) g f →
      CompactBaseChange D DT0 DG DTG (BP f) (P.along g).obj (H := H0) (H' := H) (P := P0))
  (PN : ∀ (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p))
    (g : genericScheme (ZMod p) ⟶ sourceScheme (ZMod p))
    (sq : CoordinateBaseChange (ZMod p) g f),
    CompactPairingBaseChange D CR GC DT0 S0 DG DTG SG (BP f) (P.along g).obj
      (realizedCompactFunctor HC) (CB f g sq))
  [MonoidalCategory Input] [∀ alpha m n : (ZMod p)ˣ, (P.along (specializationMorphism (ZMod p) alpha m n)).Monoidal]
  (tensorSource : ∀ A B, D.tensor A B ≅ A ⊗ B)
  [∀ f, (BP f).Additive]
  [∀ f, PreservesFiniteLimits (BP f)]
  [∀ f, PreservesFiniteColimits (BP f)]


variable (O : TorusOperationData p C0)
  (PC : BasePullbackComposition O BP) [∀ f, (BP f).Monoidal]
  (ST : SignTensorData P0)
  {W : Type q} [Group W]
  (degree : W →* Multiplicative ℤ) (inertia : Outer →* W)
  (geometric : ∀ g, degree (inertia g) = 1)
  (RS : ∀ f, SignLineModel degree inertia ((BP f ⋙ J).obj ST.line))

/-- The precise Fourier core attached to one physical entry. -/
def fourierCore (alpha m n : (ZMod p)ˣ) : FDRep ℂ Outer :=
  FO.origin (radialScale (alpha : ZMod p) (m : ZMod p))
    (radialScale_ne_zero (alpha : ZMod p) (m : ZMod p) alpha.ne_zero m.ne_zero)
    (perverseCorrelation (localSheafOperations (ZMod p) P R dualLocal middle)
      (localSource (ZMod p) P R kl)
      (angularUnit (m : ZMod p) (n : ZMod p) m.ne_zero n.ne_zero))

/-- Inertia equivalence for the ORIGINAL signed, pulled physical entry. -/
def physicalEntryFourierEquiv (alpha m n : (ZMod p)ˣ) :
    Representation.Equiv
      ((BP (genericRadialMorphism (ZMod p)) ⋙ J).obj
        (pulledEntry (H := H0) (P := P0)
          (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) O alpha m n)).ρ
      (fourierCore P R kl dualLocal middle FO alpha m n).ρ :=
  (physicalUnsignedInertiaEquiv O BP PC J ST degree inertia geometric RS
    (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) alpha m n).trans
      (originalCoreFourierInertiaEquiv (ZMod p) P R D DG LG SR kl as hkl has
        dualLocal middle dualGeneric T Z M MR FO FC (FunctorInertia.ofFDRepFunctor J)
        RM RI BI CRG alpha m n (RP alpha m n) CR GC DT0 S0 GC' DTG SG HC BP CB PN tensorSource)


/-- The same single-entry formula defines all four actual Fourier cores. -/
def rectangleCores (alpha m m' n n' : (ZMod p)ˣ) (e : PhaseRectangle) : FDRep ℂ Outer :=
  fourierCore P R kl dualLocal middle FO alpha (![m, m'] e.1) (![n, n'] e.2)

/-- Discharge the four hcore identifications required by the physical
tensor comparison. No independently chosen core equivalence is supplied. -/
def matrixEntryFourierEquiv (alpha m m' n n' : (ZMod p)ˣ) (e : PhaseRectangle) :
    Representation.Equiv
      ((BP (genericRadialMorphism (ZMod p)) ⋙ J).obj
        (matrixEntry (H := H0) (P := P0)
          (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) O alpha m m' n n' e)).ρ
      (rectangleCores P R kl dualLocal middle FO alpha m m' n n' e).ρ :=
  physicalEntryFourierEquiv P R D DG LG SR kl as hkl has dualLocal middle dualGeneric T J
    Z M MR FO FC RM RI BI CRG RP CR GC DT0 S0 GC' DTG SG HC BP CB PN tensorSource
    O PC ST degree inertia geometric RS alpha (![m, m'] e.1) (![n, n'] e.2)

variable (TA : TorusArithmeticData p C0) (TR : TorusRules P0 O TA)
  {Obj : Type r} {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : PublishedSupportRules.RationalStalkRealization p SD}
  (IC : IntermediateExtensionData realization C0) (radial : Obj → FDRep ℂ Outer)
  (IR : InertiaCompatibility (BP (genericRadialMorphism (ZMod p)) ⋙ J) IC radial P0)

/-- The actual physical IC tensor has the canonical selected Fourier
representation. This derives the previous tensor-comparison premise
from source, base-change, sign and general restriction laws. -/
def physicalTensorFourierEquiv (alpha m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4)) :
    Representation.Equiv
      (radial (physicalObjects IC (entryObjects (H := H0) (P := P0)
        (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) O alpha m m' n n') S)).ρ
      (selectedTensor (rectangleSubset S)
        (fun e => signedRepresentation (conjugatedCorner e)
          (rectangleCores P R kl dualLocal middle FO alpha m m' n n' e))).ρ :=
  physicalTensorEquiv (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) CR GC O TA TR
    (BP (genericRadialMorphism (ZMod p)) ⋙ J) IC radial IR alpha m m' n n'
    (rectangleCores P R kl dualLocal middle FO alpha m m' n n')
    (matrixEntryFourierEquiv P R D DG LG SR kl as hkl has dualLocal middle dualGeneric T J
      Z M MR FO FC RM RI BI CRG RP CR GC DT0 S0 GC' DTG SG HC BP CB PN tensorSource
      O PC ST degree inertia geometric RS alpha m m' n n') S

end PrimeGap182.TypeIII.PhysicalEntryFourier

#print axioms PrimeGap182.TypeIII.PhysicalEntryFourier.fourierCore
#print axioms PrimeGap182.TypeIII.PhysicalEntryFourier.physicalEntryFourierEquiv

#print axioms PrimeGap182.TypeIII.PhysicalEntryFourier.rectangleCores
#print axioms PrimeGap182.TypeIII.PhysicalEntryFourier.matrixEntryFourierEquiv
#print axioms PrimeGap182.TypeIII.PhysicalEntryFourier.physicalTensorFourierEquiv
