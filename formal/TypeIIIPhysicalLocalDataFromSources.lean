import TypeIIIPhysicalEntryFourier
import TypeIIICanonicalSourceLocalData
import TypeIIIPhysicalLocalFamilyData

/-!
# Original physical local data constructed from shared source laws

The original physical IC tensor and its canonical Fourier cores now share
the same finite-origin records. General sheaf and individual-source laws
remain explicit; no finished local-family or physical-core comparison is
assumed. This is conditional on a compatible realization of those laws.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.PhysicalLocalDataFromSources

open PublishedPhysicalConstruction CanonicalCurveInput CanonicalLocalCorrelation
open GenericSourceSpecialization FourierSourceMaps FourierSourcePullbacks PulledCurveInput
open FourierStalkFromSources FourierStalkInertia PublishedPhaseApplication PublishedLocalConstruction
open CanonicalFourierKernel BoundaryFromSourceModels MiddleFromLocalization
open CanonicalSourceFourierStalk CohomologyInputTransport GenericCanonicalCore
open StartingSourceMaps GenericCurvePullback GenericCohomologyBaseChange OrdinaryBaseChangeFromDuality
open OriginalCoreFourierStalk GenericPhysicalEntry ConstantSignInertia PhysicalUnsignedInertia
open PhysicalTensorComparison PublishedApplicationBridge PublishedTypeIII
open PhysicalEntryFourier PhysicalLocalFamilyData CanonicalSourceLocalData
open RegularUnipotentRepresentation ConstantFieldLocalData PublishedMackey SelectedTensorTransport GeometricCoreRank

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

variable (TA : TorusArithmeticData p C0) (TR : TorusRules P0 O TA)
  {Obj : Type r} {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : PublishedSupportRules.RationalStalkRealization p SD}
  (IC : IntermediateExtensionData realization C0) (radial : Obj → FDRep ℂ Outer)
  (IR : InertiaCompatibility (BP (genericRadialMorphism (ZMod p)) ⋙ J) IC radial P0)


variable (ZF : ZeroFunctor DG Z)
  (tame : G0 →* Multiplicative ℂ) (htame : ∃ g, (tame g).toAdd ≠ 0)
  (ZK : ∀ lambda : (PhaseField (ZMod p))ˣ,
    Representation.Equiv
      (Z.zero ((localSpecialization (ZMod p) P R).obj
        (((localSheafOperations (ZMod p) P R dualLocal middle).scalar lambda).obj
          (localSource (ZMod p) P R kl)))).ρ (tameRepresentation tame))
  (ZA : ∀ s : (PhaseField (ZMod p))ˣ,
    Representation.Equiv (Z.zero (additiveSource (ZMod p) P as s)).ρ
      (Representation.trivial ℂ G0 ℂ))
  (point : GenericPoint) (V : GeometricFiberRules DG H (J ⋙ forgetInertia Outer) point)
  (Jinf : L ⥤ FDRep ℂ I) [Jinf.Monoidal]
  (IRinf : InfinityCompatibility (localSheafOperations (ZMod p) P R dualLocal middle) Jinf FO)
  {Cover : Type r} [Group Cover]
  (CC : CubicCoverData (PhaseField (ZMod p)) ℂ I Cover)
  (AS : LinearASData (PhaseField (ZMod p)) ℂ Cover)
  (PR : CubicCoverRules CC) (AR : LinearASRules CC AS)
  (KR : KloostermanInfinityRules p CC AS
    (sourceInfinity (localSheafOperations (ZMod p) P R dualLocal middle) Jinf
      (localSource (ZMod p) P R kl)))
  (FR : LocalFourierAdditivity LF) (FA : CubicInputAdmissibility CC AS LF)
  (SRF : FiniteOriginRules p FO) (hp : 3 < p)

/-- Coordinate coercion agrees with the existing geometric residue pair. -/
theorem residuePair_units (m m' : (ZMod p)ˣ) (i : Fin 2) :
    residuePair p (m : ZMod p) (m' : ZMod p) i =
      algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) ((![m, m'] i : (ZMod p)ˣ) : ZMod p) := by
  fin_cases i <;> rfl

/-- Construct all four finite-origin records and the physical tensor
comparison on the same objects. Rank, source specializations, individual
core comparisons and the completed local-family record are conclusions. -/
def physicalLocalDataFromSources (alpha m m' n n' : (ZMod p)ˣ) :
    PhysicalLocalData (H := H0) (P := P0)
      (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) O IC radial
      (cubicData (ZMod p) (AlgebraicClosure (ZMod p)) (cubicFourierData CC AS LF FA))
      alpha m m' n n' where
  cores := rectangleCores P R kl dualLocal middle FO alpha m m' n n'
  localData e := by
    have result := canonicalSourceCoreLocalData_overClosure (ZMod p) P R D DG LG SR
      kl as hkl has dualLocal middle dualGeneric T Z M MR FO FC ZF tame htame ZK ZA
      CRG alpha (![m, m'] e.1) (![n, n'] e.2) (RP alpha (![m, m'] e.1) (![n, n'] e.2))
      point V Jinf IRinf p CC AS PR AR KR FR FA SRF hp
    simpa only [residuePair_units, rectangleCores, fourierCore] using result
  tensor_comparison S :=
    isSubquotient_of_equiv
      (physicalTensorFourierEquiv P R D DG LG SR kl as hkl has dualLocal middle dualGeneric T J
        Z M MR FO FC RM RI BI CRG RP CR GC DT0 S0 GC' DTG SG HC BP CB PN tensorSource
        O PC ST degree inertia geometric RS TA TR IC radial IR alpha m m' n n' S)

end PrimeGap182.TypeIII.PhysicalLocalDataFromSources

#print axioms PrimeGap182.TypeIII.PhysicalLocalDataFromSources.physicalLocalDataFromSources

#print axioms PrimeGap182.TypeIII.PhysicalLocalDataFromSources.residuePair_units
