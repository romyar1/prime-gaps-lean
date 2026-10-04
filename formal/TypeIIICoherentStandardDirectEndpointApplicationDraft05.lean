import TypeIIIPhysicalLocalDataFromSources
import TypeIIICanonicalPhysicalFamily
import TypeIIIFuFromQuadraticPullback
import TypeIIIPublishedTorusEndpoint
import TypeIIICoherentComputedRadialProjection01

/-!
# NEW direct standard application on the computed canonical physical (canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR)

This source composes the SURVIVING canonical source, physical-(canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR),
local-(canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR) and endpoint APIs; it replaces a supplied finished FuRules
record by the GENERAL monomial/quadratic application inputs and derives
both exact torus branches. Radial profile/phase recognition is definitional.

All maps, original cohomology comparison/image, signed core, four torus
entries, IC objects and whole Weil lifts are the SAME canonical recipe.
No supplied (canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR) profile, rank-six, transformed full support, norm bound,
physical complexity (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap) or uniform Application provider is accepted.

This is still CONDITIONAL on one compatible genuine standard realization
of the GENERAL operator/constructibility/eligibility laws. The explicit
CohomologicalRealization includes specialized original primitive trace
and arithmetic boundary obligations; those have NOT been assembled here.
The source does NOT claim existence of the coherent adic theory, a current
Lean PASS, UniformApplications, or complete Type III.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CoherentStandardDirectEndpointApplicationDraft04

open PublishedPhysicalConstruction CanonicalCurveInput CanonicalLocalCorrelation
open GenericSourceSpecialization FourierSourceMaps FourierSourcePullbacks PulledCurveInput
open FourierStalkFromSources FourierStalkInertia PublishedPhaseApplication PublishedLocalConstruction
open CanonicalFourierKernel BoundaryFromSourceModels MiddleFromLocalization
open CanonicalSourceFourierStalk CohomologyInputTransport GenericCanonicalCore
open StartingSourceMaps GenericCurvePullback GenericCohomologyBaseChange OrdinaryBaseChangeFromDuality
open OriginalCoreFourierStalk GenericPhysicalEntry ConstantSignInertia PhysicalUnsignedInertia
open PhysicalTensorComparison PublishedApplicationBridge PublishedTypeIII
open PhysicalEntryFourier PhysicalLocalFamilyData CanonicalSourceLocalData
open CanonicalPhysicalFamily PhysicalLocalDataFromSources
open CoherentComputedRadialProjection01
open StartingSourceComplexity PublishedConstructionComplexity PublishedPolynomialComplexity
open RegularUnipotentRepresentation ConstantFieldLocalData PublishedMackey SelectedTensorTransport GeometricCoreRank

universe v w z a b c d e f g h i k l o t x y q r s
/- The (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)-generating functions and numerical witnesses are fixed BEFORE
selecting the characteristic or any physical residue parameters. -/
variable (boundFn : ℕ → ℕ) (sourceCap0 unitCap : ℕ)
  (bnd : PublishedUniformComplexity.Bounds)

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
  (baseTheory : Theory.{r,s} p)
  (PD : PhaseData (ZMod p) ℂ Outer)
  (nativeRadial : baseTheory.Obj → FDRep ℂ Outer)
  (radialLaws : PublishedFourierRules.LocalRules baseTheory.data baseTheory.coefficient
    (computedFourierData baseTheory.fourier
      (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial))

/- The two radial observers are DEFINED by the same chosen genuine wild
functor. radialLaws is a GENERAL all-object projection, not a (canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR)
profile or a completed interpretation predicate. -/

variable (UR : PublishedUniformComplexity.Rules bnd (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws))
  (traceData : PublishedCovarianceRules.TraceData p ((computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws)).realization)
  (IC : IntermediateExtensionData ((computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws)).realization C0)


variable (IR : InertiaCompatibility (p := p) (BP (genericRadialMorphism (ZMod p)) ⋙ J)
  IC nativeRadial P0)

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


/- The arithmetic realization is still explicit. In particular, its
originalTraces and localBoundary fields have not yet been assembled from
the separate arithmetic source results on this same realization. -/
variable (AM : CohomologicalRealization D H0 P0
    (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) TA)
  (ICR : IntermediateExtensionRules ((computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws)).traceWeights traceData P0 TA IC)
  (ci : Input → ℕ) (cp : C0 → ℕ)
  (cm : TorusMorphismComplexity (ZMod p))
  (QB : OperationBounds (D := D) (H := H0) (P := P0) boundFn unitCap ci cp cm O IC)
  (QM : TorusPolynomialRules cm)
  (SC : PrimitiveClasses Line) (cl : Line → ℕ) (cs : MorphismComplexity (ZMod p))
  (QS : StartingSourceComplexity.Bounds (originalPullbackData (ZMod p) P)
    SC boundFn sourceCap0 cl ci cs)
  (QSM : PolynomialRules (ZMod p) cs)
  (hhyper : SC.Hypergeometric kl 3) (hAS : SC.NontrivialArtinSchreier as)


include P R D DG LG SR kl as hkl has
  dualLocal middle dualGeneric T J Z M MR FO FC
  RM RI BI CRG RP CR GC DT0 S0 GC'
  DTG SG HC BP CB PN tensorSource O PC ST
  degree inertia geometric RS TA TR baseTheory PD nativeRadial radialLaws
  UR traceData IC IR ZF tame htame ZK ZA point
  V Jinf IRinf CC AS PR AR KR FR FA
  SRF hp AM ICR boundFn sourceCap0 unitCap ci cp cm
  QB QM SC cl cs QS QSM hhyper hAS bnd

/-- Construct the original LocalFamilyData on the same canonical physical
(canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR), using the source-derived Fourier cores and finite-origin maps.
No completed local record, hcore, subset comparison or (canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR) equality
is supplied to this constructor. -/
def sourceLocalFamilyData (alpha m m' n n' : (ZMod p)ˣ) :
    LocalFamilyData (computedUniformRadialRealization baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws bnd UR) ((canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR) alpha m m' n n')
      (cubicData (ZMod p) (AlgebraicClosure (ZMod p)) (cubicFourierData CC AS LF FA)) :=
  PhysicalLocalData.toLocalFamilyData (theory := UR.theory)
    (canonicalOriginalInput (ZMod p) P D LG SR kl as hkl has) O IC (computedUniformRadialRealization baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws bnd UR)
    (physicalLocalDataFromSources P R D DG LG SR kl as hkl has dualLocal middle dualGeneric T J
      Z M MR FO FC RM RI BI CRG RP CR GC DT0 S0 GC' DTG SG HC BP CB PN tensorSource
      O PC ST degree inertia geometric RS TA TR IC ((computedUniformRadialRealization baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws bnd UR)).inertia IR ZF tame htame ZK ZA
      point V Jinf IRinf CC AS PR AR KR FR FA SRF hp alpha m m' n n') _ rfl

variable (phaseLaws : PhaseRules PD)
  (fuGeometry : FuFromQuadraticPullback.Inputs p PD (cubicFourierData CC AS LF FA))
  (sigma : ℂ ≃+* ℂ)
  (hsigma : ∀ t : ZMod p, sigma (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t))
  (chebotarev : PublishedCovarianceRules.ChebotarevRules (T := UR.theory.coefficient) traceData sigma)
  (fourierCovariance : PublishedCovarianceRules.FourierCovarianceRules
    (T := UR.theory.coefficient) (F := UR.theory.fourier)
    (Units.mk0 2 (prime_two_ne_zero p hp)))

include P R D DG LG SR kl as hkl has
  dualLocal middle dualGeneric T J Z M MR FO FC
  RM RI BI CRG RP CR GC DT0 S0 GC'
  DTG SG HC BP CB PN tensorSource O PC ST
  degree inertia geometric RS TA TR baseTheory PD nativeRadial radialLaws
  UR traceData IC IR ZF tame htame ZK ZA point
  V Jinf IRinf CC AS PR AR KR FR FA
  SRF hp AM ICR boundFn sourceCap0 unitCap ci cp cm
  QB QM SC cl cs QS QSM hhyper hAS bnd
  phaseLaws fuGeometry sigma hsigma chebotarev fourierCovariance

/-- Combined application on the original physical objects, conditional on
the explicit common source/sheaf laws and arithmetic realization.
All finished local-(canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR), trace, phase-list and quantitative-(canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR)
premises are derived inside this constructor. -/
def sourceApplication (alpha m m' n n' : (ZMod p)ˣ) :
    Application (bnd.stalkCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) (bnd.physicalSupportCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) (bnd.exceptionalCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap))
      (bnd.properCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) (bnd.punctualCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) p
      (alpha : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p) UR.theory :=
  applicationOfTraceAndLocalData (bnd.exceptionalCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) (bnd.properCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) (bnd.punctualCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap))
    hp ((canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR) alpha m m' n n') (computedUniformRadialRealization baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws bnd UR)
    (sourceLocalFamilyData (P := P) (R := R) (D := D) (DG := DG) (LG := LG)
      (SR := SR) (kl := kl) (as := as) (hkl := hkl) (has := has)
      (dualLocal := dualLocal) (middle := middle) (dualGeneric := dualGeneric) (T := T) (J := J)
      (Z := Z) (M := M) (MR := MR) (FO := FO) (FC := FC)
      (RM := RM) (RI := RI) (BI := BI) (CRG := CRG) (RP := RP)
      (CR := CR) (GC := GC) (DT0 := DT0) (S0 := S0) (GC' := GC')
      (DTG := DTG) (SG := SG) (HC := HC) (BP := BP) (CB := CB)
      (PN := PN) (tensorSource := tensorSource) (O := O) (PC := PC) (ST := ST)
      (degree := degree) (inertia := inertia) (geometric := geometric) (RS := RS) (TA := TA)
      (TR := TR) (baseTheory := baseTheory) (PD := PD) (nativeRadial := nativeRadial) (radialLaws := radialLaws)
      (UR := UR) (traceData := traceData) (IC := IC) (IR := IR) (ZF := ZF)
      (tame := tame) (htame := htame) (ZK := ZK) (ZA := ZA) (point := point)
      (V := V) (Jinf := Jinf) (IRinf := IRinf) (CC := CC) (AS := AS)
      (PR := PR) (AR := AR) (KR := KR) (FR := FR) (FA := FA)
      (SRF := SRF) (hp := hp) (AM := AM) (ICR := ICR) (boundFn := boundFn)
      (sourceCap0 := sourceCap0) (unitCap := unitCap) (ci := ci) (cp := cp) (cm := cm)
      (QB := QB) (QM := QM) (SC := SC) (cl := cl) (cs := cs)
      (QS := QS) (QSM := QSM) (hhyper := hhyper) (hAS := hAS) (bnd := bnd) alpha m m' n n')
    (phaseRules (ZMod p) (AlgebraicClosure (ZMod p)) PD phaseLaws)
    (fuRules (ZMod p) (AlgebraicClosure (ZMod p)) p PD (cubicFourierData CC AS LF FA) (fuGeometry.fuRules p phaseLaws))
    traceData sigma hsigma chebotarev fourierCovariance
    (fun S _ => canonicalFamily_torusIC (originalPullbackData (ZMod p) P) LG SR kl as hkl has
      CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
      SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n' S)
    (fun S _ => canonicalFamily_expectedTrace (originalPullbackData (ZMod p) P) LG SR kl as hkl has
      CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
      SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n' S)
    (canonicalFamily_transformedBounds (originalPullbackData (ZMod p) P) LG SR kl as hkl has
      CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
      SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n')
    alpha.ne_zero m.ne_zero m'.ne_zero n.ne_zero n'.ne_zero

/- No uniform all-prime Application provider is assumed. These two
leaves apply the exact torus endpoint at the chosen prime on the actual
computed canonical (canonicalFamily (originalPullbackData (ZMod p) P) LG SR kl as hkl has
  CR GC O TA TR AM (computedTheory baseTheory
  (phaseData (ZMod p) (AlgebraicClosure (ZMod p)) PD) nativeRadial radialLaws) traceData IC ICR boundFn sourceCap0 unitCap ci cp cm QB QM
  SC cl cs QS QSM hhyper hAS bnd UR). A coherent all-prime standard projection is
still required to BUILD UniformApplications. -/

/-- Distinct rows and columns: the original finite-exceptional estimate. -/
theorem actualCanonicalFiniteFourierBound_on_torus
    (hcutoff : cutoff (bnd.properCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) (bnd.punctualCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) < p)
    (alpha m m' n n' : (ZMod p)ˣ) (hdistinct : m ≠ m' ∧ n ≠ n') :
    FiniteExceptionalFourierBound p
      (uniformStalkConstant (bnd.stalkCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) 1 (bnd.physicalSupportCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)))
      (15 * bnd.exceptionalCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap))
      (alpha : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p) := by
  let app := sourceApplication (P := P) (R := R) (D := D) (DG := DG) (LG := LG)
      (SR := SR) (kl := kl) (as := as) (hkl := hkl) (has := has)
      (dualLocal := dualLocal) (middle := middle) (dualGeneric := dualGeneric) (T := T) (J := J)
      (Z := Z) (M := M) (MR := MR) (FO := FO) (FC := FC)
      (RM := RM) (RI := RI) (BI := BI) (CRG := CRG) (RP := RP)
      (CR := CR) (GC := GC) (DT0 := DT0) (S0 := S0) (GC' := GC')
      (DTG := DTG) (SG := SG) (HC := HC) (BP := BP) (CB := CB)
      (PN := PN) (tensorSource := tensorSource) (O := O) (PC := PC) (ST := ST)
      (degree := degree) (inertia := inertia) (geometric := geometric) (RS := RS) (TA := TA)
      (TR := TR) (baseTheory := baseTheory) (PD := PD) (nativeRadial := nativeRadial) (radialLaws := radialLaws)
      (UR := UR) (traceData := traceData) (IC := IC) (IR := IR) (ZF := ZF)
      (tame := tame) (htame := htame) (ZK := ZK) (ZA := ZA) (point := point)
      (V := V) (Jinf := Jinf) (IRinf := IRinf) (CC := CC) (AS := AS)
      (PR := PR) (AR := AR) (KR := KR) (FR := FR) (FA := FA)
      (SRF := SRF) (hp := hp) (AM := AM) (ICR := ICR) (boundFn := boundFn)
      (sourceCap0 := sourceCap0) (unitCap := unitCap) (ci := ci) (cp := cp) (cm := cm)
      (QB := QB) (QM := QM) (SC := SC) (cl := cl) (cs := cs)
      (QS := QS) (QSM := QSM) (hhyper := hhyper) (hAS := hAS) (bnd := bnd)
      (phaseLaws := phaseLaws) (fuGeometry := fuGeometry) (sigma := sigma) (hsigma := hsigma) (chebotarev := chebotarev)
      (fourierCovariance := fourierCovariance) alpha m m' n n'
  apply app.finiteFourierBound_on_torus hcutoff alpha.ne_zero m.ne_zero
    m'.ne_zero n.ne_zero n'.ne_zero
  exact ⟨fun h => hdistinct.1 (Units.ext h), fun h => hdistinct.2 (Units.ext h)⟩

/-- The repeated-index branch retains the exact curve estimate; this
weaker bound also holds in the distinct case. -/
theorem actualCanonicalCurveFourierBound_on_torus
    (hcutoff : cutoff (bnd.properCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) (bnd.punctualCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) < p)
    (alpha m m' n n' : (ZMod p)ˣ) :
    CurveExceptionalFourierBound p
      (uniformStalkConstant (bnd.stalkCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)) 1 (bnd.physicalSupportCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap)))
      (15 * bnd.exceptionalCap (physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap))
      (alpha : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p) := by
  let app := sourceApplication (P := P) (R := R) (D := D) (DG := DG) (LG := LG)
      (SR := SR) (kl := kl) (as := as) (hkl := hkl) (has := has)
      (dualLocal := dualLocal) (middle := middle) (dualGeneric := dualGeneric) (T := T) (J := J)
      (Z := Z) (M := M) (MR := MR) (FO := FO) (FC := FC)
      (RM := RM) (RI := RI) (BI := BI) (CRG := CRG) (RP := RP)
      (CR := CR) (GC := GC) (DT0 := DT0) (S0 := S0) (GC' := GC')
      (DTG := DTG) (SG := SG) (HC := HC) (BP := BP) (CB := CB)
      (PN := PN) (tensorSource := tensorSource) (O := O) (PC := PC) (ST := ST)
      (degree := degree) (inertia := inertia) (geometric := geometric) (RS := RS) (TA := TA)
      (TR := TR) (baseTheory := baseTheory) (PD := PD) (nativeRadial := nativeRadial) (radialLaws := radialLaws)
      (UR := UR) (traceData := traceData) (IC := IC) (IR := IR) (ZF := ZF)
      (tame := tame) (htame := htame) (ZK := ZK) (ZA := ZA) (point := point)
      (V := V) (Jinf := Jinf) (IRinf := IRinf) (CC := CC) (AS := AS)
      (PR := PR) (AR := AR) (KR := KR) (FR := FR) (FA := FA)
      (SRF := SRF) (hp := hp) (AM := AM) (ICR := ICR) (boundFn := boundFn)
      (sourceCap0 := sourceCap0) (unitCap := unitCap) (ci := ci) (cp := cp) (cm := cm)
      (QB := QB) (QM := QM) (SC := SC) (cl := cl) (cs := cs)
      (QS := QS) (QSM := QSM) (hhyper := hhyper) (hAS := hAS) (bnd := bnd)
      (phaseLaws := phaseLaws) (fuGeometry := fuGeometry) (sigma := sigma) (hsigma := hsigma) (chebotarev := chebotarev)
      (fourierCovariance := fourierCovariance) alpha m m' n n'
  exact app.curveFourierBound_on_torus hcutoff

end PrimeGap182.TypeIII.CoherentStandardDirectEndpointApplicationDraft04

#print axioms PrimeGap182.TypeIII.CoherentStandardDirectEndpointApplicationDraft04.sourceLocalFamilyData
#print axioms PrimeGap182.TypeIII.CoherentStandardDirectEndpointApplicationDraft04.sourceApplication

#print axioms PrimeGap182.TypeIII.CoherentStandardDirectEndpointApplicationDraft04.actualCanonicalFiniteFourierBound_on_torus
#print axioms PrimeGap182.TypeIII.CoherentStandardDirectEndpointApplicationDraft04.actualCanonicalCurveFourierBound_on_torus
