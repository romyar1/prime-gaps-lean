import TypeIIICanonicalSourceFourierStalk
import TypeIIIRegularUnipotentRepresentation
import TypeIIIConstantFieldLocalData

/-!
# Local data for the same canonical Fourier core, over the geometric constants

The three source specializations are proved, and zero-inertia functoriality
transports their individual Kl3/AS source models. Nonzero tame monodromy
constructs the regular model. Rank six and the existing finite-origin
construction then give CoreLocalData. Constant-field transport retains
that exact representation and all finite-origin maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CanonicalSourceLocalData

open PublishedPhysicalConstruction CanonicalCurveInput CanonicalLocalCorrelation
open GenericSourceSpecialization FourierSourceMaps FourierSourcePullbacks PulledCurveInput
open FourierStalkFromSources FourierStalkInertia PublishedPhaseApplication PublishedLocalConstruction
open CanonicalFourierKernel BoundaryFromSourceModels MiddleFromLocalization
open CanonicalSourceFourierStalk TensorListRepresentation RegularUnipotentRepresentation
open GeometricCoreRank ConstantFieldLocalData PublishedMackey

universe u v w z a b c d e f g h i j k l o t r
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


/-- A functorial realization of the existing zero-inertia objects. -/
structure ZeroFunctor where
  functor : GenericInput ⥤ FDRep ℂ G0
  comparison : ∀ A, Representation.Equiv (Z.zero A).ρ (functor.obj A).ρ

variable (ZF : ZeroFunctor DG Z)

variable {DG Z} in
def ZeroFunctor.mapEquiv {A B : GenericInput} (e : A ≅ B) :
    Representation.Equiv (Z.zero A).ρ (Z.zero B).ρ :=
  (ZF.comparison A).trans ((equivOfIso (ZF.functor.mapIso e)).trans (ZF.comparison B).symm)

variable (tame : G0 →* Multiplicative ℂ) (htame : ∃ g, (tame g).toAdd ≠ 0)
  (ZK : ∀ lambda : (PhaseField K)ˣ,
    Representation.Equiv
      (Z.zero ((localSpecialization K P R).obj
        (((localSheafOperations K P R dualLocal middle).scalar lambda).obj (localSource K P R kl)))).ρ
      (tameRepresentation tame))
  (ZA : ∀ s : (PhaseField K)ˣ,
    Representation.Equiv (Z.zero (additiveSource K P as s)).ρ (Representation.trivial ℂ G0 ℂ))
  (CRG : CurveRules DG) (alpha m n : Kˣ)
  (RP : PullbackProperties D DG (P.along (specializationMorphism K alpha m n)))

/-- Zero inertia of the literal first pulled source, using the unit
scalar map of the same Kl3 source. -/
def pulledFirstZeroEquiv :
    Representation.Equiv
      (Z.zero (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP).first).ρ
      (tameRepresentation tame) :=
  (ZF.mapEquiv (firstSourceIso K P R alpha m n kl)).trans
    ((ZF.mapEquiv ((localSpecialization K P R).mapIso
      (((localSheafOperations K P R dualLocal middle).scalar_one.app (localSource K P R kl)).symm))).trans
        (ZK 1))

/-- Zero inertia of the literal second pulled source. -/
def pulledSecondZeroEquiv :
    Representation.Equiv
      (Z.zero (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP).second).ρ
      (tameRepresentation tame) :=
  (ZF.mapEquiv (secondSourceIso K P R alpha m n kl)).trans (ZK (lambdaUnit K m n))

/-- The actual normalized additive source is unramified at zero. -/
def pulledAdditiveZeroEquiv :
    Representation.Equiv
      (Z.zero (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP).additive).ρ
      (Representation.trivial ℂ G0 ℂ) :=
  (ZF.mapEquiv (additiveSourceIso K P alpha m n as)).trans (ZA (scaleUnit K alpha m))

variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (point : GenericPoint) (V : GeometricFiberRules DG H F point)
  (Jinf : L ⥤ FDRep ℂ I) [Jinf.Monoidal]
  (IR : InfinityCompatibility (localSheafOperations K P R dualLocal middle) Jinf FO)
  (p : ℕ) [Fact p.Prime] [CharP K p]
  {Cover : Type r} [Group Cover]
  (CC : CubicCoverData (PhaseField K) ℂ I Cover)
  (AS : LinearASData (PhaseField K) ℂ Cover)
  (PR : CubicCoverRules CC) (AR : LinearASRules CC AS)
  (KR : KloostermanInfinityRules p CC AS
    (sourceInfinity (localSheafOperations K P R dualLocal middle) Jinf (localSource K P R kl)))
  (FR : LocalFourierAdditivity LF) (FA : CubicInputAdmissibility CC AS LF)
  (SRF : FiniteOriginRules p FO) (hp : 3 < p)

/-- Construct local data for the exact canonical core. No source
specialization, finished rank, regular-model record, or correlation
infinity identification is a premise. -/
def canonicalSourceCoreLocalData :
    CoreLocalData (cubicFourierData CC AS LF FA) (alpha : K) (m : K) (n : K)
      (FO.origin (radialScale (alpha : K) (m : K))
        (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero)
        (perverseCorrelation (localSheafOperations K P R dualLocal middle)
          (localSource K P R kl) (angularUnit (m : K) (n : K) m.ne_zero n.ne_zero))) :=
  canonicalCoreLocalDataFromSources Z M MR (localSheafOperations K P R dualLocal middle)
    (localSpecialization K P R) dualGeneric T FO
    (canonicalFourierBaseChange K P R DG as dualLocal middle Z M FO FC)
    (canonicalPulledInput K P D DG LG SR kl as hkl has alpha m n RP) CRG
    (localSource K P R kl) Jinf IR p CC AS PR AR KR FR FA SRF hp
    (alpha : K) (m : K) (n : K) alpha.ne_zero m.ne_zero n.ne_zero
    (firstSourceIso K P R alpha m n kl)
    (secondSourceIso K P R alpha m n kl ≪≫
      eqToIso (congrArg (fun lambda => (localSpecialization K P R).obj
        ((R.localEnd (FourierSourceMaps.scalarMorphism K lambda)).obj (localSource K P R kl)))
        (lambdaUnit_eq_angularUnit K m n)))
    (additiveSourceIso K P alpha m n as ≪≫
      eqToIso (congrArg (additiveSource K P as) (scaleUnit_eq_radialScale K alpha m)))
    (tameRegularModel tame htame)
    (pulledFirstZeroEquiv K P R D DG LG SR kl as hkl has dualLocal middle Z ZF tame ZK alpha m n RP)
    (pulledSecondZeroEquiv K P R D DG LG SR kl as hkl has dualLocal middle Z ZF tame ZK alpha m n RP)
    (pulledAdditiveZeroEquiv K P D DG LG SR kl as hkl has Z ZF ZA alpha m n RP) point V


/-- Match the final bridge's geometric constant field while retaining
exactly the same canonical Fourier representation and finite-origin maps.
All family input specializations and the rank have been derived above. -/
def canonicalSourceCoreLocalData_overClosure :
    CoreLocalData (cubicData K (AlgebraicClosure K) (cubicFourierData CC AS LF FA))
      (algebraMap K (AlgebraicClosure K) (alpha : K))
      (algebraMap K (AlgebraicClosure K) (m : K))
      (algebraMap K (AlgebraicClosure K) (n : K))
      (FO.origin (radialScale (alpha : K) (m : K))
        (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero)
        (perverseCorrelation (localSheafOperations K P R dualLocal middle)
          (localSource K P R kl) (angularUnit (m : K) (n : K) m.ne_zero n.ne_zero))) :=
  algebraicClosureCoreLocalData K (cubicFourierData CC AS LF FA) (alpha : K) (m : K) (n : K) _
    (canonicalSourceCoreLocalData K P R D DG LG SR kl as hkl has dualLocal middle dualGeneric T
      Z M MR FO FC ZF tame htame ZK ZA CRG alpha m n RP point V Jinf IR p CC AS PR AR KR FR FA SRF hp)

end PrimeGap182.TypeIII.CanonicalSourceLocalData

#print axioms PrimeGap182.TypeIII.CanonicalSourceLocalData.ZeroFunctor.mapEquiv
#print axioms PrimeGap182.TypeIII.CanonicalSourceLocalData.pulledFirstZeroEquiv
#print axioms PrimeGap182.TypeIII.CanonicalSourceLocalData.pulledSecondZeroEquiv
#print axioms PrimeGap182.TypeIII.CanonicalSourceLocalData.pulledAdditiveZeroEquiv
#print axioms PrimeGap182.TypeIII.CanonicalSourceLocalData.canonicalSourceCoreLocalData

#print axioms PrimeGap182.TypeIII.CanonicalSourceLocalData.canonicalSourceCoreLocalData_overClosure
