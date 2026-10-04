import TypeIIIMiddleFromLocalization
import TypeIIICanonicalLocalCorrelation

/-!
# Fourier-stalk comparison from the source recipe

Tensor/dual specialization identifies the literal input with the kernel
in general compact Fourier base change. The localization comparison then
identifies its parabolic image with the Fourier stalk. Rank six is derived
from the individual zero-inertia models and GOS; it is not an input.

The general geometric operations, compact Fourier base change, and the
three individual source specializations remain explicit realization data.
In particular, no isomorphism for the finished correlation is assumed.
Compact Fourier base change is Laumon's definition in section 1.2,
https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf,
with the projection formula for the lisse Artin--Schreier kernel.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.FourierStalkFromSources

open PublishedPhysicalConstruction BoundaryFromSourceModels MiddleFromLocalization
open RegularUnipotentBoundary GeometricCoreRank PublishedPhaseApplication
open PublishedMackey PublishedLocalConstruction CanonicalLocalCorrelation

universe u v w z a b c d e f g i j
variable {K : Type u} [Field K]
  {Input : Type v} [Category.{c} Input] [MonoidalCategory Input]
  {Point : Type z} {C : Type w} [Category.{d} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat.{w} ℂ} {BS : BoundarySequence D H F}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F BS)
  (M : CompactificationData Z) (MR : CompactificationRules Z M)
  {L : Type e} [Category.{f} L] [MonoidalCategory L]
  {Q : Type g} [Category.{i} Q]
  (O : SheafOperations (PhaseField K) L Q)
  (J : L ⥤ Input) [J.Monoidal] (dualInput : Inputᵒᵖ ⥤ Input)

/-- General compatibility between the curve recipe operations, actual
tensor/dual functors, and specialization. No selected source occurs. -/
structure SpecializationCompatibility where
  tensor : ∀ A B, D.tensor A B ≅ A ⊗ B
  dual : ∀ A, D.dual A ≅ dualInput.obj (op A)
  dualSpecialization : ∀ A, dualInput.obj (op (J.obj A)) ≅ J.obj (O.dual A)

variable (T : SpecializationCompatibility (D := D) O J dualInput)

/-- Transport actual source isomorphisms through the curve tensor. -/
def inputTensorIso {A B A' B' : Input} (hA : A ≅ A') (hB : B ≅ B') :
    D.tensor A B ≅ D.tensor A' B' :=
  T.tensor A B ≪≫ tensorIso hA hB ≪≫ (T.tensor A' B').symm

/-- Transport a source isomorphism through the same contravariant dual. -/
def inputDualIso {A B : Input} (h : A ≅ B) : D.dual A ≅ D.dual B :=
  T.dual A ≪≫ dualInput.mapIso h.op.symm ≪≫ (T.dual B).symm

/-- Restriction of the canonical correlation is derived by tensor/dual
compatibility of specialization, not supplied as a family isomorphism. -/
def specializedCorrelationIso (kl : L) (lambda : (PhaseField K)ˣ) :
    D.tensor (J.obj kl) (D.dual (J.obj ((O.scalar lambda).obj kl))) ≅
      J.obj (CanonicalLocalCorrelation.correlation O kl lambda) :=
  T.tensor _ _ ≪≫
    tensorIso (Iso.refl _) (T.dual _ ≪≫ T.dualSpecialization _) ≪≫
      Functor.Monoidal.μIso J kl (O.dual ((O.scalar lambda).obj kl))

variable {I : Type j} [Group I] {G : Type c} [Group G]
  {LF : LocalFourierData K ℂ I G} (FO : FiniteOriginData Q LF)

/-- General compact Fourier base change for arbitrary lisse objects.
`additive a ha` is the lisse kernel AS((T²/a)x), on the same specialized
curve as `J`. The right side is affine middle cohomology of its tensor
with the source. The middle-extension projection formula is included in
this general compatibility law, not in a family-specific assertion. -/
structure FourierBaseChange where
  additive : (a : PhaseField K) → a ≠ 0 → Input
  comparison : ∀ (a : PhaseField K) (ha : a ≠ 0) A,
    (FO.origin a ha (O.middleExtension.obj A)).V ≃ₗ[ℂ]
      M.affine.obj (D.tensor (J.obj A) (additive a ha))

variable (BC : FourierBaseChange Z M O J FO)
  (A : KloostermanInputData D) (CR : CurveRules D)
  (kl : L) (lambda : (PhaseField K)ˣ) (s : PhaseField K) (hs : s ≠ 0)
  (hfirst : A.first ≅ J.obj kl)
  (hsecond : A.second ≅ J.obj ((O.scalar lambda).obj kl))
  (hadditive : A.additive ≅ BC.additive s hs)

/-- The entire original input is the general Fourier kernel recipe,
derived solely from the three individual source specializations. -/
def inputKernelIso : A.input ≅
    D.tensor (J.obj (CanonicalLocalCorrelation.correlation O kl lambda)) (BC.additive s hs) :=
  inputTensorIso O J dualInput T
    (inputTensorIso O J dualInput T hfirst (inputDualIso O J dualInput T hsecond) ≪≫
      specializedCorrelationIso O J dualInput T kl lambda) hadditive

variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Identify the actual original parabolic image with the canonical
Fourier stalk, using localization and general compact base change. -/
def coreStalkFourierEquiv :
    F.obj (parabolicCore H A.input) ≃ₗ[ℂ]
      (FO.origin s hs (perverseCorrelation O kl lambda)).V :=
  ((coreStalkAffineIso Z M MR A.input (A.input_lisse CR) (A.input_slope_one CR)).toLinearEquiv.trans
    (M.affine.mapIso (inputKernelIso Z M O J dualInput T FO BC A kl lambda s hs
      hfirst hsecond hadditive)).toLinearEquiv).trans
    (BC.comparison s hs (CanonicalLocalCorrelation.correlation O kl lambda)).symm

include MR CR T hfirst hsecond hadditive in
/-- The generic Fourier rank follows from GOS and the individual
regular-unipotent zero-inertia models. No Fourier-rank premise remains. -/
theorem fourier_rank_six {rho : Representation ℂ G0 (Fin 3 → ℂ)} (U : RegularModel rho)
    (hzfirst : Representation.Equiv (Z.zero A.first).ρ rho)
    (hzsecond : Representation.Equiv (Z.zero A.second).ρ rho)
    (hzadditive : Representation.Equiv (Z.zero A.additive).ρ (Representation.trivial ℂ G0 ℂ))
    (point : Point) (V : GeometricFiberRules D H F point) :
    Module.finrank ℂ (FO.origin s hs (perverseCorrelation O kl lambda)).V = 6 := by
  rw [← (coreStalkFourierEquiv Z M MR O J dualInput T FO BC A CR kl lambda s hs
    hfirst hsecond hadditive).finrank_eq]
  exact core_rank_six_from_sources Z A CR U hzfirst hzsecond hzadditive point V

/-- Feed the derived rank into the existing finite-origin construction
for the canonical perverse correlation. The supplied objects and
comparisons concern the individual sources and general functors only;
there is no rank or completed-correlation identification premise. -/
def canonicalCoreLocalDataFromSources
    (Jinf : L ⥤ FDRep ℂ I) [Jinf.Monoidal] (IR : InfinityCompatibility O Jinf FO)
    (p : ℕ) [Fact p.Prime] [CharP K p] {Cover : Type*} [Group Cover]
    (P : CubicCoverData (PhaseField K) ℂ I Cover)
    (AS : LinearASData (PhaseField K) ℂ Cover)
    (PR : CubicCoverRules P) (AR : LinearASRules P AS)
    (KR : KloostermanInfinityRules p P AS (sourceInfinity O Jinf kl))
    (FR : LocalFourierAdditivity LF) (FA : CubicInputAdmissibility P AS LF)
    (SR : FiniteOriginRules p FO) (hp : 3 < p)
    (alpha m n : K) (ha : alpha ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hsrcFirst : A.first ≅ J.obj kl)
    (hsrcSecond : A.second ≅ J.obj ((O.scalar (angularUnit m n hm hn)).obj kl))
    (hsrcAdditive : A.additive ≅
      BC.additive (radialScale alpha m) (radialScale_ne_zero alpha m ha hm))
    {rho : Representation ℂ G0 (Fin 3 → ℂ)} (U : RegularModel rho)
    (hzFirst : Representation.Equiv (Z.zero A.first).ρ rho)
    (hzSecond : Representation.Equiv (Z.zero A.second).ρ rho)
    (hzAdditive : Representation.Equiv (Z.zero A.additive).ρ (Representation.trivial ℂ G0 ℂ))
    (point : Point) (V : GeometricFiberRules D H F point) :
    CoreLocalData (cubicFourierData P AS LF FA) alpha m n
      (FO.origin (radialScale alpha m) (radialScale_ne_zero alpha m ha hm)
        (perverseCorrelation O kl (angularUnit m n hm hn))) :=
  canonicalCoreLocalData O Jinf FO IR p P AS PR AR kl KR FR FA SR hp alpha m n ha hm hn
    (fourier_rank_six Z M MR O J dualInput T FO BC A CR kl (angularUnit m n hm hn)
      (radialScale alpha m) (radialScale_ne_zero alpha m ha hm)
      hsrcFirst hsrcSecond hsrcAdditive U hzFirst hzSecond hzAdditive point V)

end PrimeGap182.TypeIII.FourierStalkFromSources

#print axioms PrimeGap182.TypeIII.FourierStalkFromSources.inputTensorIso
#print axioms PrimeGap182.TypeIII.FourierStalkFromSources.inputDualIso
#print axioms PrimeGap182.TypeIII.FourierStalkFromSources.specializedCorrelationIso
#print axioms PrimeGap182.TypeIII.FourierStalkFromSources.inputKernelIso
#print axioms PrimeGap182.TypeIII.FourierStalkFromSources.coreStalkFourierEquiv
#print axioms PrimeGap182.TypeIII.FourierStalkFromSources.fourier_rank_six
#print axioms PrimeGap182.TypeIII.FourierStalkFromSources.canonicalCoreLocalDataFromSources
