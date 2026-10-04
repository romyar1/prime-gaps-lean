import TypeIIINativeSurfaceFromIntrinsicSimplicity
import TypeIIIRankTwoFourierFromNativeASKernel
import TypeIIINativeLocalRulesFromRadialIsomorphisms
import TypeIIILinearFourierRationalImage
import TypeIIIPhaseRulesFromSeparatedCharacters

/-!
# Punctual inverse Fourier phases from general lisse wild stalks

Point compact pushforward is indexed by ALL actual point-to-plane maps.
A general closed-point essential-image theorem and the general full-AS
punctual Fourier formula give a shifted ordinary constant-coefficient AS
sheaf. Reflection and Tate(+2) use the SAME full rank-two transform.
Exact inverse image and native ordinary H^-2 then recover its ordinary
radial pullback. General lisse inverse-image/unramified wild-stalk and
generic-rank laws are universal before choosing any punctual object.
The resulting trivial positive-rank representation has a nonzero Hom
from the SAME original coefficient-zero character by checked character
linear algebra; no inverse-point/zero-phase law is a premise.

The actual native perverse/continuous constructible Q2-adic realization,
p!=2, ordinary tensor/Tate/coefficient-fiber interpretation, point-heart
realization and lisse/wild realization remain explicit. The punctual
Fourier formula is the general proper-base-change/projection-formula
corollary of Laumon1.2.1.1 (also1.2.3.1 at rank0 +1.2.3.2 translation),
not a falsely quoted standalone numbered arbitrary-point formula.
No full compatible residual Inputs or adic foundations are constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped Classical PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.NativePunctualFourierFromLisseWildStalks
open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages NativeSurfaceFromGeometricStalks
open LinearRadialPhaseFromPoleTransport PublishedPhaseApplication
open PhaseDataFromOriginalCharacters

variable (k : Type) [Field k]

/-- The actual affine-plane structure map to its geometric coefficient point. -/
def planeStructure : FullFourierKernelCoordinates.planeScheme k ⟶ pointScheme k :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k))

/-- The origin zero section, over the SAME phase field. -/
def originZero : Spec (.of (L k)) ⟶ originScheme k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : L k)))

/-- Actual phase-field coefficient extension at the geometric coefficient point. -/
def originBasePoint : Spec (.of (L k)) ⟶ pointScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (L k)))

theorem point_isClosedImmersion (z : k × k) : IsClosedImmersion (pointMorphism k z) :=
  IsClosedImmersion.spec_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp [pointHom]⟩)

/-- Reflection preserves the original full-plane geometric origin. -/
theorem point_zero_reflection : pointMorphism k (0, 0) ≫
    RankTwoFourierKernelCoordinates.reflectionMorphism k = pointMorphism k (0, 0) := by
  rw [LinearFourierRationalImage.native_planePoint]
  have hv : ![(0 : k), 0] = (fun _ : Fin 2 => (0 : k)) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact RankTwoFourierKernelCoordinates.plane_origin_reflection k

/-- The radial map is defined at pi=0 and sends it to the full-plane origin. -/
theorem originZero_radial : originZero k ≫ radialMorphism (k := k) =
    originBasePoint k ≫ pointMorphism k (0, 0) := by
  dsimp only [originZero, radialMorphism, originBasePoint, pointMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun h => Spec.map (CommRingCat.ofHom h))
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [radialHom, pointHom]
  · intro i
    fin_cases i <;> simp [radialHom, pointHom]

/-- The inverse reflection sign is explicit; the radial AS phase is a
POLYNOMIAL, regular at pi=0, including zero coefficients. -/
theorem inverse_radial_phase_X (a b : k) :
    ((radialHom (k := k)).comp
      ((RankTwoFourierKernelCoordinates.reflectionHom k).comp (linearHom a b)))
      (MvPolynomial.X 0) =
    -Polynomial.C (algebraMap k (L k) a + algebraMap k (L k) b * direction k) *
      Polynomial.X ^ 2 := by
  simp [linearHom, radialHom, RankTwoFourierKernelCoordinates.reflectionHom]
  ring

universe mu g
variable {p : ℕ} [Fact p.Prime] {J : Type}
  {B : SourceInverseImageSystem.System.{0,mu} (ZMod p)}
  {otherScheme : J → Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index → Type}
  [∀ i, Category.{mu} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{mu} LC] [Abelian LC]
  {OC : J → Type} [∀ i, Category.{mu} (OC i)] [∀ i, Abelian (OC i)]
  {A : OrdinarySystem (extensionScheme (K := ZMod p) (extraScheme (AlgebraicClosure (ZMod p)) otherScheme))
    (extensionObjects B (extraObjects NC LC OC))}

local instance commonLocalizations : ∀ i, HasDerivedCategory.{mu}
    (extensionObjects B (extraObjects NC LC OC) i) :=
  fun i => HasDerivedCategory.standard (extensionObjects B (extraObjects NC LC OC) i)
local instance nativeLocalizations : ∀ i, HasDerivedCategory.{mu} (NC i) :=
  fun i => HasDerivedCategory.standard (NC i)

variable (point : J) (hPoint : otherScheme point = pointScheme (AlgebraicClosure (ZMod p)))
  [MonoidalCategory (NC .plane)]

local instance pointLocalization : HasDerivedCategory.{mu} (OC point) :=
  HasDerivedCategory.standard (OC point)

def indexedPlaneStructure :
    extensionScheme (K := ZMod p) (extraScheme (AlgebraicClosure (ZMod p)) otherScheme) (nativeIndex .plane) ⟶
    extensionScheme (K := ZMod p) (extraScheme (AlgebraicClosure (ZMod p)) otherScheme) (pointIndex point) :=
  planeStructure (AlgebraicClosure (ZMod p)) ≫ eqToHom hPoint.symm

/-- General point compact-push and ordinary Tate framework on fixed categories. -/
structure Data where
  pointPush : ∀ (_f :
    extensionScheme (K := ZMod p) (extraScheme (AlgebraicClosure (ZMod p)) otherScheme) (pointIndex point) ⟶
    extensionScheme (K := ZMod p) (extraScheme (AlgebraicClosure (ZMod p)) otherScheme) (nativeIndex .plane)),
    A.Derived (pointIndex point) ⥤ (nativeSystem A).Derived .plane
  [pointPushZero : ∀ f, (pointPush f).PreservesZeroMorphisms]
  tateOrdinary : ℤ → NC .plane ⥤ NC .plane

attribute [instance] Data.pointPushZero

variable (P : Data (A := A) point)
  (AS : AddChar (ZMod p) (PadicAlgCl 2) → B.Obj .line)

def ordinaryPlaneAS (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))
    (ψ : AddChar (ZMod p) (PadicAlgCl 2)) : NC .plane :=
  (A.pull (i := nativeIndex .plane) (j := sourceIndex)
    (linearMorphism z.1 z.2 ≫ baseLineMorphism (ZMod p) (AlgebraicClosure (ZMod p)))).obj (AS ψ)

def planeCoefficientPull : OC point ⥤ NC .plane :=
  A.pull (i := nativeIndex .plane) (j := pointIndex point) (indexedPlaneStructure point hPoint)

/-- Actual coefficient inverse image tensor SAME original AS(dot z). -/
def ordinaryPointFourier (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))
    (ψ : AddChar (ZMod p) (PadicAlgCl 2)) : OC point ⥤ NC .plane :=
  planeCoefficientPull (A := A) point hPoint ⋙
    tensorRight (ordinaryPlaneAS (A := A) AS z ψ)

def ordinaryReflection : NC .plane ⥤ NC .plane :=
  (nativeSystem A).pull (i := .plane) (j := .plane)
    (RankTwoFourierKernelCoordinates.reflectionMorphism (AlgebraicClosure (ZMod p)))

/-- Reflection then Tate(+2), with no rank-one/rank-two twist discrepancy lost. -/
def ordinaryPointInverse (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))
    (ψ : AddChar (ZMod p) (PadicAlgCl 2)) : OC point ⥤ NC .plane :=
  ordinaryPointFourier (A := A) point hPoint AS z ψ ⋙ ordinaryReflection (A := A) ⋙
    P.tateOrdinary (2 : ℤ)

variable (fiber : OC point ⥤ ModuleCat.{mu} ℂ)

def planeFiberZero : NC .plane ⥤ ModuleCat.{mu} ℂ :=
  A.pull (i := pointIndex point) (j := nativeIndex .plane)
    (indexedPointMorphism (K0 := ZMod p) point hPoint (0, 0)) ⋙ fiber

omit [MonoidalCategory (NC .plane)] in
/-- Actual composition and reflection-at-zero derive fiber-rank preservation. -/
theorem reflection_fiber_rank (F : NC .plane) :
    Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj
      ((ordinaryReflection (A := A)).obj F)) =
    Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj F) := by
  have hf : indexedPointMorphism (K0 := ZMod p) point hPoint (0, 0) ≫
      RankTwoFourierKernelCoordinates.reflectionMorphism (AlgebraicClosure (ZMod p)) =
      indexedPointMorphism (K0 := ZMod p) point hPoint (0, 0) := by
    simp only [indexedPointMorphism, Category.assoc, point_zero_reflection]
  exact (fiber.mapIso
    ((A.composition (i := pointIndex point) (j := nativeIndex .plane) (k := nativeIndex .plane)
      (indexedPointMorphism (K0 := ZMod p) point hPoint (0, 0))
      (RankTwoFourierKernelCoordinates.reflectionMorphism (AlgebraicClosure (ZMod p)))).app F ≪≫
      (eqToIso (congrArg (fun f => A.pull (i := pointIndex point) (j := nativeIndex .plane) f) hf)).app F)).toLinearEquiv.finrank_eq

variable (kernel : J)
  (hKernel : otherScheme kernel = RankTwoFourierKernelCoordinates.kernelScheme (AlgebraicClosure (ZMod p)))
  [MonoidalCategory (RankTwoFourierFromNativeASKernel.KernelDerived (A := A) kernel)]
  (F2 : RankTwoFourierFromNativeASKernel.Data (A := A) kernel)
  [∀ n, (F2.tate n).CommShift ℤ]
  (D : Admissibility A) (hp2 : p ≠ 2)
  (Lisse : NC .plane → Prop)
  {G : Type g} [Group G] (W : OrdinaryWild (E := ℂ) (G := G) A)

/-- Published/general laws on EVERY coefficient, point, ordinary lisse
object and regular origin morphism. No Fourier zero-phase conclusion. -/
structure PublishedLaws (D : Admissibility A) (_hp2 : p ≠ 2)
    (Lisse : NC .plane → Prop) (W : OrdinaryWild (E := ℂ) (G := G) A) where
  pointEssentialImage : ∀ z, IsClosedImmersion (pointMorphism (AlgebraicClosure (ZMod p)) z) →
    ∀ Q : Obj D,
    {x | ∃ n : ℤ, Nontrivial (pointCohomology D point hPoint fiber Q x n)} ⊆ {z} →
    ∃ C : OC point, Nonempty (Q.obj ≅ (P.pointPush (indexedPointMorphism (K0 := ZMod p) point hPoint z)).obj
      ((A.degreeZero (pointIndex point)).obj C))
  pointFourier : ∀ ψ, ψ ≠ 1 → ∀ z,
    A.degreeZero (pointIndex point) ⋙ P.pointPush (indexedPointMorphism (K0 := ZMod p) point hPoint z) ⋙
      F2.derivedTransform kernel hKernel AS ψ ≅
    ordinaryPointFourier (A := A) point hPoint AS z ψ ⋙ (nativeSystem A).degreeZero .plane ⋙
      shiftFunctor ((nativeSystem A).Derived .plane) (2 : ℤ)
  tateDegreeZero : ∀ n, (nativeSystem A).degreeZero .plane ⋙ F2.tate n ≅
    P.tateOrdinary n ⋙ (nativeSystem A).degreeZero .plane
  coefficientFinite : ∀ C, FiniteDimensional ℂ (fiber.obj C)
  lissePointAS : ∀ ψ, ψ ≠ 1 → ∀ z C,
    Lisse ((ordinaryPointFourier (A := A) point hPoint AS z ψ).obj C)
  rankPointAS : ∀ ψ, ψ ≠ 1 → ∀ z C,
    Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj
      ((ordinaryPointFourier (A := A) point hPoint AS z ψ).obj C)) = Module.finrank ℂ (fiber.obj C)
  lisseIso : ∀ e : FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)) ≅ FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)),
    ∀ F, Lisse F → Lisse (((nativeSystem A).pull (i := .plane) (j := .plane) e.hom).obj F)
  lisseTate : ∀ n F, Lisse F → Lisse ((P.tateOrdinary n).obj F)
  rankTate : ∀ n F, Lisse F → Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj
    ((P.tateOrdinary n).obj F)) = Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj F)
  wildLisseTrivial : ∀ (f : originScheme (AlgebraicClosure (ZMod p)) ⟶
    FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p))) F, Lisse F → Representation.IsTrivial
      (W.originWild.obj (((nativeSystem A).pull (i := .origin) (j := .plane) f).obj F)).ρ
  wildLisseRank : ∀ (f : originScheme (AlgebraicClosure (ZMod p)) ⟶
    FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p))) F, Lisse F →
    originZero (AlgebraicClosure (ZMod p)) ≫ f = originBasePoint (AlgebraicClosure (ZMod p)) ≫
      pointMorphism (AlgebraicClosure (ZMod p)) (0, 0) →
    Module.finrank ℂ (W.originWild.obj (((nativeSystem A).pull (i := .origin) (j := .plane) f).obj F)) =
      Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj F)

variable {P point hPoint AS fiber kernel hKernel F2 D hp2 Lisse W}
  (H : PublishedLaws point hPoint P AS fiber kernel hKernel F2 D hp2 Lisse W)

/-- The computed full inverse of a punctual coefficient object, with
actual reflection/shift and general degree-zero Tate compatibility. -/
def inversePointComparison (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1)
    (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p)) (C : OC point) :
    (F2.derivedInverse kernel hKernel AS ψ).obj
      ((P.pointPush (indexedPointMorphism (K0 := ZMod p) point hPoint z)).obj ((A.degreeZero (pointIndex point)).obj C)) ≅
    (shiftFunctor ((nativeSystem A).Derived .plane) (2 : ℤ)).obj
      (((nativeSystem A).degreeZero .plane).obj
        ((ordinaryPointInverse point hPoint P AS z ψ).obj C)) :=
  (F2.tate (2 : ℤ)).mapIso
    ((RankTwoFourierFromNativeASKernel.reflectionPull (A := A)).mapIso ((H.pointFourier ψ hψ z).app C) ≪≫
      (((nativeSystem A).pull (i := .plane) (j := .plane)
        (RankTwoFourierKernelCoordinates.reflectionMorphism (AlgebraicClosure (ZMod p)))).mapDerivedCategory.commShiftIso (2 : ℤ)).app _) ≪≫
    ((F2.tate (2 : ℤ)).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor ((nativeSystem A).Derived .plane) (2 : ℤ)).mapIso
      ((F2.tate (2 : ℤ)).mapIso
        (((nativeSystem A).degreeZeroPullback (i := .plane) (j := .plane)
          (RankTwoFourierKernelCoordinates.reflectionMorphism (AlgebraicClosure (ZMod p)))).app _) ≪≫
        (H.tateDegreeZero (2 : ℤ)).app _)

variable (D W)

/-- Native exact pullback and H^-2(degree0(F)[2])=F, proved from the
existing exact lift and standard single/shift/homology isomorphisms. -/
def ordinaryRadialComparison (F : NC .plane) :
    ((nativeSystem A).ordinary .origin (-2) ⋙ W.originWild).obj
      (((nativeSystem A).derivedPull (i := .origin) (j := .plane) (radialMorphism (k := AlgebraicClosure (ZMod p)))).obj
        ((shiftFunctor ((nativeSystem A).Derived .plane) (2 : ℤ)).obj
          (((nativeSystem A).degreeZero .plane).obj F))) ≅
    W.originWild.obj (((nativeSystem A).pull (i := .origin) (j := .plane)
      (radialMorphism (k := AlgebraicClosure (ZMod p)))).obj F) :=
  ((nativeSystem A).ordinary .origin (-2) ⋙ W.originWild).mapIso
    ((((nativeSystem A).pull (i := .origin) (j := .plane)
      (radialMorphism (k := AlgebraicClosure (ZMod p)))).mapDerivedCategory.commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor ((nativeSystem A).Derived .origin) (2 : ℤ)).mapIso
        (((nativeSystem A).degreeZeroPullback (i := .origin) (j := .plane)
          (radialMorphism (k := AlgebraicClosure (ZMod p)))).app F)) ≪≫
    W.originWild.mapIso
      (((nativeSystem A).ordinary .origin (-2)).mapIso
        (((DerivedCategory.singleFunctors (NC .origin)).shiftIso (2 : ℤ) (-2) 0 (by decide)).app _) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (NC .origin) (-2)).app _)

variable {D W}

include H in
omit [∀ n, (F2.tate n).CommShift ℤ] in
/-- Positive-rank triviality is a general lisse/wild-stalk application;
this theorem has no phase or inverse-point conclusion. -/
theorem ordinaryInverse_lisse_rank (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1)
    (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p)) (C : OC point) :
    Lisse ((ordinaryPointInverse point hPoint P AS z ψ).obj C) ∧
    Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj
      ((ordinaryPointInverse point hPoint P AS z ψ).obj C)) = Module.finrank ℂ (fiber.obj C) := by
  have hF := H.lissePointAS ψ hψ z C
  have hr := H.lisseIso (RankTwoFourierKernelCoordinates.reflectionIso (AlgebraicClosure (ZMod p))) _ hF
  refine ⟨H.lisseTate (2 : ℤ) _ hr, ?_⟩
  exact (H.rankTate (2 : ℤ) _ hr).trans
    ((reflection_fiber_rank (A := A) point hPoint fiber _).trans (H.rankPointAS ψ hψ z C))

variable (JRep : B.Obj .parameter ⥤ FDRep ℂ G)
  (characters : CharacterLaws (OriginPoleWildFromOriginalParameter.oldCharacter
    (J := JRep) (AS (CanonicalSourceCharacter.prime p))))
  [fiber.Faithful] [fiber.PreservesZeroMorphisms]

include H characters in
/-- The actual intrinsic Simple/point-support theorem. No zero-phase
premise, target Fourier support law or freely chosen Simple predicate. -/
theorem inversePointZeroPhase
    (L2 : RankTwoFourierFromNativeASKernel.PublishedLaws kernel hKernel F2 AS D hp2)
    (stalk : StalkLaws D point hPoint fiber)
    (Q : Obj D) (simpleQ : CategoryTheory.Simple Q)
    (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))
    (hsupport : geometricSupport D point hPoint fiber Q = {z}) :
    (0 : PhaseField (AlgebraicClosure (ZMod p))) ∈
      (NativeLocalRulesFromRadialIsomorphisms.rebasedPhaseData JRep
        (AS (CanonicalSourceCharacter.prime p))).phases
      ((radialFunctor (D := D) W).obj ((RankTwoFourierFromNativeASKernel.inverseFunctor L2).obj Q)) := by
  let := simpleQ
  have hfull : {x | ∃ n : ℤ, Nontrivial (pointCohomology D point hPoint fiber Q x n)} ⊆ {z} := by
    rw [← geometricSupport_eq_full stalk Q, hsupport]
  obtain ⟨C, ⟨eQ⟩⟩ := H.pointEssentialImage z
    (point_isClosedImmersion (AlgebraicClosure (ZMod p)) z) Q hfull
  have hQnonzero : ¬ IsZero Q.obj := by
    intro hzero
    apply CategoryTheory.id_nonzero Q
    apply D.plane.ι.map_injective
    change (𝟙 Q.obj) = 0
    exact (IsZero.iff_id_eq_zero Q.obj).mp hzero
  have hCnonzero : ¬ IsZero C := by
    intro hz
    have hz0 : IsZero ((A.degreeZero (pointIndex point)).obj C) :=
      Functor.map_isZero (DerivedCategory.singleFunctor (OC point) 0) hz
    exact hQnonzero ((Functor.map_isZero (P.pointPush
      (indexedPointMorphism (K0 := ZMod p) point hPoint z)) hz0).of_iso eQ)
  have hFiber : Nontrivial (fiber.obj C) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    apply hCnonzero
    apply (IsZero.iff_id_eq_zero C).mpr
    apply fiber.map_injective
    rw [fiber.map_id, fiber.map_zero]
    exact (IsZero.iff_id_eq_zero (fiber.obj C)).mp (ModuleCat.isZero_iff_subsingleton.mpr hs)
  let := H.coefficientFinite C
  have hRank : 0 < Module.finrank ℂ (fiber.obj C) := Module.finrank_pos_iff.mpr hFiber
  let ψ := CanonicalSourceCharacter.prime p
  have hψ : ψ ≠ 1 := CanonicalSourceCharacter.prime_ne_one p
  let F := (ordinaryPointInverse point hPoint P AS z ψ).obj C
  obtain ⟨hLisse, hPlaneRank⟩ := ordinaryInverse_lisse_rank H ψ hψ z C
  let R := W.originWild.obj (((nativeSystem A).pull (i := .origin) (j := .plane)
    (radialMorphism (k := AlgebraicClosure (ZMod p)))).obj F)
  have hRtrivial : Representation.IsTrivial R.ρ := H.wildLisseTrivial _ _ hLisse
  have hRrank : 0 < Module.finrank ℂ R := by
    rw [H.wildLisseRank _ _ hLisse (originZero_radial (AlgebraicClosure (ZMod p))), hPlaneRank]
    exact hRank
  let eR : (radialFunctor (D := D) W).obj ((RankTwoFourierFromNativeASKernel.inverseFunctor L2).obj Q) ≅ R :=
    ((nativeSystem A).derivedPull (i := .origin) (j := .plane)
      (radialMorphism (k := AlgebraicClosure (ZMod p))) ⋙
      (nativeSystem A).ordinary .origin (-2) ⋙ W.originWild).mapIso
        ((F2.derivedInverse kernel hKernel AS ψ).mapIso eQ ≪≫ inversePointComparison H ψ hψ z C) ≪≫
      ordinaryRadialComparison W F
  have hZero : (0 : PhaseField (ZMod p)) ∈ homSupport
      (OriginPoleWildFromOriginalParameter.oldCharacter (J := JRep) (AS ψ)) R := by
    rw [homSupport_iso (PhaseRulesFromSeparatedCharacters.isoOfEquiv
      (PhaseRulesFromSeparatedCharacters.trivialCharacterEquiv characters R hRtrivial)),
      characters.finiteSum_support]
    exact ⟨⟨0, hRrank⟩, rfl⟩
  have hZeroOriginal : (0 : PhaseField (ZMod p)) ∈ homSupport
      (OriginPoleWildFromOriginalParameter.oldCharacter (J := JRep) (AS ψ))
      ((radialFunctor (D := D) W).obj ((RankTwoFourierFromNativeASKernel.inverseFunctor L2).obj Q)) := by
    rw [homSupport_iso eR]
    exact hZero
  apply (OriginPoleWildFromOriginalParameter.image_phase_iff
    (PD := canonicalPD B JRep (AS ψ)) (0 : PhaseField (AlgebraicClosure (ZMod p))) _).mpr
  simpa only [map_zero, canonicalPD, characterPhaseData] using hZeroOriginal

end PrimeGap182.TypeIII.NativePunctualFourierFromLisseWildStalks

#print axioms PrimeGap182.TypeIII.NativePunctualFourierFromLisseWildStalks.inverse_radial_phase_X
#print axioms PrimeGap182.TypeIII.NativePunctualFourierFromLisseWildStalks.inversePointComparison
#print axioms PrimeGap182.TypeIII.NativePunctualFourierFromLisseWildStalks.ordinaryRadialComparison
#print axioms PrimeGap182.TypeIII.NativePunctualFourierFromLisseWildStalks.inversePointZeroPhase
