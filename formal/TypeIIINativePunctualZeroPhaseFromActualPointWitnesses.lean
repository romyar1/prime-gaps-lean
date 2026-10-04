import TypeIIINativePunctualFourierFromLisseWildStalks

/-!
The fifth original punctual phase clause is a flat application of actual
ordinary-point underlying bounded-proper witnesses, exact inverse-point
realization, ordinary lisse/rank consequences, and SAME-W geometric wild
recognition consequences. The pointObject and inversePointRealization
arguments MUST be computed from the actual bounded closed-point/T2,
reflection/Tate chain; they are theorem arguments, not primitive selected
completed-law capabilities in a final universal constructor.

The wild consequences here are conditional selected consequences of a
genuine before-prime geometric trait/fiber model and explicit group/functor
alignment to W. They are NOT defined as an arbitrary-W lisse/unramified
MODEL. Actual continuous finite-coefficient realization remains external.
No old unbounded RankOne/RankTwo/Linear/Punctual Data or final rule record
is a parameter. Intrinsic Simple, the original singleton geometric support,
original coefficient character and zero phase are unchanged.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped Classical PrimeGap182.TypeIII.TwoAdicComplexEmbedding
namespace PrimeGap182.TypeIII.NativePunctualZeroPhaseFromActualPointWitnesses
open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages NativeSurfaceFromGeometricStalks
open LinearRadialPhaseFromPoleTransport PublishedPhaseApplication PhaseDataFromOriginalCharacters
open NativePunctualFourierFromLisseWildStalks

universe mu g
variable {p : ℕ} [Fact p.Prime] {J : Type}
  {B : SourceInverseImageSystem.System.{0,mu} (ZMod p)}
  {otherScheme : J -> Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index -> Type}
  [∀ i, Category.{mu} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{mu} LC] [Abelian LC]
  {OC : J -> Type} [∀ i, Category.{mu} (OC i)] [∀ i, Abelian (OC i)]
  {A : OrdinarySystem (extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme))
    (extensionObjects B (extraObjects NC LC OC))}
local instance commonLocalizations : ∀ i, HasDerivedCategory.{mu}
    (extensionObjects B (extraObjects NC LC OC) i) :=
  fun _ => HasDerivedCategory.standard _
local instance nativeLocalizations : ∀ i, HasDerivedCategory.{mu} (NC i) :=
  fun _ => HasDerivedCategory.standard _
variable (D : Admissibility A) (point : J)
  (hPoint : otherScheme point = pointScheme (AlgebraicClosure (ZMod p)))
  (fiber : OC point ⥤ ModuleCat.{mu} ℂ) [MonoidalCategory (NC .plane)]
  (AS : AddChar (ZMod p) (PadicAlgCl 2) -> B.Obj .line)
  (ordinaryTate : ℤ -> NC .plane ⥤ NC .plane)
  (Lisse : NC .plane -> Prop)

/-- Literal ordinary positive-point AS/reflection/Tate(+2), without a Data wrapper. -/
def ordinaryInverse (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))
    (psi : AddChar (ZMod p) (PadicAlgCl 2)) :=
  ordinaryPointFourier (A := A) point hPoint AS z psi ⋙
    ordinaryReflection (A := A) ⋙ ordinaryTate 2

variable
  (lissePoint : ∀ psi, psi ≠ 1 -> ∀ z C,
    Lisse ((ordinaryPointFourier (A := A) point hPoint AS z psi).obj C))
  (rankPoint : ∀ psi, psi ≠ 1 -> ∀ z C,
    Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj
      ((ordinaryPointFourier (A := A) point hPoint AS z psi).obj C)) =
      Module.finrank ℂ (fiber.obj C))
  (lisseIso : ∀ e : FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)) ≅
      FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)),
    ∀ F, Lisse F -> Lisse (((nativeSystem A).pull (i := .plane) (j := .plane) e.hom).obj F))
  (lisseTate : ∀ n F, Lisse F -> Lisse ((ordinaryTate n).obj F))
  (rankTate : ∀ n F, Lisse F ->
    Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj ((ordinaryTate n).obj F)) =
      Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj F))

include lissePoint rankPoint lisseIso lisseTate rankTate in
/-- Lissity and rank of the ordinary inverse are consequences of separate general laws. -/
theorem ordinaryInverseLisseRank (psi : AddChar (ZMod p) (PadicAlgCl 2)) (hpsi : psi ≠ 1)
    (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p)) (C : OC point) :
    Lisse ((ordinaryInverse (A := A) point hPoint AS ordinaryTate z psi).obj C) ∧
    Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj
      ((ordinaryInverse (A := A) point hPoint AS ordinaryTate z psi).obj C)) =
      Module.finrank ℂ (fiber.obj C) := by
  have hF := lissePoint psi hpsi z C
  have hR := lisseIso (RankTwoFourierKernelCoordinates.reflectionIso (AlgebraicClosure (ZMod p))) _ hF
  refine ⟨lisseTate 2 _ hR, ?_⟩
  exact (rankTate 2 _ hR).trans
    ((reflection_fiber_rank (A := A) point hPoint fiber _).trans (rankPoint psi hpsi z C))

variable (inverse : Obj D ⥤ Obj D)
  (pointObject : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p) ->
    OC point ⥤ (nativeSystem A).Derived .plane)
  (pointObjectZero : ∀ z, (pointObject z).PreservesZeroMorphisms)
  (pointEssentialImage : ∀ z, ∀ Q : Obj D,
    {x | ∃ n : ℤ, Nontrivial (pointCohomology D point hPoint fiber Q x n)} ⊆ {z} ->
    ∃ C : OC point, Nonempty (Q.obj ≅ (pointObject z).obj C))
  (inversePointRealization : ∀ z C (Q : Obj D),
    (Q.obj ≅ (pointObject z).obj C) ->
    ((inverse.obj Q).obj ≅ (shiftFunctor ((nativeSystem A).Derived .plane) (2 : ℤ)).obj
      (((nativeSystem A).degreeZero .plane).obj
        ((ordinaryInverse (A := A) point hPoint AS ordinaryTate z
          (CanonicalSourceCharacter.prime p)).obj C))))
  (coefficientFinite : ∀ C, FiniteDimensional ℂ (fiber.obj C))
  {G : Type g} [Group G] (W : OrdinaryWild (E := ℂ) (G := G) A)
  (recognizedWildUnramified : ∀ (f : originScheme (AlgebraicClosure (ZMod p)) ⟶
      FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p))) F,
    Lisse F -> Representation.IsTrivial
      (W.originWild.obj (((nativeSystem A).pull (i := .origin) (j := .plane) f).obj F)).ρ)
  (recognizedWildRank : ∀ (f : originScheme (AlgebraicClosure (ZMod p)) ⟶
      FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p))) F, Lisse F ->
    originZero (AlgebraicClosure (ZMod p)) ≫ f = originBasePoint (AlgebraicClosure (ZMod p)) ≫
      pointMorphism (AlgebraicClosure (ZMod p)) (0,0) ->
    Module.finrank ℂ (W.originWild.obj (((nativeSystem A).pull (i := .origin) (j := .plane) f).obj F)) =
      Module.finrank ℂ ((planeFiberZero (A := A) point hPoint fiber).obj F))
  (JRep : B.Obj .parameter ⥤ FDRep ℂ G)
  (characters : CharacterLaws (OriginPoleWildFromOriginalParameter.oldCharacter
    (J := JRep) (AS (CanonicalSourceCharacter.prime p))))
  [fiber.Faithful] [fiber.PreservesZeroMorphisms]
  (stalk : StalkLaws D point hPoint fiber)

include lissePoint rankPoint lisseIso lisseTate rankTate pointObjectZero pointEssentialImage
  inversePointRealization coefficientFinite recognizedWildUnramified recognizedWildRank characters stalk in
/-- Exact intrinsic-Simple/singleton-support original zero-phase clause. -/
theorem inversePointZeroPhase (Q : Obj D) (simpleQ : CategoryTheory.Simple Q)
    (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))
    (hsupport : geometricSupport D point hPoint fiber Q = {z}) :
    (0 : PhaseField (AlgebraicClosure (ZMod p))) ∈
      (NativeLocalRulesFromRadialIsomorphisms.rebasedPhaseData JRep
        (AS (CanonicalSourceCharacter.prime p))).phases ((radialFunctor (D := D) W).obj (inverse.obj Q)) := by
  let := simpleQ
  have hfull : {x | ∃ n : ℤ, Nontrivial (pointCohomology D point hPoint fiber Q x n)} ⊆ {z} := by
    rw [← geometricSupport_eq_full stalk Q, hsupport]
  obtain ⟨C, ⟨eQ⟩⟩ := pointEssentialImage z Q hfull
  have hQnonzero : ¬ IsZero Q.obj := by
    intro hz
    apply CategoryTheory.id_nonzero Q
    apply D.plane.ι.map_injective
    change (𝟙 Q.obj) = 0
    exact (IsZero.iff_id_eq_zero Q.obj).mp hz
  let := pointObjectZero z
  have hCnonzero : ¬ IsZero C := by
    intro hz
    exact hQnonzero ((Functor.map_isZero (pointObject z) hz).of_iso eQ)
  have hFiber : Nontrivial (fiber.obj C) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    apply hCnonzero
    apply (IsZero.iff_id_eq_zero C).mpr
    apply fiber.map_injective
    rw [fiber.map_id, fiber.map_zero]
    exact (IsZero.iff_id_eq_zero (fiber.obj C)).mp (ModuleCat.isZero_iff_subsingleton.mpr hs)
  let := coefficientFinite C
  have hRank : 0 < Module.finrank ℂ (fiber.obj C) := Module.finrank_pos_iff.mpr hFiber
  let psi := CanonicalSourceCharacter.prime p
  let F := (ordinaryInverse (A := A) point hPoint AS ordinaryTate z psi).obj C
  obtain ⟨hLisse,hPlaneRank⟩ := ordinaryInverseLisseRank (A := A) point hPoint fiber AS ordinaryTate Lisse
    lissePoint rankPoint lisseIso lisseTate rankTate psi (CanonicalSourceCharacter.prime_ne_one p) z C
  let R := W.originWild.obj (((nativeSystem A).pull (i := .origin) (j := .plane)
    (radialMorphism (k := AlgebraicClosure (ZMod p)))).obj F)
  have hRtrivial : Representation.IsTrivial R.ρ := recognizedWildUnramified _ _ hLisse
  have hRrank : 0 < Module.finrank ℂ R := by
    rw [recognizedWildRank _ _ hLisse (originZero_radial (AlgebraicClosure (ZMod p))),hPlaneRank]
    exact hRank
  let eR : (radialFunctor (D := D) W).obj (inverse.obj Q) ≅ R :=
    ((nativeSystem A).derivedPull (i := .origin) (j := .plane)
      (radialMorphism (k := AlgebraicClosure (ZMod p))) ⋙
      (nativeSystem A).ordinary .origin (-2) ⋙ W.originWild).mapIso
        (inversePointRealization z C Q eQ) ≪≫ ordinaryRadialComparison W F
  have hZero : (0 : PhaseField (ZMod p)) ∈ homSupport
      (OriginPoleWildFromOriginalParameter.oldCharacter (J := JRep) (AS psi)) R := by
    rw [homSupport_iso (PhaseRulesFromSeparatedCharacters.isoOfEquiv
      (PhaseRulesFromSeparatedCharacters.trivialCharacterEquiv characters R hRtrivial)),
      characters.finiteSum_support]
    exact ⟨⟨0,hRrank⟩,rfl⟩
  have hOriginal : (0 : PhaseField (ZMod p)) ∈ homSupport
      (OriginPoleWildFromOriginalParameter.oldCharacter (J := JRep) (AS psi))
      ((radialFunctor (D := D) W).obj (inverse.obj Q)) := by
    rw [homSupport_iso eR]
    exact hZero
  apply (OriginPoleWildFromOriginalParameter.image_phase_iff
    (PD := canonicalPD B JRep (AS psi)) (0 : PhaseField (AlgebraicClosure (ZMod p))) _).mpr
  simpa only [map_zero,canonicalPD,characterPhaseData] using hOriginal

end PrimeGap182.TypeIII.NativePunctualZeroPhaseFromActualPointWitnesses

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.NativePunctualZeroPhaseFromActualPointWitnesses.ordinaryInverse
#print axioms PrimeGap182.TypeIII.NativePunctualZeroPhaseFromActualPointWitnesses.ordinaryInverseLisseRank
#print axioms PrimeGap182.TypeIII.NativePunctualZeroPhaseFromActualPointWitnesses.inversePointZeroPhase
