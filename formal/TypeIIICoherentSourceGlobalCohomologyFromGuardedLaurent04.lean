import TypeIIISourceGeometricRulesFromGlobalLissity
import TypeIIIUniformSourceLocalObservablesFromParameterFibers
import TypeIIIFullFourierCoreFromNativeBoundedOperations
import TypeIIIQSTCompactBridgeFromCompactifiedDerivedPushforward
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Ordinary source cohomology from the guarded good-Laurent-family theorem

The source category remains genuine ordinary constructible sheaves. The input
is the literal tensor of the three original inverse images; its dual is the
ordinary internal-Hom dual. Both rank and Swan observables use SAME-U fibers
and SAME-M local profiles at EVERY field-valued unit parameter, including
lambda = 1. Purity uses the original rational-point Frobenius.

The explicit GENERAL clauses below are external theorem-application premises,
not constructions of an adic category or selected family conclusions. In
particular, compact_good is the CONTINUOUS ADIC extension of Laumon 1981
2.1.1(ii)/2.1.2 on an independently good geometry, with finite-coefficient
lattice comparison and independence of compactification required by its
interpretation. It is not asserted to be the literal finite-field-coefficient
statement of Laumon. No arbitrary Nagata middle is assumed smooth or good.
The accompanying eligibility ledger specifies these remaining model meanings.
ONE genuine arithmetic stalk/Frobenius family RF is fixed before the prime.
Weight clauses refer only to RF p, not every abstract Data record. The final
GC and cohomology specialization use these literal RF p dictionaries, without
an additional selected equality or interpretation-switch premise.

No GC, whole-input lissity, conductor constancy, image lissity or finished
endpoint is an input. GENERAL tensor/local, scalar and cohomology laws, plus
primitive Kl3/AS properties, derive those conclusions. All operators remain
ordinary until an independent, guarded perverse-normalization application.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CoherentSourceGlobalCohomologyFromGuardedLaurent04
open ExactInverseImagesToDerived PublishedPhysicalConstruction
open QSTCompactBridgeFromCompactifiedDerivedPushforward
open PrimitiveRamificationFromGeneralKatzTheory
open UniformSourceLocalObservablesFromParameterFibers

/-- Geometry only: a good P1 compactification of the original relative Gm.
The two labeled sections are the actual zero/infinity charts. No sheaf,
ULA, rank, conductor, cohomology or lissity conclusion occurs in this record. -/
structure GoodSourceGeometry (K : Type) [Field K] where
  source : FieldPresentation K (StartingSourceMaps.sourceScheme K)
  target : FieldPresentation K (PhysicalTorusMorphism.torusScheme K)
  factor : FullFourierCoreFromNativeBoundedOperations.CompactificationOver K
    source target (SourceProjectionForQST.projection K)
  [smoothOne : SmoothOfRelativeDimension 1 factor.properMorphism]
  coordinateIso : StartingSourceMaps.sourceScheme K ≅
    Spec (.of (LaurentPolynomial (PhysicalTorusMorphism.TorusRing K)))
  projection_square : coordinateIso.hom ≫ Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.C : PhysicalTorusMorphism.TorusRing K →+*
      LaurentPolynomial (PhysicalTorusMorphism.TorusRing K))) =
        SourceProjectionForQST.projection K
  boundary : Scheme
  boundaryEmbedding : boundary ⟶ factor.middle
  [boundaryClosed : IsClosedImmersion boundaryEmbedding]
  [boundaryFinite : IsFinite (boundaryEmbedding ≫ factor.properMorphism)]
  [boundaryFlat : Flat (boundaryEmbedding ≫ factor.properMorphism)]
  boundary_complement : Set.range boundaryEmbedding.base =
    (Set.range factor.openMorphism.base)ᶜ
  zeroChart : Spec (.of (Polynomial (PhysicalTorusMorphism.TorusRing K))) ⟶ factor.middle
  infinityChart : Spec (.of (Polynomial (PhysicalTorusMorphism.TorusRing K))) ⟶ factor.middle
  [zeroOpen : IsOpenImmersion zeroChart]
  [infinityOpen : IsOpenImmersion infinityChart]
  positive_chart : coordinateIso.hom ≫ Spec.map (CommRingCat.ofHom
    (R := Polynomial (PhysicalTorusMorphism.TorusRing K))
    (S := LaurentPolynomial (PhysicalTorusMorphism.TorusRing K)) Polynomial.toLaurent) ≫ zeroChart = factor.openMorphism
  inverse_chart : coordinateIso.hom ≫ Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.invert (R := PhysicalTorusMorphism.TorusRing K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (R := Polynomial (PhysicalTorusMorphism.TorusRing K))
        (S := LaurentPolynomial (PhysicalTorusMorphism.TorusRing K)) Polynomial.toLaurent) ≫
            infinityChart = factor.openMorphism
  zero_over : zeroChart ≫ factor.properMorphism = Spec.map (CommRingCat.ofHom
    (Polynomial.C : PhysicalTorusMorphism.TorusRing K →+*
      Polynomial (PhysicalTorusMorphism.TorusRing K)))
  infinity_over : infinityChart ≫ factor.properMorphism = Spec.map (CommRingCat.ofHom
    (Polynomial.C : PhysicalTorusMorphism.TorusRing K →+*
      Polynomial (PhysicalTorusMorphism.TorusRing K)))
  zero_infinity_disjoint : Disjoint
    (Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom
      (0 : PhysicalTorusMorphism.TorusRing K))) ≫ zeroChart).base)
    (Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom
      (0 : PhysicalTorusMorphism.TorusRing K))) ≫ infinityChart).base)
  boundary_labels : Set.range boundaryEmbedding.base =
    Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom
      (0 : PhysicalTorusMorphism.TorusRing K))) ≫ zeroChart).base ∪
    Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom
      (0 : PhysicalTorusMorphism.TorusRing K))) ≫ infinityChart).base

attribute [instance] GoodSourceGeometry.smoothOne GoodSourceGeometry.boundaryClosed
  GoodSourceGeometry.boundaryFinite GoodSourceGeometry.boundaryFlat
  GoodSourceGeometry.zeroOpen GoodSourceGeometry.infinityOpen

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalClosed (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (L : ∀ X : Scheme, ObjectProperty (C X))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (M : LocalRealization C) (Z : OriginProfiles C M)
  (O : Operations C)
local instance allDerived : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- Actual ordinary parameter operations. They carry no closure or weight law.
The ledger requires genuine ordinary dual(-1) and the fixed weight-zero sign. -/
structure ParameterOperations where
  dualTateMinusOne : ∀ X : Scheme, (C X)ᵒᵖ ⥤ C X
  signed : ∀ (p : ℕ) [Fact p.Prime],
    C (PhysicalTorusMorphism.torusScheme (ZMod p)) ⥤
      C (PhysicalTorusMorphism.torusScheme (ZMod p))

variable (PO : ParameterOperations C)
  (RF : ∀ (q : ℕ) [Fact q.Prime],
    RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U q))

/-- SAME single_0, compactified six operations, H^1 and support map. -/
def nativeCohomology (K : Type) [Field K]
    (c : Compactification (SourceProjectionForQST.projection K)) :=
  (cohomologyData C O c 1).cohomology

/-- Actual generic source rank and zero/infinity Swan observables. -/
def conductor (K : Type) [Field K] (A : C (StartingSourceMaps.sourceScheme K))
    (t : ParameterPoint K) : ℕ :=
  let S := sourceObservables K C U G L M Z
  (S.rank A + S.swanZero A t) + (S.rank A + S.swanInfinity A t)

/-- GENERAL guarded clauses on every finite base field and every
ordinary lisse source object. No selected input, GC or endpoint occurs here.
compact_good holds for EVERY ordinary H^n and EVERY retained compactification;
the good geometry is independent of A. Its continuous-adic/lattice upgrade
and SAME-operator interpretation are explicit external premises. -/
structure GeneralGuardedFamilyLaws : Prop where
  compact_good : ∀ (K : Type) [Field K] [Fintype K] (_h2 : (2 : K) ≠ 0),
    GoodSourceGeometry K → ∀ (c : Compactification (SourceProjectionForQST.projection K))
      (A : C (StartingSourceMaps.sourceScheme K)),
    L (StartingSourceMaps.sourceScheme K) A →
    (∃ N : ℕ, ∀ t : ParameterPoint K, conductor C U L G M Z K A t = N) →
    ∀ n : ℤ, L (PhysicalTorusMorphism.torusScheme K) ((cohomologyData C O c n).compact.obj A)
  ordinary_duality : ∀ (K : Type) [Field K] [Fintype K] (_h2 : (2 : K) ≠ 0)
      (c : Compactification (SourceProjectionForQST.projection K))
      (A : C (StartingSourceMaps.sourceScheme K)),
    L (StartingSourceMaps.sourceScheme K) A →
    sourceIsoclinic K C U L M
      ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _).obj (Opposite.op A)) 1 →
    L (PhysicalTorusMorphism.torusScheme K) ((nativeCohomology C O K c).compact
      ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _).obj (Opposite.op A))) →
    Nonempty ((nativeCohomology C O K c).ordinary A ≅
      (PO.dualTateMinusOne _).obj (Opposite.op ((nativeCohomology C O K c).compact
        ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _).obj (Opposite.op A)))))
  dualTate_lisse : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0) {X : Scheme}
      (_PX : FieldPresentation K X) (A : C X),
    L X A → L X ((PO.dualTateMinusOne X).obj (Opposite.op A))
  image_lisse : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0) {X : Scheme}
      (_PX : FieldPresentation K X) (A B : C X) (f : A ⟶ B),
    L X A → L X B → L X (Abelian.image f)
  image_weight : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0)
      (c : Compactification (SourceProjectionForQST.projection (ZMod p)))
      (A : C (StartingSourceMaps.sourceScheme (ZMod p))) (a : ℝ),
    L (StartingSourceMaps.sourceScheme (ZMod p)) A →
    ParameterPurityFromStalks.pointwisePure (RF p) .source A a →
    sourceIsoclinic (ZMod p) C U L M A 1 →
    sourceIsoclinic (ZMod p) C U L M
      ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _).obj (Opposite.op A)) 1 →
    L (PhysicalTorusMorphism.torusScheme (ZMod p)) ((nativeCohomology C O (ZMod p) c).compact A) →
    L (PhysicalTorusMorphism.torusScheme (ZMod p)) ((nativeCohomology C O (ZMod p) c).compact
      ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _).obj (Opposite.op A))) →
    ParameterPurityFromStalks.pointwisePure (RF p) .torus
      (parabolicCore (nativeCohomology C O (ZMod p) c) A) (a + 1)
  signed_lisse : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0) A,
    L (PhysicalTorusMorphism.torusScheme (ZMod p)) A →
    L (PhysicalTorusMorphism.torusScheme (ZMod p)) ((PO.signed p).obj A)
  signed_weight : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0)
      A a,
    ParameterPurityFromStalks.pointwisePure (RF p) .torus A a →
    ParameterPurityFromStalks.pointwisePure (RF p) .torus ((PO.signed p).obj A) a
  dualTate_weight : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0)
      A a,
    L (PhysicalTorusMorphism.torusScheme (ZMod p)) A →
    ParameterPurityFromStalks.pointwisePure (RF p) .torus A a →
    ParameterPurityFromStalks.pointwisePure (RF p) .torus
      ((PO.dualTateMinusOne _).obj (Opposite.op A)) (2 - a)

variable (p : ℕ) [Fact p.Prime]
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

/-- Computed source dictionary: ordinary tensor/dual, global lissity,
actual generic rank, all geometric fibers, and actual Frobenius purity. -/
def nativeCurve :=
  (SourcePurityFromStalks.geometry R (sourceObservables (ZMod p) C U G L M Z)).curveData
    (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _)

def nativeParameter : ParameterData (C (PhysicalTorusMorphism.torusScheme (ZMod p))) where
  Lisse := L (PhysicalTorusMorphism.torusScheme (ZMod p))
  Pure := ParameterPurityFromStalks.pointwisePure R .torus
  dualTateMinusOne A := (PO.dualTateMinusOne _).obj (Opposite.op A)
  signed A := (PO.signed p).obj A

def nativeLine (LO : LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine (ZMod p)))) :=
  LinePurityFromStalks.geometry R
    (SourceGlobalLissityFromKatzPullbacks.bindLineLisseOnUnits (ZMod p) C U L LO)

def nativePullbacks := FourierSourcePullbacks.originalPullbackData (ZMod p)
  (CanonicalPrimeFramework.primeSource C U p).geometricPullbacks

/-- Global source-factor lissity is proved, rather than included among the
four GENERAL scalar numeric/local hypotheses. Purity is proved from R. -/
theorem scalarRules
    (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
    (LO : LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine (ZMod p))))
    (rank : ∀ c A, (nativeLine C U L p R LO).LisseOnUnits A →
      (nativeCurve C U L G M Z p R).rank
        ((nativePullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A) =
          (nativeLine C U L p R LO).rank A)
    (tame : ∀ c A, (nativeLine C U L p R LO).TameZero A →
      (nativeCurve C U L G M Z p R).TameZero
        ((nativePullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A))
    (breaks : ∀ c A s, (nativeLine C U L p R LO).BreaksLE A s →
      (nativeCurve C U L G M Z p R).BreaksLE
        ((nativePullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A) s)
    (isoclinic : ∀ c A s, (nativeLine C U L p R LO).Isoclinic A s →
      (nativeCurve C U L G M Z p R).Isoclinic
        ((nativePullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A) s) :
    CanonicalCurveInput.ScalarPullbackRules (nativePullbacks C U p)
      (nativeLine C U L p R LO) (nativeCurve C U L G M Z p R) where
  lisse := SourceGlobalLissityFromKatzPullbacks.scalar_lisse (ZMod p) C U L lissePull
  rank := rank
  pure := LinePurityFromStalks.scalar_pure R
  tame := tame
  breaks := breaks
  isoclinic := isoclinic

/-- The exact nine-field endpoint GC is constructed from the GENERAL laws;
no GC or selected family lissity/conductor is assumed. -/
theorem cohomologyRules
    (laws : GeneralGuardedFamilyLaws C U L G M Z O PO RF)
    (h2 : (2 : ZMod p) ≠ 0) (good : GoodSourceGeometry (ZMod p))
    (c : Compactification (SourceProjectionForQST.projection (ZMod p))) :
    CohomologyRules (nativeCurve C U L G M Z p (RF p))
      (nativeCohomology C O (ZMod p) c) (nativeParameter C U L PO p (RF p)) where
  compact_lisse A hA hN := laws.compact_good (ZMod p) h2 good c A hA hN 1
  ordinary_duality A hA hs hl := laws.ordinary_duality (ZMod p) h2 c A hA hs hl
  dualTate_lisse A hA := laws.dualTate_lisse (ZMod p) h2 good.target A hA
  lisse_of_iso A B h hB := by
    obtain ⟨e⟩ := h
    exact (L _).prop_of_iso e.symm hB
  image_lisse A B f hA hB := laws.image_lisse (ZMod p) h2 good.target A B f hA hB
  image_pure A a hl hp hs hd hc hdc := laws.image_weight p h2 c A a hl hp hs hd hc hdc
  signed_lisse A hA := laws.signed_lisse p h2 A hA
  signed_pure A a hA := laws.signed_weight p h2 A a hA
  dualTate_pure A a hl hp := laws.dualTate_weight p h2 A a hl hp

section CanonicalInput
variable (LO : LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine (ZMod p))))
  (SR : CanonicalCurveInput.ScalarPullbackRules (nativePullbacks C U p)
    (nativeLine C U L p R LO) (nativeCurve C U L G M Z p R))
  (kl as : C (StartingSourceMaps.affineLine (ZMod p)))
  (hkl : CanonicalCurveInput.Kl3Properties (nativeLine C U L p R LO) kl)
  (has : CanonicalCurveInput.ASProperties (nativeLine C U L p R LO) as)
  (CR : CurveRules (nativeCurve C U L G M Z p R))

abbrev canonicalInput := CanonicalCurveInput.canonicalInput (nativePullbacks C U p)
  (nativeLine C U L p R LO) SR kl as hkl has

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
/-- Same original tensor/dual/input maps, without a selected identification premise. -/
theorem input_is_literal :
    (canonicalInput C U L G M Z p R LO SR kl as hkl has).input =
      SourceGlobalLissityFromKatzPullbacks.sourceInput (ZMod p) C U kl as := rfl

include CR

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
/-- Both entire families are globally lisse, rank nine, tame at zero and
uniformly pure slope one at infinity. No restriction lambda != 1 occurs. -/
theorem input_and_dual_geometry :
    let D := nativeCurve C U L G M Z p R
    let A := (canonicalInput C U L G M Z p R LO SR kl as hkl has).input
    D.Lisse A ∧ D.rank A = 9 ∧ D.TameZero A ∧ D.Isoclinic A 1 ∧
      D.Lisse (D.dual A) ∧ D.rank (D.dual A) = 9 ∧
      D.TameZero (D.dual A) ∧ D.Isoclinic (D.dual A) 1 := by
  let I := canonicalInput C U L G M Z p R LO SR kl as hkl has
  have hl := I.input_lisse CR
  exact ⟨hl, I.input_rank CR, I.input_tame CR, I.input_slope_one CR,
    CR.dual_lisse _ hl, (CR.dual_rank _ hl).trans (I.input_rank CR),
    CR.dual_tame _ (I.input_tame CR), CR.dual_isoclinic _ _ (I.input_slope_one CR)⟩

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
/-- The SAME actual infinity profiles have rank nine and only slope one
on every geometric parameter fiber. This follows from the computed Swan
conductors and the finite-profile slope-one identity, with no new rank input. -/
theorem all_geometric_fiber_ranks_and_slopes (t : ParameterPoint (ZMod p)) :
    let D := nativeCurve C U L G M Z p R
    let A := (canonicalInput C U L G M Z p R LO SR kl as hkl has).input
    let B := sourceInfinityProfile (ZMod p) C U M A t
    let Bd := sourceInfinityProfile (ZMod p) C U M (D.dual A) t
    B.rank = 9 ∧ Bd.rank = 9 ∧
      (∀ r ∈ B.multiplicity.support, r = 1) ∧
      (∀ r ∈ Bd.multiplicity.support, r = 1) := by
  let I := canonicalInput C U L G M Z p R LO SR kl as hkl has
  let D := nativeCurve C U L G M Z p R
  have hs := I.input_slope_one CR
  have hd := CR.dual_isoclinic _ _ hs
  change L (StartingSourceMaps.sourceScheme (ZMod p)) I.input ∧
    ∀ s : ParameterPoint (ZMod p), ∀ r ∈
      (sourceInfinityProfile (ZMod p) C U M I.input s).multiplicity.support, r = 1 at hs
  change L (StartingSourceMaps.sourceScheme (ZMod p)) (D.dual I.input) ∧
    ∀ s : ParameterPoint (ZMod p), ∀ r ∈
      (sourceInfinityProfile (ZMod p) C U M (D.dual I.input) s).multiplicity.support, r = 1 at hd
  have hr := NaturalSwanFromFiniteBreakProfile.naturalSwan_of_isoclinic_one _ (hs.2 t)
  have hrd := NaturalSwanFromFiniteBreakProfile.naturalSwan_of_isoclinic_one _ (hd.2 t)
  exact ⟨hr.symm.trans (I.input_swan CR t).2,
    hrd.symm.trans (I.dual_input_swan CR t).2, hs.2 t, hd.2 t⟩

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
/-- Actual zero/infinity conductors and boundary rank+Swan sum on ALL
field-valued unit-parameter fibers, including geometric generic fibers. -/
theorem all_fiber_conductors (t : ParameterPoint (ZMod p)) :
    let D := nativeCurve C U L G M Z p R
    let I := canonicalInput C U L G M Z p R LO SR kl as hkl has
    D.swanZero I.input t = 0 ∧ D.swanInfinity I.input t = 9 ∧
    D.swanZero (D.dual I.input) t = 0 ∧ D.swanInfinity (D.dual I.input) t = 9 ∧
    conductor C U L G M Z (ZMod p) I.input t = 27 ∧
    conductor C U L G M Z (ZMod p) (D.dual I.input) t = 27 := by
  let I := canonicalInput C U L G M Z p R LO SR kl as hkl has
  exact ⟨(I.input_swan CR t).1, (I.input_swan CR t).2,
    (I.dual_input_swan CR t).1, (I.dual_input_swan CR t).2,
    I.input_conductor CR t, I.dual_input_conductor CR t⟩

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
/-- The previously delicate lambda=1 fiber is explicitly included for EVERY
coefficient-field extension and EVERY nonzero xi. -/
theorem lambda_one_conductor (E : Type) [Field E] [Algebra (ZMod p) E] (xi : Eˣ) :
    let D := nativeCurve C U L G M Z p R
    let I := canonicalInput C U L G M Z p R LO SR kl as hkl has
    conductor C U L G M Z (ZMod p) I.input (parameterPoint (ZMod p) E 1 xi) = 27 ∧
    conductor C U L G M Z (ZMod p) (D.dual I.input)
      (parameterPoint (ZMod p) E 1 xi) = 27 := by
  let I := canonicalInput C U L G M Z p R LO SR kl as hkl has
  exact ⟨I.input_conductor CR _, I.dual_input_conductor CR _⟩

end CanonicalInput

section CoherentModel
variable (LO : LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine (ZMod p))))
  (SR : CanonicalCurveInput.ScalarPullbackRules (nativePullbacks C U p)
    (nativeLine C U L p (RF p) LO) (nativeCurve C U L G M Z p (RF p)))
  (kl as : C (StartingSourceMaps.affineLine (ZMod p)))
  (hkl : CanonicalCurveInput.Kl3Properties (nativeLine C U L p (RF p) LO) kl)
  (has : CanonicalCurveInput.ASProperties (nativeLine C U L p (RF p) LO) as)
  (CR : CurveRules (nativeCurve C U L G M Z p (RF p)))
include CR

/-- Ordinary Hc1, ordinary H1 and their literal image are globally lisse on
ALL Gm^2. The same image has weight one. No finished cohomology field is input. -/
theorem actual_cohomology_geometry
    (laws : GeneralGuardedFamilyLaws C U L G M Z O PO RF)
    (h2 : (2 : ZMod p) ≠ 0) (good : GoodSourceGeometry (ZMod p))
    (c : Compactification (SourceProjectionForQST.projection (ZMod p))) :
    let D := nativeCurve C U L G M Z p (RF p)
    let H := nativeCohomology C O (ZMod p) c
    let P := nativeParameter C U L PO p (RF p)
    let I := canonicalInput C U L G M Z p (RF p) LO SR kl as hkl has
    P.Lisse (H.compact I.input) ∧ P.Lisse (H.compact (D.dual I.input)) ∧
      P.Lisse (H.ordinary I.input) ∧ P.Lisse (parabolicCore H I.input) ∧
        P.Pure (parabolicCore H I.input) 1 := by
  let I := canonicalInput C U L G M Z p (RF p) LO SR kl as hkl has
  let GC := cohomologyRules C U L G M Z O PO RF p laws h2 good c
  exact ⟨PublishedPhysicalConstruction.compact_lisse I CR GC,
    PublishedPhysicalConstruction.compact_dual_lisse I CR GC,
    PublishedPhysicalConstruction.ordinary_lisse I CR GC,
    PublishedPhysicalConstruction.core_lisse I CR GC,
    PublishedPhysicalConstruction.core_pure I CR GC⟩
end CoherentModel
end PrimeGap182.TypeIII.CoherentSourceGlobalCohomologyFromGuardedLaurent04
