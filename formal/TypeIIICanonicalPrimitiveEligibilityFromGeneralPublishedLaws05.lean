import TypeIIIGloballyLisseLineRamificationFromKatz
import TypeIIIPrimitiveRanksFromComputedGenericLineRank

/-!
# Exact primitive eligibility on the same canonical geometry

All published clauses below are fixed before choosing a prime, rank,
character or object. The two selected property records are computed from
the existing general rank, purity and ramification applications. Generic
rank, finite arithmetic stalks, ordinary pullback and local inertia use
the same C/U/F/O/B/G/L/M. Their genuine continuous-adic interpretation is
external; no selected primitive property record is an input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open RationalPointStalksFromUniversalFiber PrimitiveTracesFromGeneralKatzArtinSchreierFormulas
open QSTGenericFiberFromActualGenericPoint QSTCompactBridgeFromCompactifiedDerivedPushforward

universe mu
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  (F : ArithmeticFibers C) (O : Constructions C) (B : CoefficientFibers C F)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (M : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)

local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- Precisely general published laws on one set of ordinary operators. -/
structure GeneralPrimitiveLaws where
  zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _
  unequalKatzLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K), a.upper.length ≠ a.lower.length →
      L (ArithmeticSourceMaps.fiberScheme K) (member C O K h2 a)
  ordinaryKatzRank : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K), Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((boundedDegreeZero C _).obj (O.katz K h2 { a with tateTwist := 0 }))) = a.rank
  ordinaryTateRank : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (n : ℤ) (A : C (ArithmeticSourceMaps.fiberScheme K)),
    Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((boundedDegreeZero C _).obj ((O.tate K h2 n).obj A))) =
    Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A))
  coefficientFormulas : PublishedCoefficientFormulas C U F O B
  lisseGenericPointRank : ∀ (K : Type) [Field K] [Fintype K]
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
      Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A)) =
      Module.finrank ℂ ((F.fiber E).obj ((U.pull (gmPoint K E x)).obj A))
  lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    L Y A → L X ((U.pull f).obj A)
  standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient), ψ ≠ 1 →
      L (StartingSourceMaps.affineLine K) (O.artinSchreier K h2 ψ)
  rawKloostermanWeight : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
    ∀ z ∈ PrimitiveRankPurityFromGeneralKatzTheory.coefficientRoots C F B E
      ((U.pull (gmPoint K E x)).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))),
      Complex.normSq (TwoAdicComplexEmbedding.complexEquiv z) =
        (Fintype.card E : ℝ) ^ (n - 1)
  pointTateIso : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K) (n : ℤ),
    O.lineTate K h2 n ⋙ U.pull x ⋙ F.fiber E ≅ U.pull x ⋙ F.fiber E
  pointTateFrobenius : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K) (n : ℤ)
    (A : C (StartingSourceMaps.affineLine K)),
    ((pointTateIso K h2 E x n).app A).toLinearEquiv.conj
      ((F.frobenius E).app ((U.pull x).obj ((O.lineTate K h2 n).obj A))).hom =
    (Fintype.card E : ℂ)^(-n) • ((F.frobenius E).app ((U.pull x).obj A)).hom
  originTate : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (z : ℤ),
    O.tate K h2 z ⋙ M.origin K ≅ M.origin K
  infinityTate : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (z : ℤ),
    O.tate K h2 z ⋙ M.infinity K ≅ M.infinity K
  rawKatzOrigin : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    PrimitiveRamificationFromGeneralKatzTheory.wildTrivial (M.wildOrigin K)
      ((M.origin K).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0)))
  rawKatzInfinity : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    Module.finrank Coefficient ((M.infinity K).obj
      (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))) = n ∧
    (M.profile K (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))).multiplicity 0 = 0 ∧
    (M.profile K (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))).swan = 1
  smoothOriginUnramified : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)), L (StartingSourceMaps.affineLine K) A →
    PrimitiveRamificationFromGeneralKatzTheory.wildTrivial (M.wildOrigin K)
      ((M.origin K).obj ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A))
  standardASInfinity : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient), ψ ≠ 1 →
    Module.finrank Coefficient ((M.infinity K).obj
      ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj (O.artinSchreier K h2 ψ))) = 1 ∧
    (M.profile K ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj
      (O.artinSchreier K h2 ψ))).swan = 1

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [∀ X, (L X).IsClosedUnderIsomorphisms]

/-- The exact endpoint geometry, with intrinsic generic rank and actual stalk purity. -/
def canonicalGeometry (p : ℕ) [Fact p.Prime] :=
  LinePurityFromStalks.geometry (pointStalks C U F p)
    (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p))

variable (T : GeneralPrimitiveLaws C U F O B G L M)
  (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)

include T B

/-- Original normalized canonical-character Kl3 eligibility is a derived output. -/
theorem computedKl3Properties :
    CanonicalCurveInput.Kl3Properties (canonicalGeometry C U F G L M p)
      (PublishedPrimitiveSources.Data.twistOne
        (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
          (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))
        (PublishedPrimitiveSources.Data.rawKl
          (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
            (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)))) := by
  let ψ := CanonicalSourceCharacter.prime p
  have hψ : ψ ≠ 1 := CanonicalSourceCharacter.prime_ne_one p
  change CanonicalCurveInput.Kl3Properties (canonicalGeometry C U F G L M p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ))
  have ht := GloballyLisseLineRamificationFromKatz.primitive_kl_tame C U L M O
    T.zeroRestriction T.unequalKatzLisse T.originTate T.rawKatzOrigin p h2 ψ hψ
  exact {
    lisse := ht.1
    rank := PrimitiveRanksFromComputedGenericLineRank.primitive_kl_rank C U G O
      T.zeroRestriction L T.ordinaryKatzRank T.ordinaryTateRank T.unequalKatzLisse p h2 ψ hψ
    pure := PrimitiveRankPurityFromGeneralKatzTheory.primitive_kl_pure C U F O B
      T.zeroRestriction T.rawKloostermanWeight T.pointTateIso T.pointTateFrobenius p h2 ψ hψ
    tame := ht
    breaks := GloballyLisseLineRamificationFromKatz.primitive_kl_breaks C U L M O
      T.zeroRestriction T.unequalKatzLisse T.infinityTate T.rawKatzInfinity p h2 ψ hψ }

omit [∀ (X : Scheme), (L X).IsClosedUnderIsomorphisms] in
/-- Original canonical-character AS eligibility is a derived output. -/
theorem computedASProperties :
    CanonicalCurveInput.ASProperties (canonicalGeometry C U F G L M p)
      (PublishedPrimitiveSources.Data.as
        (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
          (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))) := by
  let ψ := CanonicalSourceCharacter.prime p
  have hψ : ψ ≠ 1 := CanonicalSourceCharacter.prime_ne_one p
  change CanonicalCurveInput.ASProperties (canonicalGeometry C U F G L M p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ)
  have ht := GloballyLisseLineRamificationFromKatz.primitive_as_tame C U L M O
    T.lissePull T.standardASLisse T.smoothOriginUnramified p h2 ψ hψ
  exact {
    lisse := ht.1
    rank := PrimitiveRanksFromComputedGenericLineRank.primitive_as_rank C U G O L F B
      T.coefficientFormulas T.lisseGenericPointRank T.lissePull T.standardASLisse p h2 ψ hψ
    pure := PrimitiveRankPurityFromGeneralKatzTheory.primitive_as_pure C U F O B
      T.coefficientFormulas p h2 ψ hψ
    tame := ht
    slope := GloballyLisseLineRamificationFromKatz.primitive_as_isoclinic C U L M O
      T.lissePull T.standardASLisse T.standardASInfinity p h2 ψ hψ }

end PrimeGap182.TypeIII.CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05

#print axioms PrimeGap182.TypeIII.CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.computedKl3Properties
#print axioms PrimeGap182.TypeIII.CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.computedASProperties
