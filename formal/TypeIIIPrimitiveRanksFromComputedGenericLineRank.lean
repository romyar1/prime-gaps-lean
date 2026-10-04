import TypeIIIPrimitiveRankPurityFromGeneralKatzTheory

/-!
# Primitive ranks for the computed ordinary generic line rank

Line rank is DEFINED from SAME-U restriction to the actual Gm open and
the existing actual fraction-field generic point, ordinary H0, and SAME
ALL-field geometric coefficient fiber G. No chosen lineRank or rank
recognition premise is supplied. Actual functorial isomorphism transport
proves its invariance.

General raw Katz and ALL-integer ordinary Tate ranks are reused. The sole
additional rank comparison is general finite-rank lisse rank constancy on
connected Gm: SAME geometric generic fiber and SAME finite arithmetic point
fiber have equal dimension at EVERY finite-extension unit point. It concerns
ALL globally lisse ordinary Gm objects, before any primitive/prime selection;
it is not an equality for an arbitrary chosen numerical rank function.
AS rank one follows from the already supplied ALL-family coefficient basis
and actual scalar extension. Kl3 uses SAME zeroRestriction and Tate recipe.

The lisse/continuous coefficient interpretations of L,G,F remain external.
The complete compatible model is not constructed. Primary rank references:
Katz ESDE8.4.2(6–8), GKM4.1.1(1)/4.3; Katz Four Lectures on Weil II,
pp.3–4 (lisse rank is representation dimension), and Stacks17.26 rank
constancy for finite locally free modules. No adic reconstruction is added.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.PrimitiveRanksFromComputedGenericLineRank
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward
open QSTGenericFiberFromActualGenericPoint QSTPrimitiveBridgesFromCommonKatzConstruction
open RationalPointStalksFromUniversalFiber PrimitiveTracesFromGeneralKatzArtinSchreierFormulas

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- Intrinsic generic rank of the SAME ordinary line object restricted to Gm. -/
def canonicalLineRank (K : Type) [Field K]
    (A : C (StartingSourceMaps.affineLine K)) : ℕ :=
  Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj
    ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)))

/-- Actual isomorphisms preserve the computed generic rank, without a lissity guard. -/
theorem canonicalLineRank_iso (K : Type) [Field K]
    {A B : C (StartingSourceMaps.affineLine K)} (e : A ≅ B) :
    canonicalLineRank C U G K A = canonicalLineRank C U G K B :=
  ((rawGenericFiber K C U G).mapIso ((boundedDegreeZero C _).mapIso
    ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).mapIso e))).toLinearEquiv.finrank_eq

variable (O : Constructions C)
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (ordinaryKatzRank : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K), Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((boundedDegreeZero C _).obj (O.katz K h2 { a with tateTwist := 0 }))) = a.rank)
  (ordinaryTateRank : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (n : ℤ) (A : C (ArithmeticSourceMaps.fiberScheme K)),
    Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((boundedDegreeZero C _).obj ((O.tate K h2 n).obj A))) =
    Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A)))
  (unequalKatzLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K), a.upper.length ≠ a.lower.length →
      L (ArithmeticSourceMaps.fiberScheme K) (member C O K h2 a))

include zeroRestriction ordinaryKatzRank ordinaryTateRank unequalKatzLisse in
/-- ALL normalized Kl3 objects have computed rank three; recognition is definitional. -/
theorem normalized_kloosterman_rank (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) :
    canonicalLineRank C U G K
      ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) = 3 :=
  PrimitiveRankPurityFromGeneralKatzTheory.normalized_kloosterman_rank C U O zeroRestriction
    G L (canonicalLineRank C U G) (fun _ _ _ _ _ _ => rfl)
    ordinaryKatzRank ordinaryTateRank unequalKatzLisse K h2 ψ hψ

include zeroRestriction ordinaryKatzRank ordinaryTateRank unequalKatzLisse in
/-- Exact original primitive rank on the computed line-rank model. -/
theorem primitive_kl_rank (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1) :
    canonicalLineRank C U G (ZMod p)
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
        ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ)) = 3 :=
  PrimitiveRankPurityFromGeneralKatzTheory.primitive_kl_rank C U O zeroRestriction
    G L (canonicalLineRank C U G) (fun _ _ _ _ _ _ => rfl)
    ordinaryKatzRank ordinaryTateRank unequalKatzLisse p h2 ψ hψ

variable (F : ArithmeticFibers C) (B : CoefficientFibers C F)
  (T : PublishedCoefficientFormulas C U F O B)
  (lisseGenericPointRank : ∀ (K : Type) [Field K] [Fintype K]
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
      Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A)) =
      Module.finrank ℂ ((F.fiber E).obj ((U.pull (gmPoint K E x)).obj A)))
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient), ψ ≠ 1 → L (StartingSourceMaps.affineLine K) (O.artinSchreier K h2 ψ))

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
include T lisseGenericPointRank lissePull standardASLisse in
/-- ALL AS ranks follow from the existing coefficient basis and general lisse constancy. -/
theorem artinSchreier_rank (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) :
    canonicalLineRank C U G K (O.artinSchreier K h2 ψ) = 1 :=
  PrimitiveRankPurityFromGeneralKatzTheory.artinSchreier_rank C U F O B T G L
    (canonicalLineRank C U G) (fun _ _ _ _ _ _ => rfl)
    lisseGenericPointRank lissePull standardASLisse K h2 ψ hψ

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
include T lisseGenericPointRank lissePull standardASLisse in
/-- Exact original primitive AS rank for the computed line-rank model. -/
theorem primitive_as_rank (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1) :
    canonicalLineRank C U G (ZMod p)
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ) = 1 :=
  PrimitiveRankPurityFromGeneralKatzTheory.primitive_as_rank C U F O B T G L
    (canonicalLineRank C U G) (fun _ _ _ _ _ _ => rfl)
    lisseGenericPointRank lissePull standardASLisse p h2 ψ hψ

end PrimeGap182.TypeIII.PrimitiveRanksFromComputedGenericLineRank
