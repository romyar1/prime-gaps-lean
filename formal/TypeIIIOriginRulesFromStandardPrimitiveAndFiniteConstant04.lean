import TypeIIIPrimeOriginFromStandardKloostermanLang06
import TypeIIIOriginFiniteConstantFromCurveRealization05

/-! The EXACT original PublishedOriginFrobenius.Rules is computed from two
separate GENERAL standard theorem packages and individual native operations.
No Rules/BaseChange/OriginStalks provider is a premise. The origin family is
the computed invariantStalks32, or its computed common-group relabeling.

Standard continuous-adic interpretation, finite-constant curve-pull NatIso,
and individual rawKl3/AS curve-object Iso recognition remain external. Scalar
restriction, Tate, ordinary j_* interpretation and the complete StalkData or
current TypeIII constructor are not constructed by this leaf. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.OriginRulesFromStandardPrimitiveAndFiniteConstant
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open OriginStalksFromStandardWeilInvariants PrimeOriginFromStandardKloostermanLang
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open ArithmeticSourceMaps StartingSourceMaps
universe nu mu g

/-- The original p>3 numerical guard supplies two-invertibility. -/
theorem prime_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2)
    (lt_trans (by decide : 2 < 3) hp)) ((ZMod.natCast_eq_zero_iff 2 p).mp h)

/-- SAME original Algebra (ZMod p) E transports the guard; no replacement
CharP/algebra instance or finite-field choice is installed. -/
theorem extension_two_ne_zero (p : ℕ) [Fact p.Prime] (h2p : (2 : ZMod p) ≠ 0)
    (E : Type) [Field E] [Algebra (ZMod p) E] : (2 : E) ≠ 0 := by
  intro h
  apply h2p
  apply (algebraMap (ZMod p) E).injective
  simpa only [map_ofNat, map_zero] using h

variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (fiberScheme E) ⥤ C (Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (D : FaithfulArithmeticOperations C U F nativeCompact S)

variable (P : StandardKloostermanLangOrigin.Operations S B)
  {primitiveInterpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardKloostermanLangOrigin.Operations S B → Prop}
  (primitiveTheorems : StandardKloostermanLangOrigin.PublishedTheorems primitiveInterpretation)
  (primitiveModel : primitiveInterpretation S B P)
  (X : StandardFiniteConstantOrigin.Operations S B)
  {constantInterpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardFiniteConstantOrigin.Operations S B → Prop}
  (constantTheorems : StandardFiniteConstantOrigin.PublishedTheorems constantInterpretation)
  (constantModel : constantInterpretation S B X)
  (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)

variable  (p : ℕ) [Fact p.Prime]
  (h2 : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], (2 : E) ≠ 0)

/-- Exact computed original family, with each original finite-field guard. -/
def originFamily (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    ArithmeticSourcesFromOrigin.OriginStalks.{0,0} (C (affineLine (ZMod p))) :=
  originStalks C U F nativeCompact B D (ZMod p) E (h2 E)

variable
  (curveComparison : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    U.pull (OriginFiniteConstantInvariantFrobeniusTransport.constantExtensionMorphism (ZMod p) E) ⋙
      D.curveRealization E (h2 E) ≅
    D.curveRealization (ZMod p) (h2 (ZMod p)) ⋙ X.curvePull (ZMod p) E (h2 (ZMod p)) (h2 E))
  (primitive : PublishedPrimitiveSources.Data p (C (affineLine (ZMod p))))
  (rawComparison : ∀ (psi : AddChar (ZMod p) (PadicAlgCl 2)), psi ≠ 1 →
    ((D.curveRealization (ZMod p) (h2 (ZMod p))).obj
      ((U.pull (localInputMorphism (ZMod p) (ZMod p))).obj (primitive.kloosterman3 psi)) ≅
      P.rawKloosterman (ZMod p) (h2 (ZMod p)) 3 psi))
  (asComparison : ∀ (psi : AddChar (ZMod p) (PadicAlgCl 2)), psi ≠ 1 →
    ((D.curveRealization (ZMod p) (h2 (ZMod p))).obj
      ((U.pull (localInputMorphism (ZMod p) (ZMod p))).obj (primitive.artinSchreier psi)) ≅
      (P.restriction (ZMod p) (h2 (ZMod p))).obj
        (P.langAS (ZMod p) (h2 (ZMod p)) psi)))

/-- All four original fields are computed; neither a BaseChange nor Rules
record is an input. The native ALL-Weil square is derived in finite93. -/
def originRules : PublishedOriginFrobenius.Rules primitive
    (originFamily C U F nativeCompact B D p h2) where
  comparison E _ _ _ A := OriginFiniteConstantFromCurveRealization.sourceInvariantComparison
    C U F nativeCompact B D X constantTheorems constantModel (ZMod p) E
    (h2 (ZMod p)) (h2 E) (curveComparison E) A
  frobenius E _ _ _ A x := OriginFiniteConstantFromCurveRealization.source_frobenius_square
    C U F nativeCompact B D X constantTheorems constantModel (ZMod p) E
    (h2 (ZMod p)) (h2 E) (curveComparison E) A x
  raw _hp psi hpsi := PrimeOriginFromStandardKloostermanLang.prime_raw
    C U F nativeCompact B D P primitiveTheorems primitiveModel p primitive
    (h2 (ZMod p)) psi hpsi (rawComparison psi hpsi)
  artinSchreier _hp psi hpsi := PrimeOriginFromStandardKloostermanLang.prime_artinSchreier
    C U F nativeCompact B D P primitiveTheorems primitiveModel p primitive
    (h2 (ZMod p)) psi (asComparison psi hpsi)


/-- The SAME chosen common native group; arbitrary group universe g. -/
def commonOriginFamily (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    ArithmeticSourcesFromOrigin.OriginStalks.{0,0} (C (affineLine (ZMod p))) :=
  OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
    C U F nativeCompact B D originTrait (ZMod p) E (h2 E)

/-- Computed full original record on the common cone, using SAME-field
invariant comparisons and actual finite-constant degree, without NF data. -/
def commonOriginRules : PublishedOriginFrobenius.Rules primitive
    (commonOriginFamily.{nu,mu,g} C U F nativeCompact B D originTrait p h2) where
  comparison E _ _ _ A := OriginFiniteConstantFromCurveRealization.commonSourceComparison.{nu,mu,g}
    C U F nativeCompact B D X constantTheorems constantModel (ZMod p) E
    (h2 (ZMod p)) (h2 E) (curveComparison E) originTrait A
  frobenius E _ _ _ A x := OriginFiniteConstantFromCurveRealization.commonSource_frobenius_square.{nu,mu,g}
    C U F nativeCompact B D X constantTheorems constantModel (ZMod p) E
    (h2 (ZMod p)) (h2 E) (curveComparison E) originTrait A x
  raw _hp psi hpsi := by
    ext x
    exact PrimeOriginFromStandardKloostermanLang.common_raw_frobenius.{nu,mu,g}
      C U F nativeCompact B D (ZMod p) (h2 (ZMod p)) P primitiveTheorems primitiveModel
      originTrait (primitive.kloosterman3 psi) psi hpsi (rawComparison psi hpsi) x
  artinSchreier _hp psi hpsi := by
    ext x
    exact PrimeOriginFromStandardKloostermanLang.common_artinSchreier_frobenius.{nu,mu,g}
      C U F nativeCompact B D (ZMod p) (h2 (ZMod p)) P primitiveTheorems primitiveModel
      originTrait (primitive.artinSchreier psi) psi (asComparison psi hpsi) x

end PrimeGap182.TypeIII.OriginRulesFromStandardPrimitiveAndFiniteConstant
