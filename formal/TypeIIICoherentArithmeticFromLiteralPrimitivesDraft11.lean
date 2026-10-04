import TypeIIICanonicalArithmeticRealization
import TypeIIIPrimitiveTracesFromGeneralKatzArtinSchreierFormulas
import TypeIIIArithmeticSourcesFromOrigin

/-!
# NEW computed arithmetic realization on literal common primitives

Use ONE all-schemes ordinary category/inverse-image system, ONE natural
finite-field Frobenius and ONE common Katz/AS/Tate construction record.
The (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)) point traces are computed from GENERAL all-rank/all-field
coefficient formulas. The normalized source trace is computed by the
GENERAL all-object Tate trace rule. Original three source origin models,
normalizations and invariant-line identities are computed from (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))
origin data through ALL-input arithmetic specialization, then inserted in
the existing original cohomological record.

No CohomologicalRealization, selected family trace/boundary model, common
normalized scalar, first/second source model or full Frobenius matrix is
an input. The GENERAL fiber/boundary/sign/inertia laws and (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))
origin/ramification facts still need a compatible genuine standard theory.
This is not a construction of adic foundations or completed Type III.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.CoherentArithmeticFromLiteralPrimitivesDraft11

open ExactInverseImagesToDerived UniversalOrdinaryInverseImages CanonicalPrimeFramework
open QSTPrimitiveBridgesFromCommonKatzConstruction RationalPointStalksFromUniversalFiber
open PublishedPhysicalConstruction PublishedPhaseApplication StartingSourceMaps
open StartingSourceComplexity GenericSourceSpecialization FourierSourcePullbacks
open CanonicalCurveInput CanonicalInputTrace BoundaryFromSourceModels RestrictionFrobenius
open ArithmeticBoundaryFromSources
open ArithmeticSourceMaps ArithmeticSourceTransport ArithmeticPrimitiveSources
open RegularUnipotentRepresentation

universe mu a b h

/- These GENERAL systems and theorem formulas are fixed before p.
The data must have their genuine standard adic interpretation; arbitrary
independent dictionaries do not establish the published premises. -/
variable (C : Scheme.{0} → Type)
  [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (U.pull f).Monoidal]
  (F : ArithmeticFibers C)
  [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)]
  (O : Constructions C)
  (B : PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.CoefficientFibers C F)
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _)
  (coefficientFormulas :
    PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.PublishedCoefficientFormulas C U F O B)

variable {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)


/- GENERAL trace law for EVERY line object and EVERY finite extension.
It is evaluated on the SAME rational Frobenius point system above. -/
variable (tateTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ (A : C (affineLine (ZMod p))) (z : E), ((pointStalks C U F p)).lineTrace (E := E) (((RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))).twistOne A) z =
      (Fintype.card E : ℂ)⁻¹ * ((pointStalks C U F p)).lineTrace (E := E) A z)

include B zeroRestriction coefficientFormulas tateTrace h2

omit [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)] in
/-- Raw all-rank theorem specialized to n=3, followed by the actual Tate
normalization. The field extension character uses the SAME Algebra.trace. -/
theorem literalNormalizedKlTrace
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (z : Eˣ) :
    ((pointStalks C U F p)).lineTrace (E := E) (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)))) (z : E) =
      FiniteFieldSums.kl3 (FiniteFieldSums.traceAddChar p E) (z : E) := by
  exact KatzSourceNormalization.normalized_kl_trace
    (FiniteFieldSums.traceAddChar p E) (((pointStalks C U F p)).lineTrace (E := E))
    ((RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))).twistOne (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)))
    (fun y => by
      simpa only [PublishedPrimitiveSources.complexCharacter_canonical] using
        PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.primitive_raw_trace
          C U F O B zeroRestriction coefficientFormulas p h2
          (CanonicalSourceCharacter.prime p) (CanonicalSourceCharacter.prime_ne_one p) E y)
    (tateTrace E) z

omit [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)]
  zeroRestriction tateTrace in
/-- AS rank-one Frobenius formula evaluated at ALL (pointStalks C U F p), including zero. -/
theorem literalASTrace
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (z : E) :
    ((pointStalks C U F p)).lineTrace (E := E) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))) z = FiniteFieldSums.traceAddChar p E z := by
  have ht := PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.primitive_as_trace
    C U F O B coefficientFormulas p h2 (CanonicalSourceCharacter.prime p)
    (CanonicalSourceCharacter.prime_ne_one p) E z
  change _ = PublishedPrimitiveSources.complexCharacter p
    (CanonicalSourceCharacter.prime p) E z at ht
  simpa only [PublishedPrimitiveSources.complexCharacter_canonical] using ht

variable {Point : Type h}
  {D : CurveData (((primeSource C U p)).Obj .source) Point}
  {H : CohomologyData (((primeSource C U p)).Obj .source) (((primeSource C U p)).Obj .torus)}
  {PP : ParameterData (((primeSource C U p)).Obj .torus)}
  (LG : LineGeometry (((primeSource C U p)).Obj .line)) (SR : ScalarPullbackRules (originalPullbackData (ZMod p)
  (SourceInverseImageSystem.System.geometricPullbacks (primeSource C U p))) LG D)
  (hkl : Kl3Properties LG (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))))) (has : ASProperties LG (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)))) (CR : CurveRules D)
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (tame : G0 →* Multiplicative ℂ) (htame : ∃ g, (tame g).toAdd ≠ 0)


/- The geometric parameter point is part of the genuine family eligibility.
Its trace uses the actual pointStalks curve point, not an independent trace. -/
variable
  (point : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], Eˣ → Eˣ → Point)
  (VR : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, CurveFiberRules D H (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p))).fiber E x y) (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p))).frobenius E x y) E
      (((pointStalks C U F p)).curveTraceData (E := E) D (point E x y) x y))
  (BS : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, BoundarySequence D H (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p))).fiber E x y))
  (AZ : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, RestrictionData (G0 := G0) (Ginf := Ginf) D H (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p))).fiber E x y) (BS E x y))
  (AP : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, ArithmeticRestriction (AZ E x y))
  (AB : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, ArithmeticBoundary (AZ E x y) (AP E x y) (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p))).frobenius E x y))
  (inertiaConjugation : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ _x _y : Eˣ, G0 →* G0)
  (tameFrobenius : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, ∀ g, (tame (inertiaConjugation E x y g)).toAdd =
      (Fintype.card E : ℂ)⁻¹ * (tame g).toAdd)
  (inertiaCovariance : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, ∀ A g v,
      (AP E x y).zeroFr A (((AZ E x y).zero A).ρ g v) =
        ((AZ E x y).zero A).ρ (inertiaConjugation E x y g) ((AP E x y).zeroFr A v))

/- These are the general arithmetic local functors on the SAME source
system, at every finite extension. The origin inputs concern only literal
(PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))) Kl/AS primitives and GENERAL scalar/Tate origin comparisons. Their
(PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)))/AS identity actions must be derived from GENERAL Katz/AS theorems;
no finished correlation or normalized action is an input. -/
variable
  (J0 : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ((primeSource C U p)).arithmeticCategory E ⥤ FDRep ℂ G0)
  (LF0 : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    LocalFrobenius (J0 E))
  (originInputs : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ArithmeticSourcesFromOrigin.Inputs (ZMod p) E
      (((primeSource C U p)).arithmeticPullbacks E) (J0 E) (LF0 E) ((RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))).twistOne (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))) tame)
  (specialization : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ,
      SpecializationComparison (J0 E)
        ((((primeSource C U p)).arithmeticPullbacks E).along (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y))
        (AZ E x y).zero (AP E x y).zeroFr (LF0 E))
  (sign : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ∀ x y : Eˣ, SignStalkComparison PP (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p))).fiber E x y) (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p))).frobenius E x y)
      (Module.finrank (ZMod p) E))

include C U F O B zeroRestriction coefficientFormulas h2 tateTrace LG SR hkl has CR
  tame htame point VR BS AZ AP AB inertiaConjugation tameFrobenius inertiaCovariance
  J0 LF0 originInputs specialization sign

/-- The original whole arithmetic cohomological record is COMPUTED.
No complete record, normalized trace/common scalar, selected source origin
models, invariant-line identities or corrected family trace is supplied. -/
def literalCohomologicalRealization : CohomologicalRealization D H PP (canonicalInput (originalPullbackData (ZMod p)
  (SourceInverseImageSystem.System.geometricPullbacks (primeSource C U p))) LG SR (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)))) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))) hkl has) (RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)) :=
  CanonicalArithmeticRealization.cohomologicalRealization (originalPullbackData (ZMod p)
  (SourceInverseImageSystem.System.geometricPullbacks (primeSource C U p))) LG SR (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)))) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2))) hkl has CR (RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)) tame htame
    (fun E _ _ _ x y => by
      change (U.pull (PhysicalTorusMorphism.schemePoint (K := ZMod p) x y) ⋙ F.fiber E).Additive
      infer_instance)
    (fun E _ _ _ x y => by
      change PreservesFiniteLimits
        (U.pull (PhysicalTorusMorphism.schemePoint (K := ZMod p) x y) ⋙ F.fiber E)
      infer_instance)
    (fun E _ _ _ x y => by
      change PreservesFiniteColimits
        (U.pull (PhysicalTorusMorphism.schemePoint (K := ZMod p) x y) ⋙ F.fiber E)
      infer_instance)
    (((pointStalks C U F p)).curveTraceFamily D point) VR
    (fun E _ _ _ _x _y => ((pointStalks C U F p)).lineTrace (E := E))
    (fun E _ _ _ x y => ((pointStalks C U F p)).curvePullback (E := E) D (point E x y) x y)
    (fun E _ _ _ _x _y z => literalNormalizedKlTrace C U F O B zeroRestriction
      coefficientFormulas h2 tateTrace E z)
    (fun E _ _ _ _x _y z => literalASTrace C U F O B
      coefficientFormulas h2 E z)
    BS AZ AP AB inertiaConjugation tameFrobenius inertiaCovariance
    (fun E _ _ _ x y => (originInputs E).primitiveSources.firstZero
      (AZ E x y).zero (AP E x y).zeroFr x y (specialization E x y))
    (fun E _ _ _ x y => (originInputs E).primitiveSources.secondZero
      (AZ E x y).zero (AP E x y).zeroFr x y (specialization E x y))
    (fun E _ _ _ x y => (originInputs E).primitiveSources.additiveZero
      (AZ E x y).zero (AP E x y).zeroFr x y (specialization E x y))
    (fun E _ _ _ x y => (originInputs E).primitiveSources.additiveNatural
      (AZ E x y).zero (AP E x y).zeroFr x y (specialization E x y))
    (fun E _ _ _ _x _y => (originInputs E).primitiveSources.scalar)
    (fun E _ _ _ _x _y => (originInputs E).primitiveSources.scalar_ne_zero)
    (fun E _ _ _ x y => (originInputs E).primitiveSources.firstInvariantLine
      (AZ E x y).zero (AP E x y).zeroFr x y (specialization E x y))
    (fun E _ _ _ x y => (originInputs E).primitiveSources.secondInvariantLine
      (AZ E x y).zero (AP E x y).zeroFr x y (specialization E x y))
    sign

omit [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)]
  zeroRestriction coefficientFormulas tateTrace SR hkl has CR htame VR AB
  tameFrobenius inertiaCovariance specialization sign
  B LG point AP inertiaConjugation BS AZ in
/-- The shared invariant-line normalization is FIXED, not supplied. -/
theorem literalPrimitiveCommonScalar
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    (originInputs E).primitiveSources.scalar = (Fintype.card E : ℂ)⁻¹ := rfl

end PrimeGap182.TypeIII.CoherentArithmeticFromLiteralPrimitivesDraft11

#print axioms PrimeGap182.TypeIII.CoherentArithmeticFromLiteralPrimitivesDraft11.literalNormalizedKlTrace
#print axioms PrimeGap182.TypeIII.CoherentArithmeticFromLiteralPrimitivesDraft11.literalASTrace
#print axioms PrimeGap182.TypeIII.CoherentArithmeticFromLiteralPrimitivesDraft11.literalCohomologicalRealization
#print axioms PrimeGap182.TypeIII.CoherentArithmeticFromLiteralPrimitivesDraft11.literalPrimitiveCommonScalar
