import TypeIIISourceGlobalLissityFromKatzPullbacks

/-!
# Exact original geometric rules from the SAME global lissity predicate

The line guard is global lissity of the actual Gm restriction under U.
The source guard is global lissity on the whole original source scheme.
ALL-scheme inverse-image, tensor and internal-Hom-dual closure compute
three original lissity clauses. The four scalar local clauses and ten
source local/rank clauses remain explicit, separately typed hypotheses;
no completed geometric-rules record is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.SourceGeometricRulesFromGlobalLissity
open ExactInverseImagesToDerived SourceGlobalLissityFromKatzPullbacks

universe mu pt
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalClosed (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (L : ∀ X : Scheme, ObjectProperty (C X))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    L Y A → L X ((U.pull f).obj A))
  (lisseTensor : ∀ X (A B : C X), L X A → L X B → L X (A ⊗ B))
  (lisseDual : ∀ X (A : C X), L X A →
    L X ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C X).obj (Opposite.op A)))
  (p : ℕ) [Fact p.Prime]
  {Point : Type pt}

/-- Six source numeric/local observables are retained; the source lissity
predicate is global on the actual source, rather than relative to a fiber. -/
def sourceObservables (S : SourcePurityFromStalks.Observables
    (C (StartingSourceMaps.sourceScheme (ZMod p))) Point) :
    SourcePurityFromStalks.Observables (C (StartingSourceMaps.sourceScheme (ZMod p))) Point :=
  { S with Lisse := L (StartingSourceMaps.sourceScheme (ZMod p)) }

variable (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))
  (S : SourcePurityFromStalks.Observables (C (StartingSourceMaps.sourceScheme (ZMod p))) Point)
  (O : LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine (ZMod p))))

/-- Original curve data, with categorical tensor and the SAME ordinary dual. -/
def curveData :=
  (SourcePurityFromStalks.geometry R (sourceObservables C L p S)).curveData
    (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _)

/-- Exact original line geometry with the SAME-U global restriction guard. -/
def lineGeometry :=
  LinePurityFromStalks.geometry R (bindLineLisseOnUnits (ZMod p) C U L O)

/-- Exact original scalar-pullback data from the SAME ordinary inverse images. -/
def scalarPullbacks := FourierSourcePullbacks.originalPullbackData (ZMod p)
  (CanonicalPrimeFramework.primeSource C U p).geometricPullbacks

include lissePull in
/-- Only the four local scalar clauses remain arguments. The original lisse
clause is proved for ALL parameter-ring units by the genuine scheme factor. -/
theorem scalarConstructor
    (rank : ∀ c A, (lineGeometry C U L p R O).LisseOnUnits A →
      (curveData C U L p R S).rank
        ((scalarPullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A) =
      (lineGeometry C U L p R O).rank A)
    (tame : ∀ c A, (lineGeometry C U L p R O).TameZero A →
      (curveData C U L p R S).TameZero
        ((scalarPullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A))
    (breaks : ∀ c A s, (lineGeometry C U L p R O).BreaksLE A s →
      (curveData C U L p R S).BreaksLE
        ((scalarPullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A) s)
    (isoclinic : ∀ c A s, (lineGeometry C U L p R O).Isoclinic A s →
      (curveData C U L p R S).Isoclinic
        ((scalarPullbacks C U p).pullback (CanonicalCurveInput.scalarMorphism (ZMod p) c) A) s) :
    LinePurityFromStalks.GeometricPullbackRules (scalarPullbacks C U p)
      (lineGeometry C U L p R O) (curveData C U L p R S) where
  lisse := scalar_lisse (ZMod p) C U L lissePull
  rank := rank
  tame := tame
  breaks := breaks
  isoclinic := isoclinic

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
include lisseTensor lisseDual in
/-- Only the ten rank/local source clauses remain arguments. Tensor and dual
lissity are applications of the ALL-scheme laws to the exact source category. -/
theorem sourceConstructor
    (tensorRank : ∀ A B, (curveData C U L p R S).Lisse A →
      (curveData C U L p R S).Lisse B →
      (curveData C U L p R S).rank ((curveData C U L p R S).tensor A B) =
        (curveData C U L p R S).rank A * (curveData C U L p R S).rank B)
    (dualRank : ∀ A, (curveData C U L p R S).Lisse A →
      (curveData C U L p R S).rank ((curveData C U L p R S).dual A) =
        (curveData C U L p R S).rank A)
    (tensorTame : ∀ A B, (curveData C U L p R S).TameZero A →
      (curveData C U L p R S).TameZero B →
      (curveData C U L p R S).TameZero ((curveData C U L p R S).tensor A B))
    (dualTame : ∀ A, (curveData C U L p R S).TameZero A →
      (curveData C U L p R S).TameZero ((curveData C U L p R S).dual A))
    (tensorBreaks : ∀ A B r, (curveData C U L p R S).BreaksLE A r →
      (curveData C U L p R S).BreaksLE B r →
      (curveData C U L p R S).BreaksLE ((curveData C U L p R S).tensor A B) r)
    (dualBreaks : ∀ A r, (curveData C U L p R S).BreaksLE A r →
      (curveData C U L p R S).BreaksLE ((curveData C U L p R S).dual A) r)
    (unequalBreaks : ∀ A B r s, r < s → (curveData C U L p R S).BreaksLE A r →
      (curveData C U L p R S).Isoclinic B s →
      (curveData C U L p R S).Isoclinic ((curveData C U L p R S).tensor A B) s)
    (dualIsoclinic : ∀ A r, (curveData C U L p R S).Isoclinic A r →
      (curveData C U L p R S).Isoclinic ((curveData C U L p R S).dual A) r)
    (tameSwan : ∀ A, (curveData C U L p R S).TameZero A →
      ∀ t, (curveData C U L p R S).swanZero A t = 0)
    (slopeOneSwan : ∀ A, (curveData C U L p R S).Isoclinic A 1 →
      ∀ t, (curveData C U L p R S).swanInfinity A t = (curveData C U L p R S).rank A) :
    SourcePurityFromStalks.GeometricRules (curveData C U L p R S) where
  tensor_lisse := lisseTensor _
  tensor_rank := tensorRank
  dual_lisse := lisseDual _
  dual_rank := dualRank
  tensor_tame := tensorTame
  dual_tame := dualTame
  tensor_breaks := tensorBreaks
  dual_breaks := dualBreaks
  tensor_unequal_breaks := unequalBreaks
  dual_isoclinic := dualIsoclinic
  tame_swan := tameSwan
  slope_one_swan := slopeOneSwan

end PrimeGap182.TypeIII.SourceGeometricRulesFromGlobalLissity
