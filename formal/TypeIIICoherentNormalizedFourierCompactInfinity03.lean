import TypeIIICoherentCurveNormalizationFiniteOrigin03
import TypeIIITensorListRepresentation

/-!
# SAME standard normalized finite-origin/Fourier/compact/infinity diagrams

The perverse finite-origin source is computed from ONE standard derived
Fourier and generic-cohomology recipe. Its origin and infinity are literal
functor views, not separately supplied family comparisons.

GENERAL curve torsion-quotient/truncation and cohomology laws yield both
normalized diagrams for every ordinary constructible object. They use no
exactness of perverse normalization or of intermediate extension.
The genuine continuous-adic interpretation of the general projections
remains external; no coherent model or Type III conclusion is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03

open PublishedLocalConstruction PublishedPhaseApplication CanonicalLocalCorrelation
open CoherentCurveNormalizationFiniteOrigin03 TensorListRepresentation

universe u v w z a b c d e f g h
variable {K : Type u} [Field K] {E : Type v} [Field E]
  {I : Type w} [Group I] {Outer : Type z} [Group Outer]
  {Ord : Type a} [Category.{b} Ord]
  {Perv : Type c} [Category.{d} Perv]
  {Derived : Type e} [Category.{f} Derived]
  {LF : LocalFourierData K E I Outer}

/-- One standard perverse construction recipe. `radialFourier` is the
SAME Fourier operation followed by the literal nonzero radial pullback;
`originGenericMinusOne` and `infinityGenericMinusOne` are actual derived
generic degree-minus-one restrictions. `closedPointZero` is the matching
closed-point degree-zero view, with its unramified action inflated.
The natural vanishing-cycle maps are GENERAL standard constructions. -/
structure StandardFiniteOriginOperations (underlying : Perv ⥤ Derived) where
  infinityGenericMinusOne : Derived ⥤ FDRep E I
  radialFourier : (s : PhaseField K) → s ≠ 0 → Derived ⥤ Derived
  originGenericMinusOne : Derived ⥤ FDRep E Outer
  closedPointZero : (s : PhaseField K) → s ≠ 0 → Derived ⥤ FDRep E Outer
  infinity_admissible : ∀ A, LF.Admissible
    (infinityGenericMinusOne.obj (underlying.obj A))
  toVanishing : ∀ (s : PhaseField K) (hs : s ≠ 0) A,
    Representation.IntertwiningMap
      (originGenericMinusOne.obj ((radialFourier s hs).obj (underlying.obj A))).ρ
      ((LF.operation s hs).obj
        (infinityGenericMinusOne.obj (underlying.obj A))
        (infinity_admissible A)).ρ
  toBoundary : ∀ (s : PhaseField K) (hs : s ≠ 0) A,
    Representation.IntertwiningMap
      ((LF.operation s hs).obj
        (infinityGenericMinusOne.obj (underlying.obj A))
        (infinity_admissible A)).ρ
      ((closedPointZero s hs).obj (underlying.obj A)).ρ

/-- All fields of the perverse package use the literal SAME recipe. -/
def StandardFiniteOriginOperations.perverseData
    {underlying : Perv ⥤ Derived} (S : StandardFiniteOriginOperations (LF := LF) underlying) :
    FiniteOriginData Perv LF where
  infinity A := S.infinityGenericMinusOne.obj (underlying.obj A)
  infinity_admissible A := S.infinity_admissible A
  origin s hs A := S.originGenericMinusOne.obj ((S.radialFourier s hs).obj (underlying.obj A))
  boundary s hs A := (S.closedPointZero s hs).obj (underlying.obj A)
  toVanishing s hs A := S.toVanishing s hs A
  toBoundary s hs A := S.toBoundary s hs A

/-- The canonical punctual-torsion quotient and GENERAL curve
truncation comparison. For constructible ordinary A, quotient(A)=A/T(A),
where T(A) is its maximal punctual subsheaf. `normalize` is pH0(A[1]);
this comparison follows from the torsion triangle and the curve criterion.
No exactness of normalize or of quotient is supplied. -/
structure CurveNormalizationOperations (underlying : Perv ⥤ Derived) where
  normalize : Ord ⥤ Perv
  quotient : Ord ⥤ Ord
  quotientMap : 𝟭 Ord ⟶ quotient
  shiftOne : Ord ⥤ Derived
  quotientComparison : normalize ⋙ underlying ≅ quotient ⋙ shiftOne

/-- GENERAL Fourier-fiber and punctual-torsion cohomology corollaries,
for ALL ordinary curve objects and ALL nonzero radial scales. Positive
compact degrees of punctual torsion vanish, so the actual quotient map
induces the compactDegreeOne and infinity quotient isomorphisms.
These must be projections of ONE genuine standard theory; none refers to
a selected Kl source/correlation, rank, profile, or norm bound. -/
structure GeneralCurveFiberRules {underlying : Perv ⥤ Derived}
    (N : CurveNormalizationOperations (Ord := Ord) underlying)
    (S : StandardFiniteOriginOperations (LF := LF) underlying) where
  compactDegreeOne : (s : PhaseField K) → s ≠ 0 → Ord ⥤ FDRep E Outer
  ordinaryInfinity : Ord ⥤ FDRep E I
  fourierFiber : ∀ (s : PhaseField K) (hs : s ≠ 0),
    (N.shiftOne ⋙ S.radialFourier s hs) ⋙ S.originGenericMinusOne ≅ compactDegreeOne s hs
  compactQuotientIsIso : ∀ (s : PhaseField K) (hs : s ≠ 0) A,
    IsIso ((compactDegreeOne s hs).map (N.quotientMap.app A))
  infinityFiber : N.shiftOne ⋙ S.infinityGenericMinusOne ≅ ordinaryInfinity
  infinityQuotientIsIso : ∀ A, IsIso (ordinaryInfinity.map (N.quotientMap.app A))

/-- The ordinary-indexed package is evaluated at the computed normalized
object, and keeps the SAME perverse maps. -/
def normalizedData {underlying : Perv ⥤ Derived}
    (N : CurveNormalizationOperations (Ord := Ord) underlying)
    (S : StandardFiniteOriginOperations (LF := LF) underlying) : FiniteOriginData Ord LF :=
  normalizedFiniteOriginData N.normalize S.perverseData

/-- GENERAL perverse finite-origin laws transport by literal evaluation. -/
theorem normalizedRules (p : ℕ) [Fact p.Prime] [CharP K p]
    {underlying : Perv ⥤ Derived}
    (N : CurveNormalizationOperations (Ord := Ord) underlying)
    (S : StandardFiniteOriginOperations (LF := LF) underlying)
    (perverseRules : FiniteOriginRules p S.perverseData) :
    FiniteOriginRules p (normalizedData N S) :=
  normalizedFiniteOriginRules p N.normalize S.perverseData perverseRules

/-- Compose actual normalization, derived Fourier/generic restriction,
GENERAL fiber formula, and inverse compact quotient map. No normalized
origin/compact comparison itself is an input. -/
def normalizedOriginCompactIso {underlying : Perv ⥤ Derived}
    (N : CurveNormalizationOperations (Ord := Ord) underlying)
    (S : StandardFiniteOriginOperations (LF := LF) underlying)
    (R : GeneralCurveFiberRules N S)
    (s : PhaseField K) (hs : s ≠ 0) (A : Ord) :
    (normalizedData N S).origin s hs A ≅ (R.compactDegreeOne s hs).obj A := by
  letI := R.compactQuotientIsIso s hs A
  exact ((S.radialFourier s hs ⋙ S.originGenericMinusOne).mapIso
      (N.quotientComparison.app A)) ≪≫
    (R.fourierFiber s hs).app (N.quotient.obj A) ≪≫
    (asIso ((R.compactDegreeOne s hs).map (N.quotientMap.app A))).symm

/-- Generic restriction kills punctual torsion; compose that actual
quotient comparison with the SAME normalization and infinity functors. -/
def normalizedInfinityIso {underlying : Perv ⥤ Derived}
    (N : CurveNormalizationOperations (Ord := Ord) underlying)
    (S : StandardFiniteOriginOperations (LF := LF) underlying)
    (R : GeneralCurveFiberRules N S) (A : Ord) :
    (normalizedData N S).infinity A ≅ R.ordinaryInfinity.obj A := by
  letI := R.infinityQuotientIsIso A
  exact S.infinityGenericMinusOne.mapIso (N.quotientComparison.app A) ≪≫
    R.infinityFiber.app (N.quotient.obj A) ≪≫
    (asIso (R.ordinaryInfinity.map (N.quotientMap.app A))).symm

/-- Retain the SAME action while exposing the compact fiber equivalence. -/
def normalizedOriginCompactEquiv {underlying : Perv ⥤ Derived}
    (N : CurveNormalizationOperations (Ord := Ord) underlying)
    (S : StandardFiniteOriginOperations (LF := LF) underlying)
    (R : GeneralCurveFiberRules N S)
    (s : PhaseField K) (hs : s ≠ 0) (A : Ord) :
    Representation.Equiv ((normalizedData N S).origin s hs A).ρ
      ((R.compactDegreeOne s hs).obj A).ρ :=
  TensorListRepresentation.equivOfIso (normalizedOriginCompactIso N S R s hs A)

/-- The whole all-object InfinityCompatibility record is derived from
GENERAL ordinary open-restriction and dual-restriction laws on the SAME
chosen operations. No selected correlation infinity model is an input. -/
def normalizedInfinityCompatibility
    {L : Type g} [Category.{h} L] [MonoidalCategory L]
    {underlying : Perv ⥤ Derived}
    (N : CurveNormalizationOperations (Ord := Ord) underlying)
    (S : StandardFiniteOriginOperations (LF := LF) underlying)
    (R : GeneralCurveFiberRules N S)
    (ops : SheafOperations (PhaseField K) L Ord)
    (Jinf : L ⥤ FDRep E I) [Jinf.Monoidal]
    (dualRestriction : ∀ A, Representation.Equiv (Jinf.obj (ops.dual A)).ρ
      (dualRepresentation (Jinf.obj A)).ρ)
    (ordinaryOpenRestriction : ∀ A,
      R.ordinaryInfinity.obj (ops.middleExtension.obj A) ≅ Jinf.obj A) :
    InfinityCompatibility ops Jinf (normalizedData N S) where
  dual A := dualRestriction A
  middleExtension A := TensorListRepresentation.equivOfIso
    (normalizedInfinityIso N S R (ops.middleExtension.obj A) ≪≫ ordinaryOpenRestriction A)

end PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03

#print axioms PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03.StandardFiniteOriginOperations.perverseData
#print axioms PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03.normalizedData
#print axioms PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03.normalizedRules
#print axioms PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03.normalizedOriginCompactIso
#print axioms PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03.normalizedInfinityIso
#print axioms PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03.normalizedOriginCompactEquiv
#print axioms PrimeGap182.TypeIII.CoherentNormalizedFourierCompactInfinity03.normalizedInfinityCompatibility
