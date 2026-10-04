import TypeIIIArithmeticSourceMaps
import TypeIIIRationalPointStalksFromUniversalFiber

/-!
# The actual arithmetic source point factors through its Laurent fiber

Universal Laurent evaluation proves the point-map equality on the original
quotient source, with the same curve coordinate and parameter units. The
same ordinary inverse-image compositor constructs the point fiber isomorphism.
Naturality of the already supplied finite coefficient Frobenius constructs
its square. No standard coefficient category, Frobenius comparison, trace
formula, or new model recognition is assumed or constructed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial

namespace PrimeGap182.TypeIII.ArithmeticSourcePointFromLaurentSpecialization
open StartingSourceMaps ArithmeticSourceMaps ExactInverseImagesToDerived
open RationalPointStalksFromUniversalFiber

variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- Evaluation at the actual unit of the Laurent curve. -/
def laurentEvaluation (z : Eˣ) : LaurentPolynomial E →ₐ[K] E where
  toRingHom := LaurentPolynomial.eval₂ (RingHom.id E) z
  commutes' c := by
    change LaurentPolynomial.eval₂ _ z
      (LaurentPolynomial.C (algebraMap K E c)) = _
    rw [LaurentPolynomial.eval₂_C]
    rfl

/-- The point on the actual Laurent curve, independent of the base field. -/
def gmPoint (z : Eˣ) : Spec (.of E) ⟶ fiberScheme E :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id E) z))

/-- Composition evaluates all six original source coordinates. -/
theorem evaluation_comp_specialization (z lambda xi : Eˣ) :
    (laurentEvaluation K E z).comp (specializationHom K E lambda xi) =
      StartingSourceMaps.evaluation (K := K) z lambda xi := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change laurentEvaluation K E z
    (evaluation _ _ _ (coordinate K i)) = evaluation _ _ _ (coordinate K i)
  rw [evaluation_coordinate, evaluation_coordinate]
  fin_cases i <;>
    simp [unitCoordinates, laurentEvaluation,
      constantUnit, PhysicalTorusLaurent.variableUnit,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]

/-- This is an equality of the original scheme maps, over every extension. -/
theorem sourcePoint_eq_gmPoint_specialization (z lambda xi : Eˣ) :
    RationalPointStalks.curvePoint (K := K) z lambda xi =
      gmPoint E z ≫ specializationMorphism K E lambda xi := by
  dsimp only [RationalPointStalks.curvePoint, gmPoint, specializationMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact (congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom
      (evaluation_comp_specialization K E z lambda xi))).symm

universe mu
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)

/-- SAME-U composition, followed only by the proved point-map equality. -/
def sourcePointPullIso (z lambda xi : Eˣ) :
    U.pull (specializationMorphism K E lambda xi) ⋙ U.pull (gmPoint E z) ≅
      U.pull (RationalPointStalks.curvePoint (K := K) z lambda xi) :=
  U.composition (gmPoint E z) (specializationMorphism K E lambda xi) ≪≫
    eqToIso (congrArg (fun f => U.pull f)
      (sourcePoint_eq_gmPoint_specialization K E z lambda xi).symm)

variable [Fintype E] (F : ArithmeticFibers C)

/-- The coefficient fiber is the retained finite arithmetic fiber. -/
def sourcePointFiberIso (z lambda xi : Eˣ) :
    (U.pull (specializationMorphism K E lambda xi) ⋙ U.pull (gmPoint E z)) ⋙
        F.fiber E ≅
      U.pull (RationalPointStalks.curvePoint (K := K) z lambda xi) ⋙ F.fiber E :=
  Functor.isoWhiskerRight (sourcePointPullIso K E C U z lambda xi) (F.fiber E)

/-- Frobenius covariance uses only its retained naturality on C(Spec E). -/
theorem sourcePointFiberIso_frobenius (z lambda xi : Eˣ)
    (A : C (sourceScheme K)) :
    (F.frobenius E).app
        ((U.pull (gmPoint E z)).obj
          ((U.pull (specializationMorphism K E lambda xi)).obj A)) ≫
        (sourcePointFiberIso K E C U F z lambda xi).hom.app A =
      (sourcePointFiberIso K E C U F z lambda xi).hom.app A ≫
        (F.frobenius E).app
          ((U.pull (RationalPointStalks.curvePoint (K := K) z lambda xi)).obj A) := by
  exact ((F.frobenius E).naturality
    ((sourcePointPullIso K E C U z lambda xi).hom.app A)).symm

end PrimeGap182.TypeIII.ArithmeticSourcePointFromLaurentSpecialization
