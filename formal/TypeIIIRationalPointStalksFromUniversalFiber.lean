import TypeIIICanonicalPrimeFramework
import TypeIIIRationalPointStalks

/-!
# Arithmetic point stalks from one universal inverse-image system

One ordinary coefficient fiber and its geometric Frobenius transformation
are fixed on EVERY finite field spectrum, independently of a prime. The
actual scheme-point inverse image constructs all source, line and torus
fibers. SAME-U ordinary composition constructs their pullback comparison.
Naturality of the ONE coefficient Frobenius proves the comparison equation;
no separate pointwise Frobenius/pullback law is supplied.

The ordinary arithmetic/adic category, finite coefficient fibers and
interpretation of their geometric Frobenius remain general published
framework parameters. This construction does not identify arbitrary
independent point or local-action models, or construct a whole Inputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.RationalPointStalksFromUniversalFiber
open ExactInverseImagesToDerived UniversalOrdinaryInverseImages
open CanonicalPrimeFramework SourceInverseImageSystem

universe mu
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)]

/-- General ordinary arithmetic coefficient fibers, fixed BEFORE a prime.
Frobenius is one natural transformation on every finite field category. -/
structure ArithmeticFibers where
  fiber : ∀ (E : Type) [Field E] [Fintype E], C (Spec (.of E)) ⥤ ModuleCat.{0} ℂ
  frobenius : ∀ (E : Type) [Field E] [Fintype E], fiber E ⟶ fiber E
  finite : ∀ (E : Type) [Field E] [Fintype E] A,
    FiniteDimensional ℂ ((fiber E).obj A)

variable [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

/-- Every original point uses ACTUAL inverse image to its finite spectrum.
The comparison and Frobenius covariance are constructed, not fields. -/
def pointStalks (F : ArithmeticFibers C) (p : ℕ) [Fact p.Prime] :
    RationalPointStalks.Data (primeSource C U p) where
  fiber E _ _ _ X x := U.pull x ⋙ F.fiber E
  frobenius E _ _ _ X x := (U.pull x).whiskerLeft (F.frobenius E)
  finite E _ _ _ X x A := F.finite E ((U.pull x).obj A)
  pullback E _ _ _ {X Y} f x := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (U.composition x f) (F.fiber E)
  frobenius_pullback E _ _ _ {X Y} f x A := by
    dsimp
    simp only [Category.id_comp]
    exact ((F.frobenius E).naturality ((U.composition x f).hom.app A)).symm

variable {C U} {F : ArithmeticFibers C} {p : ℕ} [Fact p.Prime]

/-- The ordinary fiber of every original point has this SAME-U formula. -/
theorem pointStalks_fiber (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X) :
    (pointStalks C U F p).fiber E X x = U.pull x ⋙ F.fiber E := rfl

/-- There is no independently chosen Frobenius on a pulled-back object. -/
theorem pointStalks_frobenius (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X) :
    (pointStalks C U F p).frobenius E X x =
      (U.pull x).whiskerLeft (F.frobenius E) := rfl

/-- The original trace-pullback endpoint follows for EVERY original map. -/
theorem pointStalks_pullback_trace (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    {X Y : Space (ZMod p)} (f : scheme (ZMod p) X ⟶ scheme (ZMod p) Y)
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : (primeSource C U p).Obj Y) :
    (pointStalks C U F p).trace E x (((primeSource C U p).pull f).obj A) =
      (pointStalks C U F p).trace E (x ≫ f) A :=
  RationalPointStalks.Data.pullback_trace (pointStalks C U F p) E f x A

end PrimeGap182.TypeIII.RationalPointStalksFromUniversalFiber

#print axioms PrimeGap182.TypeIII.RationalPointStalksFromUniversalFiber.pointStalks
#print axioms PrimeGap182.TypeIII.RationalPointStalksFromUniversalFiber.pointStalks_pullback_trace
