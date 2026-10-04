import TypeIIIArithmeticPrimitivesFromCommonKatzConstruction
import TypeIIIRationalPointStalksFromUniversalFiber

/-!
# Primitive Tate trace from the SAME general point-stalk normalization

ALL field-line objects, all finite-field spectrum points and all integer
Tate twists have a natural stalk isomorphism with geometric Frobenius scaled
by q^(-n). This precise general representation theorem is an explicit
parameter. Actual linear trace invariance and linearity derive the original
Tate(+1) trace clause on SAME primitive operations and SAME F/U point stalks.
No selected trace formula, completed Rules, new global axiom or numerical
estimate is supplied. Continuous-adic/Tate interpretation remains external.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PrimeGap182.TypeIII.PrimitiveTateTraceFromGeneralStalkNormalization
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open RationalPointStalksFromUniversalFiber

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (F : ArithmeticFibers C) (O : Constructions C)

/-- Trace of the actual SAME-U inverse-image point and SAME-F Frobenius. -/
def pointTrace {K : Type} [Field K] (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K)
    (A : C (StartingSourceMaps.affineLine K)) : ℂ :=
  LinearMap.trace ℂ ((F.fiber E).obj ((U.pull x).obj A))
    ((F.frobenius E).app ((U.pull x).obj A)).hom

variable
  (pointTateIso : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K) (n : ℤ),
    O.lineTate K h2 n ⋙ U.pull x ⋙ F.fiber E ≅ U.pull x ⋙ F.fiber E)
  (pointTateFrobenius : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K) (n : ℤ)
    (A : C (StartingSourceMaps.affineLine K)),
    ((pointTateIso K h2 E x n).app A).toLinearEquiv.conj
      ((F.frobenius E).app ((U.pull x).obj ((O.lineTate K h2 n).obj A))).hom =
    (Fintype.card E : ℂ)^(-n) • ((F.frobenius E).app ((U.pull x).obj A)).hom)

include pointTateFrobenius in
/-- GENERAL all-integer Tate trace normalization, derived from Frobenius
conjugacy and actual linear trace; no trace formula is a premise. -/
theorem point_tate_trace (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K) (n : ℤ)
    (A : C (StartingSourceMaps.affineLine K)) :
    pointTrace C U F E x ((O.lineTate K h2 n).obj A) =
      (Fintype.card E : ℂ)^(-n) * pointTrace C U F E x A := by
  let e := ((pointTateIso K h2 E x n).app A).toLinearEquiv
  have hc : e.conj
      ((F.frobenius E).app ((U.pull x).obj ((O.lineTate K h2 n).obj A))).hom =
      (Fintype.card E : ℂ)^(-n) • ((F.frobenius E).app ((U.pull x).obj A)).hom :=
    pointTateFrobenius K h2 E x n A
  have h := (LinearMap.trace_conj' 
    ((F.frobenius E).app ((U.pull x).obj ((O.lineTate K h2 n).obj A))).hom e).symm
  have ht := congrArg (LinearMap.trace ℂ ((U.pull x ⋙ F.fiber E).obj A)) hc
  simpa only [Functor.comp_obj, map_smul, smul_eq_mul, pointTrace] using h.trans ht

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

include pointTateFrobenius in
/-- Exact original primitiveLaw.tateTrace on SAME pointStalks and SAME
ordinary Tate(+1) operation, for every object and every point including zero. -/
theorem primitive_tate_trace (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (A : C (StartingSourceMaps.affineLine (ZMod p))) (z : E) :
    let D := RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
      (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)
    D.trace E (D.twistOne A) z = (Fintype.card E : ℂ)⁻¹ * D.trace E A z := by
  change pointTrace C U F E (RationalPointStalks.linePoint z)
      ((O.lineTate (ZMod p) h2 1).obj A) =
    (Fintype.card E : ℂ)⁻¹ * pointTrace C U F E (RationalPointStalks.linePoint z) A
  simpa only [zpow_neg_one] using
    point_tate_trace C U F O pointTateIso pointTateFrobenius (ZMod p) h2 E
      (RationalPointStalks.linePoint z) 1 A

end PrimeGap182.TypeIII.PrimitiveTateTraceFromGeneralStalkNormalization
