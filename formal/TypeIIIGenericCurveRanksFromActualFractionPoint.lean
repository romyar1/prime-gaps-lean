import TypeIIIGenericSourceRanksFromActualFractionPoint
import TypeIIIGenericCurvePullback

/-!
# Generic curve ranks at the actual original fraction-field point

The SAME original generic Laurent curve has an actual dominant fraction-field
point. Its rank is the dimension of SAME-U/SAME-G ordinary coefficient fiber,
not an independently supplied observable or a finite-point anchor. Tensor,
unit and lisse-dual ranks reuse the existing ALL-scheme/ALL-field coefficient
comparisons. ONE precise ALL-integral-scheme globally finite-rank lisse point
rank-constancy theorem identifies an actual source pullback rank. This theorem
allows arbitrary field-valued points, including the transcendental geometric
base; the older finite-arithmetic-point comparison is not substituted here.
Continuous/adic fiber and Lisse recognition remain general model parameters.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct
namespace PrimeGap182.TypeIII.GenericCurveRanksFromActualFractionPoint
open ExactInverseImagesToDerived GenericSourceRanksFromActualFractionPoint
open GenericSourceSpecialization GenericCurvePullback QSTDualityBridgesFromSmoothLisseVerdier

variable (K : Type) [Field K]
abbrev GenericCurveField := FractionRing (GenericRing K)

/-- Literal dominant point of the SAME original generic Laurent scheme. -/
def genericCurvePoint : Spec (.of (GenericCurveField K)) ⟶ genericScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (GenericRing K) (GenericCurveField K)))

theorem genericCurvePoint_dominant : IsDominant (genericCurvePoint K) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap (GenericRing K) (GenericCurveField K)))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (GenericRing K) (GenericCurveField K))]
  exact bot_le

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)

/-- Computed intrinsic generic rank, including arbitrary constructible objects. -/
def canonicalGenericCurveRank (A : C (genericScheme K)) : ℕ :=
  geometricPointRank C U G (GenericCurveField K) _ (genericCurvePoint K) A

theorem genericCurveRank_iso {A B : C (genericScheme K)} (e : A ≅ B) :
    canonicalGenericCurveRank K C U G A = canonicalGenericCurveRank K C U G B :=
  geometricPointRank_iso C U G (GenericCurveField K) _ (genericCurvePoint K) e

/-- Exact ordinary composition identifies ranks at every pulled actual point. -/
theorem geometricPointRank_pull {X Y : Scheme} (f : X ⟶ Y) (E : Type) [Field E]
    (x : Spec (.of E) ⟶ X) (A : C Y) :
    geometricPointRank C U G E X x ((U.pull f).obj A) =
      geometricPointRank C U G E Y (x ≫ f) A :=
  ((Functor.isoWhiskerRight (U.composition x f) (G.fiber E)).app A).toLinearEquiv.finrank_eq

variable (L : ∀ X : Scheme, ObjectProperty (C X))
  (lisseGeometricPointRank : ∀ (X : Scheme) [IsIntegral X] (A : C X), L X A →
    ∀ (E E' : Type) [Field E] [Field E'] (x : Spec (.of E) ⟶ X) (y : Spec (.of E') ⟶ X),
      geometricPointRank C U G E X x A = geometricPointRank C U G E' X y A)

include lisseGeometricPointRank in
/-- Generic curve pullback rank equals ANY geometric point rank on an integral lisse target. -/
theorem genericCurveRank_pullback_at_point (Y : Scheme) [IsIntegral Y]
    (f : genericScheme K ⟶ Y) (A : C Y) (hA : L Y A)
    (E : Type) [Field E] (y : Spec (.of E) ⟶ Y) :
    canonicalGenericCurveRank K C U G ((U.pull f).obj A) = geometricPointRank C U G E Y y A :=
  (geometricPointRank_pull C U G f (GenericCurveField K) (genericCurvePoint K) A).trans
    (lisseGeometricPointRank Y A hA (GenericCurveField K) E (genericCurvePoint K ≫ f) y)

include lisseGeometricPointRank in
/-- The SAME original source and ANY actual generic pullback have equal intrinsic rank. -/
theorem source_genericCurve_rank (f : genericScheme K ⟶ StartingSourceMaps.sourceScheme K)
    (A : C (StartingSourceMaps.sourceScheme K)) (hA : L (StartingSourceMaps.sourceScheme K) A) :
    canonicalGenericCurveRank K C U G ((U.pull f).obj A) = canonicalGenericSourceRank K C U G A :=
  genericCurveRank_pullback_at_point K C U G L lisseGeometricPointRank _ f A hA
    (GenericSourceField K) (genericSourcePoint K)

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (geometricCoefficientTensor : ∀ (E : Type) [Field E] (A B : C (Spec (.of E))),
    ((G.fiber E).obj A ⊗[ℂ] (G.fiber E).obj B) ≃ₗ[ℂ] (G.fiber E).obj (A ⊗ B))
  (geometricCoefficientUnit : ∀ (E : Type) [Field E],
    ℂ ≃ₗ[ℂ] (G.fiber E).obj (𝟙_ (C (Spec (.of E)))))

include geometricCoefficientTensor in
/-- Tensor ranks multiply at the actual generic point. -/
theorem genericCurveRank_tensor (A B : C (genericScheme K)) :
    canonicalGenericCurveRank K C U G (A ⊗ B) =
      canonicalGenericCurveRank K C U G A * canonicalGenericCurveRank K C U G B :=
  geometricPointRank_tensor C U G geometricCoefficientTensor (GenericCurveField K) _
    (genericCurvePoint K) A B

include geometricCoefficientUnit in
/-- The intrinsic actual coefficient unit has generic rank one. -/
theorem genericCurveRank_unit : canonicalGenericCurveRank K C U G (𝟙_ (C (genericScheme K))) = 1 := by
  have h := (geometricPointUnitEquiv C U G geometricCoefficientUnit _ (GenericCurveField K)
    (genericCurvePoint K)).finrank_eq
  simpa [canonicalGenericCurveRank, geometricPointRank] using h.symm

variable [∀ X, MonoidalClosed (C X)] [∀ X, BraidedCategory (C X)]
  (geometricDualStalkBijective : ∀ (X : Scheme) (E : Type) [Field E]
    (x : Spec (.of E) ⟶ X) (A : C X), L X A →
      Function.Bijective (genericCanonicalDualMap C U G geometricCoefficientTensor
        geometricCoefficientUnit X E x A))

include geometricCoefficientTensor geometricCoefficientUnit geometricDualStalkBijective in
/-- Globally finite-rank lisse duals preserve this SAME computed generic rank. -/
theorem genericCurveRank_dual (A : C (genericScheme K)) (hA : L (genericScheme K) A) :
    canonicalGenericCurveRank K C U G ((ordinaryDual C _).obj (op A)) =
      canonicalGenericCurveRank K C U G A :=
  geometricPointRank_dual C U G geometricCoefficientTensor geometricCoefficientUnit
    L geometricDualStalkBijective (GenericCurveField K) _ (genericCurvePoint K) A hA

end PrimeGap182.TypeIII.GenericCurveRanksFromActualFractionPoint
