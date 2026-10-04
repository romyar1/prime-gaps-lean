import TypeIIISourceRanksFromCommonFinitePoint
import TypeIIINativePointFiberFromUniversalGeometricFibers
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generic source rank from the actual fraction-field point

The original source ring is already integral. Its actual fraction-field
point is dominant and determines the generic source rank by SAME-U ordinary
pullback and SAME-G finite geometric coefficient fiber. This definition
also applies to constructible objects with exceptional finite-point stalks.

Tensor rank follows from ALL-field geometric coefficient tensor comparison.
Lisse dual rank follows from bijectivity of the computed finite-locally-free
internal-Hom comparison at EVERY field-valued point of EVERY scheme. These
are three honest general framework capabilities (tensor, unit and dual). None is inferred from
arithmetic coefficient laws that quantify finite fields only. No arbitrary
rank observable, ALL-constructible pointwise rank constancy, arithmetic
Frobenius law or selected source rank clause is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

namespace PrimeGap182.TypeIII.GenericSourceRanksFromActualFractionPoint
open ExactInverseImagesToDerived QSTDualityBridgesFromSmoothLisseVerdier
open CanonicalOrdinaryDualEvaluation

variable (K : Type) [Field K]

abbrev GenericSourceField := FractionRing (StartingSourceMaps.SourceRing K)

/-- The actual generic point of the original source torus. -/
def genericSourcePoint : Spec (.of (GenericSourceField K)) ⟶ StartingSourceMaps.sourceScheme K :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (StartingSourceMaps.SourceRing K) (GenericSourceField K)))

/-- The fraction-field map is dominant on the integral source. -/
theorem genericSourcePoint_dominant : IsDominant (genericSourcePoint K) := by
  constructor
  change DenseRange (PrimeSpectrum.comap
    (algebraMap (StartingSourceMaps.SourceRing K) (GenericSourceField K)))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
    (IsFractionRing.injective (StartingSourceMaps.SourceRing K) (GenericSourceField K))]
  exact bot_le

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)

/-- Dimension of the actual geometric coefficient fiber at an arbitrary field point. -/
def geometricPointRank (E : Type) [Field E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) (A : C X) : ℕ :=
  Module.finrank ℂ ((U.pull x ⋙ G.fiber E).obj A)

/-- Generic rank is computed at the original source's dominant fraction-field point. -/
def canonicalGenericSourceRank (A : C (StartingSourceMaps.sourceScheme K)) : ℕ :=
  geometricPointRank C U G (GenericSourceField K) _ (genericSourcePoint K) A

/-- Actual ordinary isomorphisms preserve all geometric point ranks. -/
theorem geometricPointRank_iso (E : Type) [Field E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) {A B : C X} (e : A ≅ B) :
    geometricPointRank C U G E X x A = geometricPointRank C U G E X x B :=
  ((U.pull x ⋙ G.fiber E).mapIso e).toLinearEquiv.finrank_eq

/-- Actual ordinary isomorphisms preserve the computed generic source rank. -/
theorem canonicalGenericSourceRank_iso {A B : C (StartingSourceMaps.sourceScheme K)} (e : A ≅ B) :
    canonicalGenericSourceRank K C U G A = canonicalGenericSourceRank K C U G B :=
  geometricPointRank_iso C U G (GenericSourceField K) _ (genericSourcePoint K) e

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (geometricCoefficientTensor : ∀ (E : Type) [Field E]
    (A B : C (Spec (.of E))),
      ((G.fiber E).obj A ⊗[ℂ] (G.fiber E).obj B) ≃ₗ[ℂ]
        (G.fiber E).obj (A ⊗ B))

/-- The actual ordinary coefficient tensor comparison, transported through SAME-U. -/
def geometricPointTensorEquiv (X : Scheme) (E : Type) [Field E]
    (x : Spec (.of E) ⟶ X) (A B : C X) :
    ((U.pull x ⋙ G.fiber E).obj A ⊗[ℂ] (U.pull x ⋙ G.fiber E).obj B) ≃ₗ[ℂ]
      (U.pull x ⋙ G.fiber E).obj (A ⊗ B) :=
  (geometricCoefficientTensor E ((U.pull x).obj A) ((U.pull x).obj B)).trans
    ((G.fiber E).mapIso (Functor.Monoidal.μIso (U.pull x) A B)).toLinearEquiv

include geometricCoefficientTensor in
/-- Tensor dimensions multiply at every actual geometric field point. -/
theorem geometricPointRank_tensor (E : Type) [Field E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) (A B : C X) :
    geometricPointRank C U G E X x (A ⊗ B) =
      geometricPointRank C U G E X x A * geometricPointRank C U G E X x B := by
  let : FiniteDimensional ℂ ((U.pull x ⋙ G.fiber E).obj A) := G.finite E ((U.pull x).obj A)
  let : FiniteDimensional ℂ ((U.pull x ⋙ G.fiber E).obj B) := G.finite E ((U.pull x).obj B)
  exact (geometricPointTensorEquiv C U G geometricCoefficientTensor X E x A B).finrank_eq.symm.trans
    Module.finrank_tensorProduct

include geometricCoefficientTensor in
/-- The computed generic source rank has the original tensor rank law. -/
theorem source_tensor_rank (A B : C (StartingSourceMaps.sourceScheme K)) :
    canonicalGenericSourceRank K C U G (A ⊗ B) =
      canonicalGenericSourceRank K C U G A * canonicalGenericSourceRank K C U G B :=
  geometricPointRank_tensor C U G geometricCoefficientTensor (GenericSourceField K) _
    (genericSourcePoint K) A B

variable (geometricCoefficientUnit : ∀ (E : Type) [Field E],
    ℂ ≃ₗ[ℂ] (G.fiber E).obj (𝟙_ (C (Spec (.of E)))))

/-- The actual ordinary coefficient unit comparison, transported through SAME-U. -/
def geometricPointUnitEquiv (X : Scheme) (E : Type) [Field E]
    (x : Spec (.of E) ⟶ X) :
    ℂ ≃ₗ[ℂ] (U.pull x ⋙ G.fiber E).obj (𝟙_ (C X)) :=
  (geometricCoefficientUnit E).trans
    ((G.fiber E).mapIso (Functor.Monoidal.εIso (U.pull x))).toLinearEquiv

variable [∀ X, MonoidalClosed (C X)] [∀ X, BraidedCategory (C X)]

/-- Currying the actual source evaluation and the transported coefficient
tensor/unit maps determines the dual map in the geometric module universe. -/
def genericCanonicalDualMap (X : Scheme) (E : Type) [Field E]
    (x : Spec (.of E) ⟶ X) (A : C X) :
    (U.pull x ⋙ G.fiber E).obj ((ordinaryDual C X).obj (op A)) →ₗ[ℂ]
      Module.Dual ℂ ((U.pull x ⋙ G.fiber E).obj A) :=
  TensorProduct.curry ((geometricPointUnitEquiv C U G geometricCoefficientUnit X E x).symm.toLinearMap ∘ₗ
    ((U.pull x ⋙ G.fiber E).map (sourceEvaluate C X A)).hom ∘ₗ
    (geometricPointTensorEquiv C U G geometricCoefficientTensor X E x
      ((ordinaryDual C X).obj (op A)) A).toLinearMap)

variable (L : ∀ X : Scheme, C X → Prop)
  (geometricDualStalkBijective : ∀ (X : Scheme) (E : Type) [Field E]
    (x : Spec (.of E) ⟶ X) (A : C X), L X A →
      Function.Bijective (genericCanonicalDualMap C U G geometricCoefficientTensor
        geometricCoefficientUnit X E x A))

/-- The universal finite-lisse theorem turns the computed geometric dual map into an equivalence. -/
def genericDualStalkEquiv (X : Scheme) (E : Type) [Field E]
    (x : Spec (.of E) ⟶ X) (A : C X) (hA : L X A) :
    (U.pull x ⋙ G.fiber E).obj ((ordinaryDual C X).obj (op A)) ≃ₗ[ℂ]
      Module.Dual ℂ ((U.pull x ⋙ G.fiber E).obj A) :=
  LinearEquiv.ofBijective (genericCanonicalDualMap C U G geometricCoefficientTensor
    geometricCoefficientUnit X E x A) (geometricDualStalkBijective X E x A hA)

include geometricCoefficientTensor geometricCoefficientUnit geometricDualStalkBijective in
/-- Globally finite-rank lisse duals have the same dimension at every geometric point. -/
theorem geometricPointRank_dual (E : Type) [Field E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) (A : C X) (hA : L X A) :
    geometricPointRank C U G E X x ((ordinaryDual C X).obj (op A)) =
      geometricPointRank C U G E X x A := by
  let : FiniteDimensional ℂ ((U.pull x ⋙ G.fiber E).obj A) := G.finite E ((U.pull x).obj A)
  exact (genericDualStalkEquiv C U G geometricCoefficientTensor geometricCoefficientUnit
    L geometricDualStalkBijective X E x A hA).finrank_eq.trans Subspace.dual_finrank_eq

include geometricCoefficientTensor geometricCoefficientUnit geometricDualStalkBijective in
/-- The original globally lisse source dual preserves its computed generic rank. -/
theorem source_dual_rank (A : C (StartingSourceMaps.sourceScheme K))
    (hA : L (StartingSourceMaps.sourceScheme K) A) :
    canonicalGenericSourceRank K C U G
      ((ordinaryDual C (StartingSourceMaps.sourceScheme K)).obj (op A)) =
      canonicalGenericSourceRank K C U G A :=
  geometricPointRank_dual C U G geometricCoefficientTensor geometricCoefficientUnit
    L geometricDualStalkBijective (GenericSourceField K) _ (genericSourcePoint K) A hA

end PrimeGap182.TypeIII.GenericSourceRanksFromActualFractionPoint
