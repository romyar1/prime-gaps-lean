import TypeIIIParabolicMiddleComparison

/-!
# Rank of the physical parabolic image at a geometric stalk

The GOS dimension formula is separated from finite-field traces and
Frobenius. It applies to a geometric point, including a generic point.
The actual image of the original compact-to-ordinary comparison has rank
six once its geometric boundary is identified with the computed Jordan
centralizer. No final core rank, finite base field, or Frobenius operator
is an input. The geometric boundary identification remains to be supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.GeometricCoreRank

open PublishedPhysicalConstruction ParabolicMiddleComparison

universe u v w z
variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C)
  (F : C ⥤ ModuleCat.{w} ℂ)

/-- The geometric GOS and vanishing consequence at a chosen point, for
every lisse input of slope one and dual slope one. Finite dimensionality
is explicit. There is no arithmetic field or trace in this record. -/
structure GeometricFiberRules (point : Point) : Prop where
  compact_finite : ∀ A, D.Lisse A → FiniteDimensional ℂ (F.obj (H.compact A))
  compact_rank : ∀ A, D.Lisse A → D.Isoclinic A 1 → D.Isoclinic (D.dual A) 1 →
    Module.finrank ℂ (F.obj (H.compact A)) =
      D.swanZero A point + D.swanInfinity A point

/-- Only the geometric part of the original boundary model is needed
for rank: an injection with image the kernel of the ORIGINAL comparison.
The boundary space is the actual, already computed matrix centralizer. -/
structure GeometricBoundaryModel (A : Input) where
  boundary : jordanThreeCentralizer ℂ →ₗ[ℂ] F.obj (H.compact A)
  injective : Function.Injective boundary
  exact : LinearMap.range boundary = LinearMap.ker (F.map (H.comparison A)).hom

variable {D H F} (K : KloostermanInputData D) (R : CurveRules D)
  (point : Point) (V : GeometricFiberRules D H F point)

include R V in
omit [Abelian C] in
theorem compact_rank_nine : Module.finrank ℂ (F.obj (H.compact K.input)) = 9 := by
  rw [V.compact_rank _ (K.input_lisse R) (K.input_slope_one R)
    (R.dual_isoclinic _ _ (K.input_slope_one R)),
    (K.input_swan R point).1, (K.input_swan R point).2]

variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (B : GeometricBoundaryModel H F K.input)

include R V in
theorem core_finite : FiniteDimensional ℂ (F.obj (parabolicCore H K.input)) := by
  let := V.compact_finite _ (K.input_lisse R)
  exact FiniteDimensional.of_surjective (coreStalkQuotient H F K.input)
    (coreStalkQuotient_surjective H F K.input)

include R V B in
theorem core_rank_add_three :
    Module.finrank ℂ (F.obj (parabolicCore H K.input)) + 3 =
      Module.finrank ℂ (F.obj (H.compact K.input)) := by
  let := V.compact_finite _ (K.input_lisse R)
  have h := (coreStalkQuotient H F K.input).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (coreStalkQuotient_surjective H F K.input),
    finrank_top, coreStalkQuotient_ker H F K.input, ← B.exact,
    LinearMap.finrank_range_of_inj B.injective, jordanThreeCentralizer_finrank] at h
  exact h

include R V B in
/-- GOS and the boundary sequence give rank six at this geometric stalk. -/
theorem core_rank_six : Module.finrank ℂ (F.obj (parabolicCore H K.input)) = 6 := by
  have h := core_rank_add_three K R point V B
  rw [compact_rank_nine K R point V] at h
  omega

include R V B in
/-- Transfer the derived rank through the canonical image-to-middle
comparison. Its two geometric boundary sequences still must be supplied. -/
theorem middle_rank_six
    (M : BoundaryFactorization (F.map (H.comparison K.input)))
    (hleft : M.fromBoundary.hom = 0) (hright : M.toBoundary.hom = 0) :
    Module.finrank ℂ M.middle = 6 := by
  rw [← (coreStalkMiddleIso H F K.input M hleft hright).toLinearEquiv.finrank_eq]
  exact core_rank_six K R point V B

end PrimeGap182.TypeIII.GeometricCoreRank

#print axioms PrimeGap182.TypeIII.GeometricCoreRank.compact_rank_nine
#print axioms PrimeGap182.TypeIII.GeometricCoreRank.core_finite
#print axioms PrimeGap182.TypeIII.GeometricCoreRank.core_rank_add_three
#print axioms PrimeGap182.TypeIII.GeometricCoreRank.core_rank_six
#print axioms PrimeGap182.TypeIII.GeometricCoreRank.middle_rank_six
