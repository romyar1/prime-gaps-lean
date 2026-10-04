import TypeIIIArithmeticBoundaryAssemblyFromCanonicalMaps11
import Mathlib.RepresentationTheory.Invariants

/-! Pure guarded finite-fiber transport of canonical localization.
The standard/source localization objects and operations are independent input
data. This module constructs no standard continuous coefficient interpretation
or native trait/Weil realization. Actual applications must derive compact and
guarded ordinary comparisons from individual canonical operation mates; the
support square is an operation-level hypothesis here, not a selected finished
boundary, exactness or connecting-Frobenius hypothesis.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryFromGuardedFiniteFiberOperations
open PublishedPhysicalConstruction PublishedPhaseApplication PublishedMackey
open ArithmeticBoundaryFromCanonicalLocalization ArithmeticDualFromCanonicalEvaluation
open GeometricBoundaryFromFunctors

universe u v a b g t c d e
variable {Input : Type u} [Category.{v} Input] [MonoidalCategory Input]
  {Local : Type a} [Category.{b} Local] [MonoidalCategory Local]
  {G : Type g} [Group G] {Ginf : Type t} [Group Ginf]
  (along : Input ⥤ Local) [along.Monoidal]
  (J : Local ⥤ FDRep ℂ G) [J.Monoidal]
  {Point : Type c}
  {Native : Type} [Category.{d} Native] [Abelian Native]
  {Standard : Type} [Category.{e} Standard] [Abelian Standard]
  (O : CurveDataFromOperations.Observables Input Point)
  (dual : Inputᵒᵖ ⥤ Input) (ev : ∀ A, dual.obj (op A) ⊗ A ⟶ 𝟙_ Input)
  (standardCurve : CurveData Input Point)
  (nativeH : CohomologyData Input Native) (nativeF : Native ⥤ ModuleCat.{0} ℂ)
  (standardH : CohomologyData Input Standard) (standardF : Standard ⥤ ModuleCat.{0} ℂ)
  (standardZero : Input ⥤ FDRep ℂ G)
  (zeroComparison : along ⋙ J ≅ standardZero)
  (infinity : Input ⥤ FDRep ℂ Ginf)
  (N : LocalizationData standardH standardF standardZero infinity)
  {p : ℕ} [Fact p.Prime] {h2 : 2 ≠ p}
  (R : LocalizationLaws standardCurve N p h2)
  (lisseMeaning : ∀ A, O.Lisse A → standardCurve.Lisse A)
  (slopeMeaning : ∀ A, (O.curveData dual).Isoclinic A 1 → standardCurve.Isoclinic A 1)
  (standardPositive : ∀ A, standardCurve.Isoclinic A 1 →
    Representation.invariants (infinity.obj A).ρ = ⊥)
  (bijective : ∀ A, O.Lisse A → Function.Bijective (canonicalDualMap (along ⋙ J) dual ev A))
  (compactComparison : ∀ A,
    nativeF.obj (nativeH.compact A) ≃ₗ[ℂ] standardF.obj (standardH.compact A))
  (ordinaryComparison : ∀ A, O.Lisse A → (O.curveData dual).TameZero A →
    (O.curveData dual).Isoclinic A 1 →
      nativeF.obj (nativeH.ordinary A) ≃ₗ[ℂ] standardF.obj (standardH.ordinary A))
  (supportSquare : ∀ A hL hT hS,
    (ordinaryComparison A hL hT hS).toLinearMap.comp (nativeF.map (nativeH.comparison A)).hom =
      (standardF.map (standardH.comparison A)).hom.comp (compactComparison A).toLinearMap)

/-- Invariants comparison computed by the actual functor isomorphism. -/
def zeroInvariantsComparison (A : Input) :
    Representation.invariants (((along ⋙ J).obj A).ρ) ≃ₗ[ℂ]
      Representation.invariants ((standardZero.obj A).ρ) :=
  ((Rep.invariantsFunctor ℂ G).mapIso
    ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso (zeroComparison.app A))).toLinearEquiv

/-- The product comparison changes only the origin acted coefficient object. -/
def boundaryInvariantsComparison (A : Input) :
    (Representation.invariants (((along ⋙ J).obj A).ρ) ×
      Representation.invariants ((infinity.obj A).ρ)) ≃ₗ[ℂ]
    (Representation.invariants ((standardZero.obj A).ρ) ×
      Representation.invariants ((infinity.obj A).ρ)) :=
  (zeroInvariantsComparison along J standardZero zeroComparison A).prodCongr
    (LinearEquiv.refl ℂ _)

/-- ALL-object native map from the canonical standard localization arrow.
No ordinary base-change comparison is used to define this map. -/
def toCompact (A : Input) :
    (Representation.invariants (((along ⋙ J).obj A).ρ) ×
      Representation.invariants ((infinity.obj A).ρ)) →ₗ[ℂ]
        nativeF.obj (nativeH.compact A) :=
  (compactComparison A).symm.toLinearMap.comp
    ((connecting N A).comp
      (boundaryInvariantsComparison along J standardZero zeroComparison infinity A).toLinearMap)

-- Connected-lisse evaluation and positive slope yield native injection.
include R lisseMeaning slopeMeaning standardPositive in
omit [MonoidalCategory Local] [along.Monoidal] [J.Monoidal] [Abelian Native] [Abelian Standard] in
theorem toCompact_injective (A : Input) (hL : O.Lisse A)
    (hS : (O.curveData dual).Isoclinic A 1) :
    Function.Injective (toCompact along J nativeH nativeF standardH standardF
      standardZero zeroComparison infinity N compactComparison A) := by
  exact (compactComparison A).symm.injective.comp
    ((connecting_injective N R standardPositive A (lisseMeaning A hL) (slopeMeaning A hS)).comp
      (boundaryInvariantsComparison along J standardZero zeroComparison infinity A).injective)

-- Only exactness uses the ordinary/support comparison, with the old guards.
include R supportSquare in
omit [MonoidalCategory Local] [along.Monoidal] [J.Monoidal] [Abelian Native] [Abelian Standard] in
theorem toCompact_exact (A : Input) (hL : O.Lisse A)
    (hT : (O.curveData dual).TameZero A) (hS : (O.curveData dual).Isoclinic A 1) :
    LinearMap.range (toCompact along J nativeH nativeF standardH standardF
      standardZero zeroComparison infinity N compactComparison A) =
      LinearMap.ker (nativeF.map (nativeH.comparison A)).hom := by
  ext x
  change (∃ y, (compactComparison A).symm
    (connecting N A (boundaryInvariantsComparison along J standardZero zeroComparison infinity A y)) = x) ↔ _
  constructor
  · rintro ⟨y,hy⟩
    have hs : (standardF.map (standardH.comparison A)).hom
        (connecting N A (boundaryInvariantsComparison along J standardZero zeroComparison infinity A y)) = 0 :=
      (connecting_exact N R A).le ⟨_, rfl⟩
    have hc : compactComparison A x =
        connecting N A (boundaryInvariantsComparison along J standardZero zeroComparison infinity A y) := by
      rw [← hy, (compactComparison A).apply_symm_apply]
    have hq := congrArg (fun q => q x) (supportSquare A hL hT hS)
    change ordinaryComparison A hL hT hS ((nativeF.map (nativeH.comparison A)).hom x) =
      (standardF.map (standardH.comparison A)).hom (compactComparison A x) at hq
    change (nativeF.map (nativeH.comparison A)).hom x = 0
    apply (ordinaryComparison A hL hT hS).injective
    rw [hq, hc, hs, map_zero]
  · intro hx
    have hq := congrArg (fun q => q x) (supportSquare A hL hT hS)
    change ordinaryComparison A hL hT hS ((nativeF.map (nativeH.comparison A)).hom x) =
      (standardF.map (standardH.comparison A)).hom (compactComparison A x) at hq
    have hs : (standardF.map (standardH.comparison A)).hom (compactComparison A x) = 0 := by
      rw [← hq, hx, map_zero]
    have hr : compactComparison A x ∈ LinearMap.range (connecting N A) :=
      (connecting_exact N R A).ge hs
    obtain ⟨z,hz⟩ := hr
    refine ⟨(boundaryInvariantsComparison along J standardZero zeroComparison infinity A).symm z, ?_⟩
    rw [(boundaryInvariantsComparison along J standardZero zeroComparison infinity A).apply_symm_apply,
      hz, (compactComparison A).symm_apply_apply]

/-- Literal original BoundaryMaps with the canonical computed dual comparison. -/
def boundaryMaps : ArithmeticZeroFromSpecialization.BoundaryMaps
    (Ginf := Ginf) (O.curveData dual) nativeH nativeF dual (along ⋙ J) where
  infinity := infinity
  dual := dualComparison (along ⋙ J) dual ev O.Lisse bijective
  positiveSlope A hS := standardPositive A (slopeMeaning A hS)
  toCompact := toCompact along J nativeH nativeF standardH standardF standardZero
    zeroComparison infinity N compactComparison
  injective := toCompact_injective along J O dual standardCurve nativeH nativeF standardH standardF
    standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive compactComparison
  exact := toCompact_exact along J O dual standardCurve nativeH nativeF standardH standardF
    standardZero zeroComparison infinity N R compactComparison ordinaryComparison supportSquare

end PrimeGap182.TypeIII.ArithmeticBoundaryFromGuardedFiniteFiberOperations
