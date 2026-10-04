import TypeIIIRegularUnipotentBoundary
import TypeIIIGeometricCoreRank

/-!
# The geometric boundary from the individual source inertia models

Apply the general boundary sequence and restriction laws to the original
three-factor curve input. The zero-inertia invariant space is constructed
from two individual regular-unipotent source models and a trivial additive
source. The already proved positive slope at infinity removes that boundary
summand. This constructs the boundary model used by the geometric rank
theorem, rather than assuming the completed boundary identification.

General sheaf restriction and boundary-sequence laws, and the individual
source inertia models, remain explicit published inputs. A compatible
geometric realization and the Fourier-stalk comparison are not supplied by
this module. No final-rank or family-boundary equivalence is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace PrimeGap182.TypeIII.BoundaryFromSourceModels

open PublishedPhysicalConstruction PublishedMackey PublishedPhaseApplication
open RegularUnipotentBoundary GeometricCoreRank

universe u v w z a b
variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C)
  (F : C ⥤ ModuleCat.{w} ℂ)

/-- The general boundary sequence, for every eligible curve input. Its
maps lead into the original compact cohomology and comparison kernel.
The relative ordinary-cohomology exactness is only requested in the
tame-zero, slope-one class where constant conductor supports base change. -/
structure BoundarySequence where
  space : Input → ModuleCat.{w} ℂ
  toCompact : ∀ A, space A →ₗ[ℂ] F.obj (H.compact A)
  injective : ∀ A, D.Lisse A → D.Isoclinic A 1 → Function.Injective (toCompact A)
  exact : ∀ A, D.Lisse A → D.TameZero A → D.Isoclinic A 1 →
    LinearMap.range (toCompact A) = LinearMap.ker (F.map (H.comparison A)).hom

variable {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (S : BoundarySequence D H F)

/-- General inertia restriction, boundary-stalk decomposition, and the
vanishing of invariant vectors at positive slope. All laws quantify over
arbitrary curve inputs; none mentions the Kloosterman tensor recipe. -/
structure RestrictionData where
  zero : Input → FDRep ℂ G0
  infinity : Input → FDRep ℂ Ginf
  tensorZero : ∀ A B, Representation.Equiv (zero (D.tensor A B)).ρ
    (tensor (zero A) (zero B)).ρ
  dualZero : ∀ A, D.Lisse A → Representation.Equiv (zero (D.dual A)).ρ
    (dualRepresentation (zero A)).ρ
  boundary : ∀ A, D.Lisse A → S.space A ≃ₗ[ℂ]
    (Representation.invariants (zero A).ρ × Representation.invariants (infinity A).ρ)
  positiveSlope : ∀ A, D.Isoclinic A 1 → Representation.invariants (infinity A).ρ = ⊥

variable {D H F S} (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F S)
  (K : KloostermanInputData D)

/-- Restrict the literal original input and preserve its tensor/dual order. -/
def zeroInputEquiv : Representation.Equiv (Z.zero K.input).ρ
    (tensor (tensor (Z.zero K.first) (dualRepresentation (Z.zero K.second)))
      (Z.zero K.additive)).ρ :=
  (Z.tensorZero (D.tensor K.first (D.dual K.second)) K.additive).trans
    (tensorEquiv
      ((Z.tensorZero K.first (D.dual K.second)).trans
        (tensorEquiv (Representation.Equiv.refl _) (Z.dualZero K.second K.second_lisse)))
      (Representation.Equiv.refl _))

section ZeroSummand

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (W : FDRep ℂ Ginf) (h : Representation.invariants W.ρ = ⊥)

/-- Remove the vanishing infinity-invariant summand by an actual linear equivalence. -/
def discardInfinity : (V × Representation.invariants W.ρ) ≃ₗ[ℂ] V where
  toFun x := x.1
  invFun x := (x, 0)
  left_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact ((Submodule.mem_bot ℂ).mp (h ▸ x.2.property)).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ZeroSummand

variable (R : CurveRules D) {rho : Representation ℂ G0 (Fin 3 → ℂ)}
  (M : RegularModel rho)
  (hfirst : Representation.Equiv (Z.zero K.first).ρ rho)
  (hsecond : Representation.Equiv (Z.zero K.second).ρ rho)
  (hadditive : Representation.Equiv (Z.zero K.additive).ρ (Representation.trivial ℂ G0 ℂ))

/-- The full boundary identification is a conclusion of the source
models and general laws, including the vanishing infinity summand. -/
def boundaryIdentification : jordanThreeCentralizer ℂ ≃ₗ[ℂ] S.space K.input :=
  ((Z.boundary K.input (K.input_lisse R)).trans
    ((discardInfinity (Z.infinity K.input) (Z.positiveSlope K.input (K.input_slope_one R))).trans
      ((invariantsEquiv (zeroInputEquiv Z K)).trans
        (inputInvariantsEquiv M (Z.zero K.first) (Z.zero K.second) (Z.zero K.additive)
          hfirst hsecond hadditive)))).symm

/-- The original boundary injection now gives the exact geometric
boundary model required by the physical image-rank theorem. -/
def geometricBoundaryModel : GeometricBoundaryModel H F K.input where
  boundary := (S.toCompact K.input).comp
    (boundaryIdentification Z K R M hfirst hsecond hadditive).toLinearMap
  injective := (S.injective K.input (K.input_lisse R) (K.input_slope_one R)).comp
    (boundaryIdentification Z K R M hfirst hsecond hadditive).injective
  exact := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    exact S.exact K.input (K.input_lisse R) (K.input_tame R) (K.input_slope_one R)

include R M hfirst hsecond hadditive in
omit [Abelian C] in
theorem boundary_finrank : Module.finrank ℂ (S.space K.input) = 3 := by
  rw [← (boundaryIdentification Z K R M hfirst hsecond hadditive).finrank_eq,
    jordanThreeCentralizer_finrank]

include R M hfirst hsecond hadditive in
/-- Rank six for the same physical image, with individual source models
and general geometric laws instead of a supplied boundary identification. -/
theorem core_rank_six_from_sources
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (point : Point) (V : GeometricFiberRules D H F point) :
    Module.finrank ℂ (F.obj (parabolicCore H K.input)) = 6 :=
  core_rank_six K R point V (geometricBoundaryModel Z K R M hfirst hsecond hadditive)

end PrimeGap182.TypeIII.BoundaryFromSourceModels

#print axioms PrimeGap182.TypeIII.BoundaryFromSourceModels.zeroInputEquiv
#print axioms PrimeGap182.TypeIII.BoundaryFromSourceModels.discardInfinity
#print axioms PrimeGap182.TypeIII.BoundaryFromSourceModels.boundaryIdentification
#print axioms PrimeGap182.TypeIII.BoundaryFromSourceModels.geometricBoundaryModel
#print axioms PrimeGap182.TypeIII.BoundaryFromSourceModels.boundary_finrank
#print axioms PrimeGap182.TypeIII.BoundaryFromSourceModels.core_rank_six_from_sources
