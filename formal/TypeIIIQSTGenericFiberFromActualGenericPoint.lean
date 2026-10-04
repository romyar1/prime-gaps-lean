import TypeIIIQSTPrimitiveBridgesFromCommonKatzConstruction
import TypeIIINativePointFiberFromUniversalGeometricFibers
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The actual generic Gm point and the SAME finite ordinary fiber

The fraction-field point of the original Laurent coordinate ring is
proved dominant. Ordinary H0 of SAME-U derived pullback is evaluated by
the existing ALL-field geometric coefficient fiber. Coordinates from
an actual finite basis provide a ModuleCat0 object for the original
Background interface, without changing its intrinsic dimension.
No generic-rank theorem, selected fiber comparison, extra finiteness law
or whole Background is assumed. Continuous-adic interpretation remains
external to this conditional construction.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.QSTGenericFiberFromActualGenericPoint
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward

variable (K : Type) [Field K]

abbrev GenericField := FractionRing (LaurentPolynomial K)

/-- The actual fraction-field point of the original Gm scheme. -/
def genericPoint : Spec (.of (GenericField K)) ⟶ ArithmeticSourceMaps.fiberScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial K) (GenericField K)))

theorem genericPoint_dominant : IsDominant (genericPoint K) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap (LaurentPolynomial K) (GenericField K)))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (LaurentPolynomial K) (GenericField K))]
  exact bot_le

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)

local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- The actual generic fiber is ordinary H0 after SAME-U derived pullback. -/
def rawGenericFiber : Bounded C (ArithmeticSourceMaps.fiberScheme K) ⥤ ModuleCat.{mu} ℂ :=
  (QSTAdmissibilityFromBoundedDerived.boundedProperty (C (ArithmeticSourceMaps.fiberScheme K))).ι ⋙
    U.derivedPull (genericPoint K) ⋙
      DerivedCategory.homologyFunctor (C (Spec (.of (GenericField K)))) 0 ⋙
        G.fiber (GenericField K)

instance rawGenericFinite (A : Bounded C (ArithmeticSourceMaps.fiberScheme K)) :
    FiniteDimensional ℂ ((rawGenericFiber K C U G).obj A) :=
  G.finite (GenericField K) _

/-- The original small-universe module is coordinates of the actual fiber. -/
def genericFiber (A : Bounded C (ArithmeticSourceMaps.fiberScheme K)) : ModuleCat.{0} ℂ :=
  ModuleCat.of ℂ (Fin (Module.finrank ℂ ((rawGenericFiber K C U G).obj A)) → ℂ)

instance genericFinite (A : Bounded C (ArithmeticSourceMaps.fiberScheme K)) :
    FiniteDimensional ℂ (genericFiber K C U G A) := by
  dsimp [genericFiber]
  infer_instance

/-- A genuine coefficient-basis equivalence; no independently chosen module
or selected comparison is supplied to resolve the universe difference. -/
def coordinateBasis (A : Bounded C (ArithmeticSourceMaps.fiberScheme K)) :
    (rawGenericFiber K C U G).obj A ≃ₗ[ℂ] genericFiber K C U G A :=
  (Module.finBasis ℂ ((rawGenericFiber K C U G).obj A)).equivFun

theorem genericFiber_finrank (A : Bounded C (ArithmeticSourceMaps.fiberScheme K)) :
    Module.finrank ℂ (genericFiber K C U G A) =
      Module.finrank ℂ ((rawGenericFiber K C U G).obj A) :=
  (coordinateBasis K C U G A).finrank_eq.symm

/-- Isomorphic bounded Gm objects have the same actual generic fiber rank. -/
theorem genericFiber_finrank_iso {A B : Bounded C (ArithmeticSourceMaps.fiberScheme K)}
    (e : A ≅ B) :
    Module.finrank ℂ (genericFiber K C U G A) = Module.finrank ℂ (genericFiber K C U G B) := by
  rw [genericFiber_finrank, genericFiber_finrank]
  exact ((rawGenericFiber K C U G).mapIso e).toLinearEquiv.finrank_eq

end PrimeGap182.TypeIII.QSTGenericFiberFromActualGenericPoint
