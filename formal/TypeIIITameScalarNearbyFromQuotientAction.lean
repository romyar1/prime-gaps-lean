import TypeIIIGenericOriginFractionFieldCoordinates
import TypeIIIScalarLocalPropagationFromFilteredTraits

/-!
# Full tame scalar nearby comparison from the actual quotient action

A scalar-origin automorphism that acts trivially modulo wild inertia acts
identically on EVERY wild-trivial representation. This is proved on actual
operators, and yields a full identity-underlying-module representation iso.
The ALL-field geometric tame-quotient theorem is separately precise group
model data. Scalar and constant-field comparisons are the SAME general
filtered trait families used by the source-local application, not selected
primitive equivalences. ANY coefficient functor can transport the resulting
iso; the intended one is computed from the fixed Padic/complex field equiv.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.TameScalarNearbyFromQuotientAction
open ExactInverseImagesToDerived PrimitiveRamificationFromGeneralKatzTheory
open ScalarLocalPropagationFromFilteredTraits GenericOriginFractionFieldCoordinates

variable {k H : Type} [Field k] [Group H]

/-- Actual action operators agree when the automorphism is identity modulo P. -/
theorem restricted_tame_action (P : Subgroup H) (alpha : H ≃* H)
    (quotient : ∀ g, ∃ w : P, alpha g = g * w.val)
    (V : FDRep k H) (tame : ∀ w : P, V.ρ w.val = 1) (g : H) :
    FDRep.ρ ((Action.res (FGModuleCat k) alpha.toMonoidHom).obj V) g = V.ρ g := by
  change V.ρ (alpha g) = V.ρ g
  obtain ⟨w, hw⟩ := quotient g
  rw [hw, map_mul, tame w, mul_one]

/-- Full identity-module isomorphism; invariants are not substituted for V. -/
def restrictedTameIso (P : Subgroup H) (alpha : H ≃* H)
    (quotient : ∀ g, ∃ w : P, alpha g = g * w.val)
    (V : FDRep k H) (tame : ∀ w : P, V.ρ w.val = 1) :
    (Action.res (FGModuleCat k) alpha.toMonoidHom).obj V ≅ V :=
by
  let f : ((Action.res (FGModuleCat k) alpha.toMonoidHom).obj V).V ≅ V.V := by
    change V.V ≅ V.V
    exact Iso.refl _
  refine Action.mkIso f ?_
  intro g
  apply FGModuleCat.hom_ext
  change V.ρ (alpha g) = V.ρ g
  exact restricted_tame_action P alpha quotient V tame g

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (M : LocalRealization C)
  (T : ∀ (F : Type) [Field F], FDRep (PadicAlgCl 2) (M.originGroup F) ⥤
    FDRep ℂ (M.originGroup F))
  (scalarOriginAutomorphism : ∀ (F : Type) [Field F], (2 : F) ≠ 0 →
    Fˣ → M.originGroup F ≃* M.originGroup F)
  (scalarOriginComparison : ∀ (F : Type) [Field F] (hF : (2 : F) ≠ 0) (a : Fˣ),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙
      U.pull (ArithmeticSourceMaps.scalarMorphism F F a) ⋙ M.origin F ≅
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
      Action.res (FGModuleCat (PadicAlgCl 2)) (scalarOriginAutomorphism F hF a).toMonoidHom)
  (scalarOriginTameQuotient : ∀ (F : Type) [Field F] (hF : (2 : F) ≠ 0)
    (a : Fˣ) (g : M.originGroup F), ∃ w : M.wildOrigin F,
      scalarOriginAutomorphism F hF a g = g * w.val)

include scalarOriginComparison scalarOriginTameQuotient in
/-- ALL Gm-lisse tame objects get the full scalar nearby comparison. -/
def scalarNearbyIso (F : Type) [Field F] (hF : (2 : F) ≠ 0) (a : Fˣ)
    (A : C (ArithmeticSourceMaps.fiberScheme F))
    (hL : L (ArithmeticSourceMaps.fiberScheme F) A)
    (hA : wildTrivial (M.wildOrigin F) ((M.origin F).obj A)) :
    (M.origin F ⋙ T F).obj ((U.pull (ArithmeticSourceMaps.scalarMorphism F F a)).obj A) ≅
      (M.origin F ⋙ T F).obj A :=
  (T F).mapIso (((scalarOriginComparison F hF a).app ⟨A, hL⟩) ≪≫
    restrictedTameIso (M.wildOrigin F) (scalarOriginAutomorphism F hF a)
      (scalarOriginTameQuotient F hF a) ((M.origin F).obj A) hA)

variable [∀ X, (L X).IsClosedUnderIsomorphisms]
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (baseOriginHom : ∀ (F B : Type) [Field F] [Field B] [Algebra F B],
    (2 : F) ≠ 0 → (2 : B) ≠ 0 → M.originGroup B →* M.originGroup F)
  (baseOriginWild : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0) (g : M.wildOrigin B),
    baseOriginHom F B hF hB g.val ∈ M.wildOrigin F)
  (baseOriginComparison : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ U.pull (baseGmMorphism F B) ⋙ M.origin B ≅
      (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
        Action.res (FGModuleCat (PadicAlgCl 2)) (baseOriginHom F B hF hB))

include lissePull baseOriginWild baseOriginComparison scalarOriginComparison scalarOriginTameQuotient in
/-- Original parameter-unit scalars compare through the SAME fraction field. -/
def genericScalarNearbyEquiv (K : Type) [Field K] (hK : (2 : K) ≠ 0)
    (c : (GenericCurvePullback.ParameterRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K))
    (hL : SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A)
    (hA : GloballyLisseLineRamificationFromKatz.tameZero C U L M K A) :
    Representation.Equiv
      ((genericZeroFunctor K C U (fun F => M.originGroup F)
          (fun F => M.origin F ⋙ T F)).obj
        ((U.pull (GeometricOriginFromScalar.genericScalarMorphism K c)).obj A)).ρ
      ((primitiveOriginFunctor K C U (fun F => M.originGroup F)
          (fun F => M.origin F ⋙ T F)).obj A).ρ := by
  let F := ParameterFractionField K
  have hF : (2 : F) ≠ 0 := by
    have hi := (algebraMap K F).injective.ne hK
    simpa only [map_ofNat, map_zero] using hi
  let B := (U.pull (ArithmeticSourceMaps.localInputMorphism K F)).obj A
  have hLB : L (ArithmeticSourceMaps.fiberScheme F) B :=
    (L _).prop_of_iso (localInputBaseIso K F C U A).symm (lissePull _ _ hL)
  have hTB : wildTrivial (M.wildOrigin F) ((M.origin F).obj B) :=
    wildTrivial_iso _ ((M.origin F).mapIso (localInputBaseIso K F C U A)).symm
      (base_tame K F C U L M baseOriginHom baseOriginWild baseOriginComparison
        hK hF _ hL hA.2)
  exact TensorListRepresentation.equivOfIso
    (((genericScalarOriginIso K C U (fun E => M.originGroup E)
        (fun E => M.origin E ⋙ T E) c).app A) ≪≫
      scalarNearbyIso C U L M T scalarOriginAutomorphism scalarOriginComparison scalarOriginTameQuotient
        F hF (parameterFractionUnit K c) B hLB hTB)

section OriginalPullbackData
variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (p : ℕ) [Fact p.Prime] (hK : (2 : ZMod p) ≠ 0)
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

include lissePull baseOriginWild baseOriginComparison scalarOriginComparison scalarOriginTameQuotient in
/-- Exact original PullbackData, with primitiveZero computed on the SAME F. -/
def originPullbackData : GeometricOriginFromScalar.PullbackData (ZMod p)
    (fun f => U.pull f)
    (fun A => (genericZeroFunctor (ZMod p) C U (fun E => M.originGroup E)
      (fun E => M.origin E ⋙ T E)).obj A)
    (LinePurityFromStalks.geometry R
      (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p))) where
  primitiveZero A := (primitiveOriginFunctor (ZMod p) C U (fun E => M.originGroup E)
    (fun E => M.origin E ⋙ T E)).obj A
  scalarZero c A hL hA := genericScalarNearbyEquiv C U L M T
    scalarOriginAutomorphism scalarOriginComparison scalarOriginTameQuotient lissePull
    baseOriginHom baseOriginWild baseOriginComparison (ZMod p) hK c A hL hA
end OriginalPullbackData
end PrimeGap182.TypeIII.TameScalarNearbyFromQuotientAction
