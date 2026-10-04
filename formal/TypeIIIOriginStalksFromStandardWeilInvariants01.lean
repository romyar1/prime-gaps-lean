import TypeIIIStandardP1BoundaryPrimitives03
import TypeIIIArithmeticSourcesFromOrigin

/-!
# Origin invariant stalks computed from the same standard Weil action

The fiber is the invariant subspace of the literal standard origin
representation. The invertible residue Frobenius is the restriction of
B.originWeil's chosen geometric Frobenius, with covariance inherited from
that SAME Weil data. This is an exact OriginStalks construction for all
ordinary line objects; no OriginStalks provider, scalar comparison, Tate
comparison, field-extension Frobenius law, or interpretation existence
is assumed or derived. In a genuine interpreted model this describes the
ordinary j_* invariant stalk at zero, rather than the zero stalk of j!.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.OriginStalksFromStandardWeilInvariants
open ArithmeticSourcesFromOrigin ArithmeticBoundaryFromInvariantFunctors
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open ArithmeticSourceMaps StartingSourceMaps LocalWeilAction
universe u v g nu mu

section InvariantStalks
variable {Line : Type u} [Category.{v} Line] {G : Type g} [Group G]
  (J : Line ⥤ FDRep ℂ G) (phi : G →* G) (W : LocalWeilAction.Data J phi)

/-- Exact old invariant-stalk interface, computed from ONE same Weil action. -/
def invariantStalks : ArithmeticSourcesFromOrigin.OriginStalks.{u,0} Line where
  fiber A := ModuleCat.of ℂ (Representation.invariants (J.obj A).ρ)
  frobenius A := ArithmeticBoundaryFromInvariantFunctors.invariantAction
    (J.obj A) (W.localFrobenius.action A) phi (W.covariance A)

@[simp] theorem invariantStalks_fiber (A : Line) :
    (invariantStalks J phi W).fiber A =
      ModuleCat.of ℂ (Representation.invariants (J.obj A).ρ) := rfl

/-- Every-object covariance is inherited; no inertia-surjectivity is needed. -/
theorem nearby_covariance (A : Line) (q : G) (x : (J.obj A).V) :
    W.localFrobenius.action A ((J.obj A).ρ q x) =
      (J.obj A).ρ (phi q) (W.localFrobenius.action A x) := W.covariance A q x

@[simp] theorem invariantStalks_frobenius_val (A : Line)
    (x : (invariantStalks J phi W).fiber A) :
    ((invariantStalks J phi W).frobenius A x).val =
      W.localFrobenius.action A x.val := rfl

@[simp] theorem invariantStalks_inverse_val (A : Line)
    (x : (invariantStalks J phi W).fiber A) :
    (((invariantStalks J phi W).frobenius A).symm x).val =
      (W.localFrobenius.action A).symm x.val := rfl

@[simp] theorem invariantStalks_left_inv (A : Line)
    (x : (invariantStalks J phi W).fiber A) :
    ((invariantStalks J phi W).frobenius A).symm
      ((invariantStalks J phi W).frobenius A x) = x :=
  ((invariantStalks J phi W).frobenius A).symm_apply_apply x

@[simp] theorem invariantStalks_right_inv (A : Line)
    (x : (invariantStalks J phi W).fiber A) :
    (invariantStalks J phi W).frobenius A
      (((invariantStalks J phi W).frobenius A).symm x) = x :=
  ((invariantStalks J phi W).frobenius A).apply_symm_apply x
end InvariantStalks

section LiteralSource
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (fiberScheme E) ⥤ C (AlgebraicGeometry.Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,g,0} S)
  (D : FaithfulArithmeticOperations C U F nativeCompact S)
  (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E]
  (h2 : (2 : E) ≠ 0)

/-- The literal local-input pull, standard curve realization, then SAME origin. -/
def sourceOriginFunctor : C (affineLine K) ⥤ FDRep ℂ (B.OriginGroup E h2) :=
  (U.pull (localInputMorphism K E)) ⋙ D.curveRealization E h2 ⋙ B.origin E h2

/-- Exact old OriginStalks type for ordinary affine-line objects. Numerical and
finite-field guards are unchanged; no selected finished primitive is a premise. -/
def originStalks : ArithmeticSourcesFromOrigin.OriginStalks.{0,0} (C (affineLine K)) where
  fiber A := ModuleCat.of ℂ (Representation.invariants
    ((B.origin E h2).obj ((D.curveRealization E h2).obj
      ((U.pull (localInputMorphism K E)).obj A))).ρ)
  frobenius A := ArithmeticBoundaryFromInvariantFunctors.invariantAction
    ((B.origin E h2).obj ((D.curveRealization E h2).obj
      ((U.pull (localInputMorphism K E)).obj A)))
    ((B.originWeil E h2).localFrobenius.action
      ((D.curveRealization E h2).obj ((U.pull (localInputMorphism K E)).obj A)))
    (B.originConjugation E h2)
    ((B.originWeil E h2).covariance
      ((D.curveRealization E h2).obj ((U.pull (localInputMorphism K E)).obj A)))

@[simp] theorem originStalks_fiber (A : C (affineLine K)) :
    (originStalks C U F nativeCompact B D K E h2).fiber A =
      ModuleCat.of ℂ (Representation.invariants
        ((sourceOriginFunctor C U F nativeCompact B D K E h2).obj A).ρ) := rfl

/-- SAME standard chosen geometric Frobenius on every actual source input. -/
theorem source_covariance (A : C (affineLine K)) (q : B.OriginGroup E h2)
    (x : ((sourceOriginFunctor C U F nativeCompact B D K E h2).obj A).V) :
    (B.originWeil E h2).localFrobenius.action
      ((D.curveRealization E h2).obj ((U.pull (localInputMorphism K E)).obj A))
      (((sourceOriginFunctor C U F nativeCompact B D K E h2).obj A).ρ q x) =
    ((sourceOriginFunctor C U F nativeCompact B D K E h2).obj A).ρ
      ((B.originConjugation E h2) q)
      ((B.originWeil E h2).localFrobenius.action
        ((D.curveRealization E h2).obj ((U.pull (localInputMorphism K E)).obj A)) x) :=
  (B.originWeil E h2).covariance
    ((D.curveRealization E h2).obj ((U.pull (localInputMorphism K E)).obj A)) q x

@[simp] theorem originStalks_frobenius_val (A : C (affineLine K))
    (x : (originStalks C U F nativeCompact B D K E h2).fiber A) :
    ((originStalks C U F nativeCompact B D K E h2).frobenius A x).val =
      (B.originWeil E h2).localFrobenius.action
        ((D.curveRealization E h2).obj ((U.pull (localInputMorphism K E)).obj A)) x.val := rfl

@[simp] theorem originStalks_inverse_val (A : C (affineLine K))
    (x : (originStalks C U F nativeCompact B D K E h2).fiber A) :
    (((originStalks C U F nativeCompact B D K E h2).frobenius A).symm x).val =
      ((B.originWeil E h2).localFrobenius.action
        ((D.curveRealization E h2).obj ((U.pull (localInputMorphism K E)).obj A))).symm
          x.val := rfl

@[simp] theorem originStalks_left_inv (A : C (affineLine K))
    (x : (originStalks C U F nativeCompact B D K E h2).fiber A) :
    ((originStalks C U F nativeCompact B D K E h2).frobenius A).symm
      ((originStalks C U F nativeCompact B D K E h2).frobenius A x) = x :=
  ((originStalks C U F nativeCompact B D K E h2).frobenius A).symm_apply_apply x

@[simp] theorem originStalks_right_inv (A : C (affineLine K))
    (x : (originStalks C U F nativeCompact B D K E h2).fiber A) :
    (originStalks C U F nativeCompact B D K E h2).frobenius A
      (((originStalks C U F nativeCompact B D K E h2).frobenius A).symm x) = x :=
  ((originStalks C U F nativeCompact B D K E h2).frobenius A).apply_symm_apply x
end LiteralSource
end PrimeGap182.TypeIII.OriginStalksFromStandardWeilInvariants
