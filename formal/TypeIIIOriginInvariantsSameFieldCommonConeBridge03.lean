import TypeIIIOriginStalksFromStandardWeilInvariants01
import TypeIIINativeCommonArithmeticTraitWeilCone04
import TypeIIIArithmeticBoundaryStandardLocalizationReindex07

/-!
# SAME-field invariant/Frobenius comparison for the computed common cone

Only genuine group restriction through an equivalence is changed. The existing
invariantsChange supplies the linear equivalence; its underlying map is literal
identity. Frobenius comes from the SAME independently standard Weil action.
This conditional pure bridge does not supply finite-extension comparison,
Frobenius-power laws, Kl3 or AS identity actions, or originActions role606.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.OriginInvariantsSameFieldCommonConeBridge
open ArithmeticSourcesFromOrigin LocalWeilAction
open OriginStalksFromStandardWeilInvariants
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open ArithmeticSourceMaps StartingSourceMaps
universe u v us vs g gs nu mu

section GeneralRestriction
variable {Line : Type u} [Category.{v} Line]
  {StandardLine : Type us} [Category.{vs} StandardLine]
  {G : Type g} [Group G] {StandardG : Type gs} [Group StandardG]
  (realization : Line ⥤ StandardLine) (standardJ : StandardLine ⥤ FDRep ℂ StandardG)
  (standardPhi : StandardG →* StandardG) (standardD : Data standardJ standardPhi)
  (origin : G ≃* StandardG) {W : Type g} [Group W] (weil : W ≃* standardD.Weil)

/-- The computed restriction functor and Weil representation, with no provider. -/
def restrictedOriginStalks : ArithmeticSourcesFromOrigin.OriginStalks.{u,0} Line :=
  OriginStalksFromStandardWeilInvariants.invariantStalks
    (CanonicalLocalWeilFiberFromGroupDictionary.fiber realization standardJ origin)
    (CanonicalLocalWeilFiberFromGroupDictionary.conjugation standardPhi origin)
    (CanonicalLocalWeilFiberFromGroupDictionary.weilData realization standardJ
      standardPhi standardD origin weil)

/-- Reuse the prior genuine group-equivalence invariant comparison. -/
def invariantComparison (A : Line) :
    (restrictedOriginStalks realization standardJ standardPhi standardD origin weil).fiber A ≃ₗ[ℂ]
      (OriginStalksFromStandardWeilInvariants.invariantStalks
        standardJ standardPhi standardD).fiber (realization.obj A) :=
  ArithmeticBoundaryStandardLocalizationReindex.invariantsChange origin
    (standardJ.obj (realization.obj A))

@[simp] theorem invariantComparison_val (A : Line)
    (x : (restrictedOriginStalks realization standardJ standardPhi standardD origin weil).fiber A) :
    (invariantComparison realization standardJ standardPhi standardD origin weil A x).val =
      x.val := rfl

@[simp] theorem invariantComparison_inverse_val (A : Line)
    (x : (OriginStalksFromStandardWeilInvariants.invariantStalks
      standardJ standardPhi standardD).fiber (realization.obj A)) :
    ((invariantComparison realization standardJ standardPhi standardD origin weil A).symm x).val =
      x.val := rfl

/-- ALL-object SAME chosen-Frobenius square; no full-Weil recognition is added. -/
theorem frobenius_square (A : Line)
    (x : (restrictedOriginStalks realization standardJ standardPhi standardD origin weil).fiber A) :
    invariantComparison realization standardJ standardPhi standardD origin weil A
      ((restrictedOriginStalks realization standardJ standardPhi standardD origin weil).frobenius A x) =
    (OriginStalksFromStandardWeilInvariants.invariantStalks standardJ standardPhi standardD).frobenius
      (realization.obj A)
      (invariantComparison realization standardJ standardPhi standardD origin weil A x) := by
  apply Subtype.ext
  change standardD.representation (realization.obj A)
    (weil (weil.symm standardD.frobenius)) x.val =
      standardD.representation (realization.obj A) standardD.frobenius x.val
  rw [MulEquiv.apply_symm_apply]

/-- Inverse Frobenius uses the same inverse Weil element. -/
theorem inverse_frobenius_square (A : Line)
    (x : (restrictedOriginStalks realization standardJ standardPhi standardD origin weil).fiber A) :
    invariantComparison realization standardJ standardPhi standardD origin weil A
      (((restrictedOriginStalks realization standardJ standardPhi standardD origin weil).frobenius A).symm x) =
    ((OriginStalksFromStandardWeilInvariants.invariantStalks standardJ standardPhi standardD).frobenius
      (realization.obj A)).symm
      (invariantComparison realization standardJ standardPhi standardD origin weil A x) := by
  apply Subtype.ext
  change standardD.representation (realization.obj A)
    (weil ((weil.symm standardD.frobenius)⁻¹)) x.val =
      standardD.representation (realization.obj A) standardD.frobenius⁻¹ x.val
  rw [map_inv, MulEquiv.apply_symm_apply]
end GeneralRestriction

section LiteralCommonSource
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (fiberScheme E) ⥤ C (AlgebraicGeometry.Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (D : FaithfulArithmeticOperations C U F nativeCompact S)
  (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
  (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E] (h2 : (2 : E) ≠ 0)

/-- Exact original interface at the computed common native origin choices. -/
def commonOriginStalks : ArithmeticSourcesFromOrigin.OriginStalks.{0,0} (C (affineLine K)) :=
  OriginStalksFromStandardWeilInvariants.invariantStalks
    (NativeCommonArithmeticTraitWeilCone.fiber.{0,mu,nu,g} K E B originTrait h2
      ((U.pull (localInputMorphism K E)) ⋙ D.curveRealization E h2))
    (NativeCommonArithmeticTraitWeilCone.conjugation.{nu,g} K E B originTrait h2)
    (NativeCommonArithmeticTraitWeilCone.weilData.{0,mu,nu,g} K E B originTrait h2
      ((U.pull (localInputMorphism K E)) ⋙ D.curveRealization E h2))

/-- Native group labels change, while the standard input and vectors remain SAME. -/
def commonInvariantComparison (A : C (affineLine K)) :
    (commonOriginStalks.{g,nu,mu} C U F nativeCompact B D originTrait K E h2).fiber A ≃ₗ[ℂ]
      (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2).fiber A :=
  invariantComparison ((U.pull (localInputMorphism K E)) ⋙ D.curveRealization E h2)
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K E B originTrait h2)
    (NativeCommonArithmeticTraitWeilCone.weilEquiv.{nu,g} E B h2) A

@[simp] theorem commonInvariantComparison_val (A : C (affineLine K))
    (x : (commonOriginStalks.{g,nu,mu} C U F nativeCompact B D originTrait K E h2).fiber A) :
    (commonInvariantComparison C U F nativeCompact B D originTrait K E h2 A x).val = x.val := rfl

@[simp] theorem commonInvariantComparison_inverse_val (A : C (affineLine K))
    (x : (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2).fiber A) :
    ((commonInvariantComparison.{g,nu,mu} C U F nativeCompact B D originTrait K E h2 A).symm x).val =
      x.val := rfl

/-- Exact SAME-field Frobenius comparison, with all original finite-E/h2 guards. -/
theorem common_frobenius_square (A : C (affineLine K))
    (x : (commonOriginStalks.{g,nu,mu} C U F nativeCompact B D originTrait K E h2).fiber A) :
    commonInvariantComparison C U F nativeCompact B D originTrait K E h2 A
      ((commonOriginStalks C U F nativeCompact B D originTrait K E h2).frobenius A x) =
    (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2).frobenius A
      (commonInvariantComparison C U F nativeCompact B D originTrait K E h2 A x) :=
  frobenius_square ((U.pull (localInputMorphism K E)) ⋙ D.curveRealization E h2)
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K E B originTrait h2)
    (NativeCommonArithmeticTraitWeilCone.weilEquiv.{nu,g} E B h2) A x

/-- Exact inverse-Frobenius comparison on the SAME invariant subspaces. -/
theorem common_inverse_frobenius_square (A : C (affineLine K))
    (x : (commonOriginStalks.{g,nu,mu} C U F nativeCompact B D originTrait K E h2).fiber A) :
    commonInvariantComparison C U F nativeCompact B D originTrait K E h2 A
      (((commonOriginStalks C U F nativeCompact B D originTrait K E h2).frobenius A).symm x) =
    ((OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2).frobenius A).symm
      (commonInvariantComparison C U F nativeCompact B D originTrait K E h2 A x) :=
  inverse_frobenius_square ((U.pull (localInputMorphism K E)) ⋙ D.curveRealization E h2)
    (B.origin E h2) (B.originConjugation E h2) (B.originWeil E h2)
    (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K E B originTrait h2)
    (NativeCommonArithmeticTraitWeilCone.weilEquiv.{nu,g} E B h2) A x
end LiteralCommonSource
end PrimeGap182.TypeIII.OriginInvariantsSameFieldCommonConeBridge
