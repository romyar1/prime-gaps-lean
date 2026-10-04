import TypeIIIOriginInvariantsSameFieldCommonConeBridge03
import TypeIIIOriginFrobeniusPowerFromInertiaTwistedLiftRoot02

/-!
Pure finite-constant transport from individual nearby representation and Weil
comparisons. The coefficient-field map is the literal Laurent map preserving
positive T. The invariant comparison is computed by the existing invariants
functor and group-equivalence comparison. A Frobenius lift may map to inertia
times a degree power; no equality of arbitrary chosen lifts is asserted.

The standard finite-constant nearby comparison and its Weil square remain
explicit individual theorem/dictionary operands. This module neither constructs
a continuous-adic model nor proves prime-field Kl3/AS actions or role606 Rules.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.OriginFiniteConstantInvariantFrobeniusTransport
open ArithmeticSourcesFromOrigin LocalWeilAction ArithmeticSourceMaps StartingSourceMaps
open OriginStalksFromStandardWeilInvariants
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open ExactInverseImagesToDerived
universe u v ue ve g ge nu mu

section LiteralConstantExtension
variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- The literal coefficient extension on Gm, retaining positive T. -/
def constantExtensionHom : FiberRing K →ₐ[K] FiberRing E where
  toRingHom := LaurentPolynomial.eval₂
    (LaurentPolynomial.C.comp (algebraMap K E)) (PhysicalTorusLaurent.variableUnit E)
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C c) = _
    rw [LaurentPolynomial.eval₂_C]
    rfl

@[simp] theorem constantExtensionHom_C (c : K) :
    constantExtensionHom K E (LaurentPolynomial.C c) =
      LaurentPolynomial.C (algebraMap K E c) := LaurentPolynomial.eval₂_C _ _ c

@[simp] theorem constantExtensionHom_T (n : ℤ) :
    constantExtensionHom K E (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T n) = _
  rw [LaurentPolynomial.eval₂_T]
  exact PhysicalTorusLaurent.variableUnit_pow E n

theorem constantExtension_localInputHom :
    (constantExtensionHom K E).comp (localInputHom K K) = localInputHom K E := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, localInputHom, MvPolynomial.aeval_X]
  change constantExtensionHom K E (LaurentPolynomial.T 1) = LaurentPolynomial.T 1
  exact constantExtensionHom_T K E 1

def constantExtensionMorphism : fiberScheme E ⟶ fiberScheme K :=
  Spec.map (CommRingCat.ofHom (constantExtensionHom K E).toRingHom)

theorem constantExtension_localInputMorphism :
    constantExtensionMorphism K E ≫ localInputMorphism K K = localInputMorphism K E := by
  dsimp only [constantExtensionMorphism, localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (constantExtension_localInputHom K E))

variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)

/-- SAME ordinary compositor and exact scheme equality; no base-change law. -/
def sourceConstantPullIso :
    U.pull (localInputMorphism K K) ⋙ U.pull (constantExtensionMorphism K E) ≅
      U.pull (localInputMorphism K E) :=
  U.composition (constantExtensionMorphism K E) (localInputMorphism K K) ≪≫
    eqToIso (congrArg U.pull (constantExtension_localInputMorphism K E))
end LiteralConstantExtension

section GeneralNearbyComparison
variable {BaseLine : Type u} [Category.{v} BaseLine]
  {ExtensionLine : Type ue} [Category.{ve} ExtensionLine]
  {BaseGroup : Type g} [Group BaseGroup] {ExtensionGroup : Type ge} [Group ExtensionGroup]
  (pull : BaseLine ⥤ ExtensionLine)
  (baseJ : BaseLine ⥤ FDRep ℂ BaseGroup) (extensionJ : ExtensionLine ⥤ FDRep ℂ ExtensionGroup)
  (basePhi : BaseGroup →* BaseGroup) (extensionPhi : ExtensionGroup →* ExtensionGroup)
  (baseWeil : Data baseJ basePhi) (extensionWeil : Data extensionJ extensionPhi)
  (inertia : ExtensionGroup ≃* BaseGroup)
  (nearby : pull ⋙ extensionJ ≅ baseJ ⋙ Action.res (FGModuleCat ℂ) inertia.toMonoidHom)

/-- The individual nearby NatIso maps invariants; existing invariantsChange
then changes geometric group labels. No invariant-stalk provider is an input. -/
def comparison (A : BaseLine) :
    (invariantStalks extensionJ extensionPhi extensionWeil).fiber (pull.obj A) ≃ₗ[ℂ]
      (invariantStalks baseJ basePhi baseWeil).fiber A :=
  (((Rep.invariantsFunctor ℂ ExtensionGroup).mapIso
    ((forget₂ (FDRep ℂ ExtensionGroup) (Rep ℂ ExtensionGroup)).mapIso
      (nearby.app A))).toLinearEquiv).trans
    (ArithmeticBoundaryStandardLocalizationReindex.invariantsChange inertia (baseJ.obj A))

@[simp] theorem comparison_val (A : BaseLine)
    (x : (invariantStalks extensionJ extensionPhi extensionWeil).fiber (pull.obj A)) :
    (comparison pull baseJ extensionJ basePhi extensionPhi baseWeil extensionWeil
      inertia nearby A x).val = (nearby.hom.app A).hom.hom x.val := rfl

variable (weilMap : extensionWeil.Weil →* baseWeil.Weil)
  (weilSquare : ∀ A w x,
    (nearby.hom.app A).hom.hom (extensionWeil.representation (pull.obj A) w x) =
      baseWeil.representation A (weilMap w) ((nearby.hom.app A).hom.hom x))

include weilSquare in
/-- Only a group-level lift identity and the ALL-Weil nearby action square
are used. The inertia factor disappears on the computed invariant stalk. -/
theorem comparison_frobenius_pow (A : BaseLine) (degree : ℕ) (q : BaseGroup)
    (frobeniusImage : weilMap extensionWeil.frobenius =
      baseWeil.inertia q * baseWeil.frobenius ^ degree)
    (x : (invariantStalks extensionJ extensionPhi extensionWeil).fiber (pull.obj A)) :
    comparison pull baseJ extensionJ basePhi extensionPhi baseWeil extensionWeil inertia nearby A
      ((invariantStalks extensionJ extensionPhi extensionWeil).frobenius (pull.obj A) x) =
    ((invariantStalks baseJ basePhi baseWeil).frobenius A ^ degree)
      (comparison pull baseJ extensionJ basePhi extensionPhi baseWeil extensionWeil inertia nearby A x) := by
  apply Subtype.ext
  change (nearby.hom.app A).hom.hom
      (extensionWeil.representation (pull.obj A) extensionWeil.frobenius x.val) = _
  rw [weilSquare, frobeniusImage]
  exact OriginFrobeniusPowerFromInertiaTwistedLift.representation_inertia_frobenius_pow
    baseJ basePhi baseWeil A q degree
      (comparison pull baseJ extensionJ basePhi extensionPhi baseWeil extensionWeil inertia nearby A x)
end GeneralNearbyComparison

section ExactCommonGroupMap
variable {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
  (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
  (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0)

/-- Both actual common-group dictionaries occur, including the SAME chosen
K/K coefficient-field equivalence; it is not silently replaced by identity. -/
def commonInertiaMap : B.OriginGroup E h2E ≃* B.OriginGroup K h2K :=
  (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K E B originTrait h2E).symm.trans
    (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K K B originTrait h2K)

@[simp] theorem commonInertiaMap_origin (x : NativeCommonArithmeticTraitWeilCone.CommonOrigin.{g} K) :
    commonInertiaMap.{g,nu} B originTrait K E h2K h2E
      (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K E B originTrait h2E x) =
    NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K K B originTrait h2K x := by
  exact MulEquiv.symm_apply_apply
    (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K E B originTrait h2E) x
      |> congrArg (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g} K K B originTrait h2K)
end ExactCommonGroupMap
end PrimeGap182.TypeIII.OriginFiniteConstantInvariantFrobeniusTransport
