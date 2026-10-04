import TypeIIIOriginStalkDataFromIndividualStandardOperations03
import TypeIIIOriginInvariantsSameFieldCommonConeBridge03

/-! The common native origin is computed from the SAME standard Weil action.
Only individual ordinary scalar/twist operation comparisons and independently
standard ALL-object operators are interpreted. No origin, StalkData,
ScalarStalkComparison, TateOriginRules or finished family provider is assumed. -/
noncomputable section
open CategoryTheory
open scoped MonoidalCategory TensorProduct
namespace PrimeGap182.TypeIII.CommonOriginStalkDataFromStandardOperations
open ArithmeticSourceMaps ArithmeticSourceTransport ArithmeticSourcesFromOrigin
open ArithmeticPrimitiveSources ArithmeticOriginFromScalar TensorListRepresentation
open RegularUnipotentBoundary ArithmeticBoundaryFromInvariantFunctors
open OriginInvariantsSameFieldCommonConeBridge
universe u i n s p ul il nl sl pl g gs

section StandardApplication
variable (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E]
  {Line : Type u} [Category.{ul} Line] {Input : Type i} [Category.{il} Input]
  {Local : Type n} [Category.{nl} Local]
  {Standard : Type s} [Category.{sl} Standard] [MonoidalCategory Standard]
  {G : Type g} [Group G] {StandardG : Type gs} [Group StandardG]
  {original : (StartingSourceMaps.sourceScheme K ⟶ StartingSourceMaps.affineLine K) → Line ⥤ Input}
  (P : Pullbacks (Local := Local) K E original) (R : Local ⥤ Standard)
  (standardJ : Standard ⥤ FDRep ℂ StandardG) [standardJ.Monoidal]
  (standardPhi : StandardG →* StandardG)
  (standardW : LocalWeilAction.Data standardJ standardPhi)
  (groupDictionary : G ≃* StandardG)
  {Weil : Type g} [Group Weil] (weilDictionary : Weil ≃* standardW.Weil)

abbrev commonJ := CanonicalLocalWeilFiberFromGroupDictionary.fiber R standardJ groupDictionary
abbrev commonPhi := CanonicalLocalWeilFiberFromGroupDictionary.conjugation standardPhi groupDictionary
abbrev commonW := CanonicalLocalWeilFiberFromGroupDictionary.weilData R standardJ
  standardPhi standardW groupDictionary weilDictionary
abbrev standardSource := P.specialized (localInputMorphism K E) ⋙ R

/-- Literal computed common-cone invariant stalks, with the same O32 action. -/
def computedOrigin : OriginStalks.{u,0} Line :=
  restrictedOriginStalks (standardSource K E P R) standardJ standardPhi standardW
    groupDictionary weilDictionary

/-- The gated SAME-group invariant comparison is computed, not a new premise. -/
def computedOriginComparison (A : Line) :
    (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).fiber A ≃ₗ[ℂ]
      (OriginStalkDataFromIndividualStandardOperations.origin standardW (standardSource K E P R)).fiber A :=
  invariantComparison (standardSource K E P R) standardJ standardPhi standardW
    groupDictionary weilDictionary A

omit [MonoidalCategory Standard] [standardJ.Monoidal] in
/-- Ordinary isomorphism naturality restricts to actual inertia invariants. -/
theorem isoInvariant_operator {A B : Standard} (f : A ≅ B)
    (x : Representation.invariants (standardJ.obj A).ρ) :
    invariantsEquiv (equivOfIso (standardJ.mapIso f))
      (invariantAction (standardJ.obj A) (standardW.localFrobenius.action A)
        standardPhi (standardW.covariance A) x) =
    invariantAction (standardJ.obj B) (standardW.localFrobenius.action B)
      standardPhi (standardW.covariance B)
      (invariantsEquiv (equivOfIso (standardJ.mapIso f)) x) := by
  apply Subtype.ext
  exact standardW.localFrobenius.natural f x.val

variable {Point : Type p} [Category.{pl} Point]
  (ordinaryOrigin : Standard ⥤ Point) (pointFiber : Point ⥤ ModuleCat ℂ)
  (pointFr : ∀ X, pointFiber.obj X ≃ₗ[ℂ] pointFiber.obj X)
  (pointNatural : ∀ {X Y} (f : X ≅ Y) x,
    (pointFiber.mapIso f).toLinearEquiv (pointFr X x) =
      pointFr Y ((pointFiber.mapIso f).toLinearEquiv x))
  (jstarComparison :
    standardJ ⋙ forget₂ (FDRep ℂ StandardG) (Rep ℂ StandardG) ⋙ Rep.invariantsFunctor ℂ StandardG ≅
      ordinaryOrigin ⋙ pointFiber)
  (jstarOperator : ∀ A x,
    (jstarComparison.app A).toLinearEquiv
      (invariantAction (standardJ.obj A) (standardW.localFrobenius.action A)
        standardPhi (standardW.covariance A) x) =
    pointFr (ordinaryOrigin.obj A) ((jstarComparison.app A).toLinearEquiv x))
  (standardScalar : Eˣ → Standard ⥤ Standard)
  (fixedOrigin : ∀ a, standardScalar a ⋙ ordinaryOrigin ≅ ordinaryOrigin)
  (scalarOperation : ∀ a, P.localEnd (scalarMorphism K E a) ⋙ R ≅ R ⋙ standardScalar a)

/-- Actual scalar operation, then standard fixed-origin mate, then common reindexing. -/
def scalarComparison (A : Line) (a : Eˣ) :
    Representation.invariants
      ((commonJ R standardJ groupDictionary).obj (scalarSource K E P A a)).ρ ≃ₗ[ℂ]
      (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).fiber A :=
  (ArithmeticBoundaryStandardLocalizationReindex.invariantsChange groupDictionary
    (standardJ.obj (R.obj (scalarSource K E P A a)))).trans
  ((invariantsEquiv (equivOfIso (standardJ.mapIso
    ((scalarOperation a).app ((P.specialized (localInputMorphism K E)).obj A))))).trans
  ((OriginStalkDataFromIndividualStandardOperations.scalarInvariantComparison ordinaryOrigin
    pointFiber jstarComparison standardScalar fixedOrigin a
    ((standardSource K E P R).obj A)).trans
  (computedOriginComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary A).symm))

include pointNatural jstarOperator

omit [Fintype E] [MonoidalCategory Standard] [standardJ.Monoidal] in
/-- No nearby arithmetic matrices are equated: only the computed invariants are compared. -/
theorem scalarComparison_operator (A : Line) (a : Eˣ)
    (x : Representation.invariants
      ((commonJ R standardJ groupDictionary).obj (scalarSource K E P A a)).ρ) :
    scalarComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
      ordinaryOrigin pointFiber jstarComparison standardScalar fixedOrigin scalarOperation A a
      (invariantAction ((commonJ R standardJ groupDictionary).obj (scalarSource K E P A a))
        ((commonW R standardJ standardPhi standardW groupDictionary weilDictionary).localFrobenius.action
          (scalarSource K E P A a))
        (commonPhi standardPhi groupDictionary)
        ((commonW R standardJ standardPhi standardW groupDictionary weilDictionary).covariance
          (scalarSource K E P A a)) x) =
    (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).frobenius A
      (scalarComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
        ordinaryOrigin pointFiber jstarComparison standardScalar fixedOrigin scalarOperation A a x) := by
  let c0 : Representation.invariants
      ((commonJ R standardJ groupDictionary).obj (scalarSource K E P A a)).ρ ≃ₗ[ℂ]
      Representation.invariants (standardJ.obj (R.obj (scalarSource K E P A a))).ρ :=
    ArithmeticBoundaryStandardLocalizationReindex.invariantsChange groupDictionary
      (standardJ.obj (R.obj (scalarSource K E P A a)))
  let f := (scalarOperation a).app ((P.specialized (localInputMorphism K E)).obj A)
  let c1 : Representation.invariants (standardJ.obj (R.obj (scalarSource K E P A a))).ρ ≃ₗ[ℂ]
      Representation.invariants
        (standardJ.obj ((standardScalar a).obj ((standardSource K E P R).obj A))).ρ :=
    invariantsEquiv (equivOfIso (standardJ.mapIso f))
  let c2 : Representation.invariants
      (standardJ.obj ((standardScalar a).obj ((standardSource K E P R).obj A))).ρ ≃ₗ[ℂ]
      (OriginStalkDataFromIndividualStandardOperations.origin standardW (standardSource K E P R)).fiber A :=
    OriginStalkDataFromIndividualStandardOperations.scalarInvariantComparison ordinaryOrigin
      pointFiber jstarComparison standardScalar fixedOrigin a ((standardSource K E P R).obj A)
  let c3 := computedOriginComparison K E P R standardJ standardPhi standardW
    groupDictionary weilDictionary A
  let fN := invariantAction ((commonJ R standardJ groupDictionary).obj (scalarSource K E P A a))
    ((commonW R standardJ standardPhi standardW groupDictionary weilDictionary).localFrobenius.action
      (scalarSource K E P A a)) (commonPhi standardPhi groupDictionary)
    ((commonW R standardJ standardPhi standardW groupDictionary weilDictionary).covariance
      (scalarSource K E P A a))
  let fS := invariantAction (standardJ.obj (R.obj (scalarSource K E P A a)))
    (standardW.localFrobenius.action (R.obj (scalarSource K E P A a))) standardPhi
    (standardW.covariance (R.obj (scalarSource K E P A a)))
  let fT := invariantAction (standardJ.obj ((standardScalar a).obj ((standardSource K E P R).obj A)))
    (standardW.localFrobenius.action ((standardScalar a).obj ((standardSource K E P R).obj A)))
    standardPhi (standardW.covariance ((standardScalar a).obj ((standardSource K E P R).obj A)))
  let fA := (OriginStalkDataFromIndividualStandardOperations.origin standardW (standardSource K E P R)).frobenius A
  let fC := (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).frobenius A
  apply c3.injective
  change c3 (c3.symm (c2 (c1 (c0 (fN x))))) = c3 (fC (c3.symm (c2 (c1 (c0 x)))))
  rw [c3.apply_symm_apply]
  have h0 := frobenius_square R standardJ standardPhi standardW groupDictionary weilDictionary
    (scalarSource K E P A a) x
  change c0 (fN x) = fS (c0 x) at h0
  rw [h0]
  have h1 := isoInvariant_operator standardJ standardPhi standardW f (c0 x)
  change c1 (fS (c0 x)) = fT (c1 (c0 x)) at h1
  rw [h1]
  have h2 := OriginStalkDataFromIndividualStandardOperations.scalarInvariantComparison_operator
    standardW ordinaryOrigin pointFiber pointFr pointNatural jstarComparison jstarOperator
    standardScalar fixedOrigin a ((standardSource K E P R).obj A) (c1 (c0 x))
  change c2 (fT (c1 (c0 x))) = fA (c2 (c1 (c0 x))) at h2
  rw [h2]
  have h3 := frobenius_square (standardSource K E P R) standardJ standardPhi standardW
    groupDictionary weilDictionary A (c3.symm (c2 (c1 (c0 x))))
  change c3 (fC (c3.symm (c2 (c1 (c0 x))))) = fA (c3 (c3.symm (c2 (c1 (c0 x))))) at h3
  rw [c3.apply_symm_apply] at h3
  exact h3.symm

/-- The old scalar-stalk interface is an output of genuine ordinary operations. -/
def scalarStalkComparison : ScalarStalkComparison K E P
    (commonJ R standardJ groupDictionary)
    (commonW R standardJ standardPhi standardW groupDictionary weilDictionary).localFrobenius
    (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary) where
  comparison := scalarComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
    ordinaryOrigin pointFiber jstarComparison standardScalar fixedOrigin scalarOperation
  frobenius A a v := by
    have h := scalarComparison_operator K E P R standardJ standardPhi standardW groupDictionary
      weilDictionary ordinaryOrigin pointFiber pointFr pointNatural jstarComparison jstarOperator
      standardScalar fixedOrigin scalarOperation A a v
    have hi := congrArg (scalarComparison K E P R standardJ standardPhi standardW groupDictionary
      weilDictionary ordinaryOrigin pointFiber jstarComparison standardScalar fixedOrigin
      scalarOperation A a).symm h
    rw [LinearEquiv.symm_apply_apply] at hi
    exact congrArg Subtype.val hi

omit pointNatural jstarOperator

variable (twistOne : Line → Line) (T : Standard)
  (basis : (standardJ.obj T).V ≃ₗ[ℂ] ℂ)
  (inertiaTrivial : ∀ g x, basis ((standardJ.obj T).ρ g x) = basis x)
  (twistOperation : ∀ A, (standardSource K E P R).obj (twistOne A) ≅
    (standardSource K E P R).obj A ⊗ T)
  (tensorRule : ArithmeticTensorFromWeil.TensorRules standardW)
  (lineOperator : ∀ x, basis (standardW.localFrobenius.action T x) =
    (Fintype.card E : ℂ)⁻¹ * basis x)

/-- Tate contraction on the standard source is transported by the known common invariant identity. -/
def tateComparison (A : Line) :
    (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).fiber (twistOne A) ≃ₗ[ℂ]
      (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).fiber A :=
  (computedOriginComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
    (twistOne A)).trans
  ((OriginStalkDataFromIndividualStandardOperations.tateInvariantComparison standardW
    (standardSource K E P R) twistOne T basis inertiaTrivial twistOperation A).trans
  (computedOriginComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary A).symm)

include tensorRule lineOperator

theorem tateComparison_operator (A : Line)
    (x : (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).fiber (twistOne A)) :
    tateComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
      twistOne T basis inertiaTrivial twistOperation A
      ((computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).frobenius (twistOne A) x) =
    (Fintype.card E : ℂ)⁻¹ •
      (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).frobenius A
        (tateComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
          twistOne T basis inertiaTrivial twistOperation A x) := by
  let cA := computedOriginComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary A
  let cT := computedOriginComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary (twistOne A)
  let ct := OriginStalkDataFromIndividualStandardOperations.tateInvariantComparison standardW
    (standardSource K E P R) twistOne T basis inertiaTrivial twistOperation A
  let fCA := (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).frobenius A
  let fCT := (computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary).frobenius (twistOne A)
  let fSA := (OriginStalkDataFromIndividualStandardOperations.origin standardW (standardSource K E P R)).frobenius A
  let fST := (OriginStalkDataFromIndividualStandardOperations.origin standardW (standardSource K E P R)).frobenius (twistOne A)
  apply cA.injective
  change cA (cA.symm (ct (cT (fCT x)))) = cA ((Fintype.card E : ℂ)⁻¹ • fCA (cA.symm (ct (cT x))))
  rw [cA.apply_symm_apply, map_smul]
  have hT := frobenius_square (standardSource K E P R) standardJ standardPhi standardW
    groupDictionary weilDictionary (twistOne A) x
  change cT (fCT x) = fST (cT x) at hT
  rw [hT]
  have ht := OriginStalkDataFromIndividualStandardOperations.tateInvariantComparison_operator standardW
    (standardSource K E P R) twistOne T basis inertiaTrivial twistOperation tensorRule
    (Fintype.card E : ℂ)⁻¹ lineOperator A (cT x)
  change ct (fST (cT x)) = (Fintype.card E : ℂ)⁻¹ • fSA (ct (cT x)) at ht
  rw [ht]
  have hA := frobenius_square (standardSource K E P R) standardJ standardPhi standardW
    groupDictionary weilDictionary A (cA.symm (ct (cT x)))
  change cA (fCA (cA.symm (ct (cT x)))) = fSA (cA (cA.symm (ct (cT x)))) at hA
  rw [cA.apply_symm_apply] at hA
  rw [hA]

omit tensorRule lineOperator

/-- Precomposition of a genuine equivariant comparison needs no injectivity premise. -/
def restrictEquiv {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V']
    {rho : Representation ℂ StandardG V} {sigma : Representation ℂ StandardG V'}
    (e : Representation.Equiv rho sigma) :
    Representation.Equiv (rho.comp groupDictionary.toMonoidHom) (sigma.comp groupDictionary.toMonoidHom) :=
  Representation.Equiv.mk e.toLinearEquiv (fun g => e.isIntertwining' (groupDictionary g))

variable (LG : CanonicalCurveInput.LineGeometry Line)
  (standardLisse standardTame : Standard → Prop)
  (lisseRecognition : ∀ A, LG.LisseOnUnits A → standardLisse ((standardSource K E P R).obj A))
  (tameRecognition : ∀ A, LG.TameZero A → standardTame ((standardSource K E P R).obj A))
  (standardScalarRestriction : ∀ (a : Eˣ) A, standardLisse A → standardTame A →
    Representation.Equiv (standardJ.obj ((standardScalar a).obj A)).ρ (standardJ.obj A).ρ)

/-- Full StalkData is computed, retaining the guarded scope of standard scalar restriction. -/
def stalkData : ArithmeticOriginFromScalar.StalkData K E P
    (commonJ R standardJ groupDictionary)
    (commonW R standardJ standardPhi standardW groupDictionary weilDictionary).localFrobenius LG twistOne where
  origin := computedOrigin K E P R standardJ standardPhi standardW groupDictionary weilDictionary
  comparison := scalarStalkComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
    ordinaryOrigin pointFiber pointFr pointNatural jstarComparison jstarOperator standardScalar fixedOrigin scalarOperation
  tate := {
    comparison := tateComparison K E P R standardJ standardPhi standardW groupDictionary weilDictionary
      twistOne T basis inertiaTrivial twistOperation
    frobenius := tateComparison_operator K E P R standardJ standardPhi standardW groupDictionary weilDictionary
      twistOne T basis inertiaTrivial twistOperation tensorRule lineOperator }
  scalarRestriction a A hL hT :=
    restrictEquiv groupDictionary
      ((equivOfIso (standardJ.mapIso ((scalarOperation a).app
        ((P.specialized (localInputMorphism K E)).obj A)))).trans
        (standardScalarRestriction a ((standardSource K E P R).obj A)
          (lisseRecognition A hL) (tameRecognition A hT)))
end StandardApplication
end PrimeGap182.TypeIII.CommonOriginStalkDataFromStandardOperations
