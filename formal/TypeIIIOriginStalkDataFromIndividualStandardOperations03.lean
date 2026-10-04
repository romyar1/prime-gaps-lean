import TypeIIIOriginStalksFromStandardWeilInvariants01
import TypeIIITateLineInvariantContraction03
import TypeIIIArithmeticOriginFromScalar
import TypeIIIArithmeticTensorFromWeil

/-! Compute the SAME invariant origin stalks. Scalar Frobenius is transported
through an ordinary fixed-origin mate and the ordinary residue operator's
naturality. Tate Frobenius is contracted from ONE inertia-trivial coefficient
line. Standard guarded scalar restriction is separate. No StalkData,
ScalarStalkComparison, TateOriginRules or finished family is a premise. -/
noncomputable section
open CategoryTheory
open scoped MonoidalCategory TensorProduct
namespace PrimeGap182.TypeIII.OriginStalkDataFromIndividualStandardOperations
open LocalWeilAction ArithmeticSourceTransport ArithmeticSourcesFromOrigin
open ArithmeticSourceMaps ArithmeticPrimitiveSources ArithmeticOriginFromScalar
open OriginStalksFromStandardWeilInvariants TensorListRepresentation
open RegularUnipotentBoundary TateLineInvariantContraction
universe u v a b c d g h

section Restriction
variable {Line : Type u} [Category.{a} Line]
  {Local : Type v} [Category.{b} Local] {G : Type g} [Group G]
  {J : Local ⥤ FDRep ℂ G} {phi : G →* G}
  (W : LocalWeilAction.Data J phi) (source : Line ⥤ Local)

/-- Restrict the SAME whole Weil action along the literal source functor. -/
def sourceWeil : LocalWeilAction.Data (source ⋙ J) phi where
  Weil := W.Weil
  inertia := W.inertia
  frobenius := W.frobenius
  relation := W.relation
  representation A := W.representation (source.obj A)
  restriction A := W.restriction (source.obj A)
  natural f := W.natural (source.map f)

/-- The origin is computed, with no chosen stalk provider. -/
def origin : OriginStalks.{u,0} Line :=
  invariantStalks (source ⋙ J) phi (sourceWeil W source)
end Restriction

section OrdinaryFixedOrigin
variable {Local : Type v} [Category.{b} Local] {G : Type g} [Group G]
  {J : Local ⥤ FDRep ℂ G} {phi : G →* G}
  (W : LocalWeilAction.Data J phi)
  {Point : Type c} [Category.{d} Point]
  (ordinaryOrigin : Local ⥤ Point) (pointFiber : Point ⥤ ModuleCat ℂ)
  (pointFr : ∀ X, pointFiber.obj X ≃ₗ[ℂ] pointFiber.obj X)
  (pointNatural : ∀ {X Y} (f : X ≅ Y) x,
    (pointFiber.mapIso f).toLinearEquiv (pointFr X x) =
      pointFr Y ((pointFiber.mapIso f).toLinearEquiv x))
  (jstarComparison :
    J ⋙ forget₂ (FDRep ℂ G) (Rep ℂ G) ⋙ Rep.invariantsFunctor ℂ G ≅
      ordinaryOrigin ⋙ pointFiber)
  (jstarOperator : ∀ A x,
    (jstarComparison.app A).toLinearEquiv
      (ArithmeticBoundaryFromInvariantFunctors.invariantAction (J.obj A)
        (W.localFrobenius.action A) phi (W.covariance A) x) =
    pointFr (ordinaryOrigin.obj A) ((jstarComparison.app A).toLinearEquiv x))
  {Index : Type h} (scalar : Index → Local ⥤ Local)
  (fixedOrigin : ∀ s, scalar s ⋙ ordinaryOrigin ≅ ordinaryOrigin)

/-- Compare invariants through genuine ordinary j_* and its fixed-point mate. -/
def scalarInvariantComparison (s : Index) (A : Local) :
    Representation.invariants (J.obj ((scalar s).obj A)).ρ ≃ₗ[ℂ] Representation.invariants (J.obj A).ρ :=
  (jstarComparison.app ((scalar s).obj A)).toLinearEquiv.trans
    ((pointFiber.mapIso ((fixedOrigin s).app A)).toLinearEquiv.trans
      (jstarComparison.app A).toLinearEquiv.symm)

include pointNatural jstarOperator

/-- Ordinary residue naturality derives invariant Frobenius transport. -/
theorem scalarInvariantComparison_operator (s : Index) (A : Local)
    (x : Representation.invariants (J.obj ((scalar s).obj A)).ρ) :
    scalarInvariantComparison ordinaryOrigin pointFiber jstarComparison scalar fixedOrigin s A
      (ArithmeticBoundaryFromInvariantFunctors.invariantAction
        (J.obj ((scalar s).obj A)) (W.localFrobenius.action ((scalar s).obj A))
        phi (W.covariance ((scalar s).obj A)) x) =
    ArithmeticBoundaryFromInvariantFunctors.invariantAction (J.obj A)
      (W.localFrobenius.action A) phi (W.covariance A)
      (scalarInvariantComparison ordinaryOrigin pointFiber jstarComparison scalar fixedOrigin s A x) := by
  let eA : Representation.invariants (J.obj A).ρ ≃ₗ[ℂ]
      pointFiber.obj (ordinaryOrigin.obj A) := (jstarComparison.app A).toLinearEquiv
  let eS : Representation.invariants (J.obj ((scalar s).obj A)).ρ ≃ₗ[ℂ]
      pointFiber.obj (ordinaryOrigin.obj ((scalar s).obj A)) :=
    (jstarComparison.app ((scalar s).obj A)).toLinearEquiv
  let em := (pointFiber.mapIso ((fixedOrigin s).app A)).toLinearEquiv
  apply eA.injective
  change eA (eA.symm (em (eS
      (ArithmeticBoundaryFromInvariantFunctors.invariantAction
        (J.obj ((scalar s).obj A)) (W.localFrobenius.action ((scalar s).obj A))
        phi (W.covariance ((scalar s).obj A)) x)))) =
    eA (ArithmeticBoundaryFromInvariantFunctors.invariantAction (J.obj A)
      (W.localFrobenius.action A) phi (W.covariance A) (eA.symm (em (eS x))))
  rw [eA.apply_symm_apply]
  have hs := jstarOperator ((scalar s).obj A) x
  change eS (ArithmeticBoundaryFromInvariantFunctors.invariantAction
    (J.obj ((scalar s).obj A)) (W.localFrobenius.action ((scalar s).obj A))
    phi (W.covariance ((scalar s).obj A)) x) =
      pointFr (ordinaryOrigin.obj ((scalar s).obj A)) (eS x) at hs
  rw [hs]
  have hm := pointNatural ((fixedOrigin s).app A) (eS x)
  change em (pointFr (ordinaryOrigin.obj ((scalar s).obj A)) (eS x)) =
    pointFr (ordinaryOrigin.obj A) (em (eS x)) at hm
  rw [hm]
  have ha := jstarOperator A (eA.symm (em (eS x)))
  change eA (ArithmeticBoundaryFromInvariantFunctors.invariantAction (J.obj A)
    (W.localFrobenius.action A) phi (W.covariance A) (eA.symm (em (eS x)))) =
      pointFr (ordinaryOrigin.obj A) (eA (eA.symm (em (eS x)))) at ha
  rw [eA.apply_symm_apply] at ha
  exact ha.symm
end OrdinaryFixedOrigin

section Tate
variable {Line : Type u} [Category.{a} Line]
  {Local : Type v} [Category.{b} Local] [MonoidalCategory Local]
  {G : Type g} [Group G] {J : Local ⥤ FDRep ℂ G} [J.Monoidal]
  {phi : G →* G} (W : LocalWeilAction.Data J phi)
  (source : Line ⥤ Local) (twistOne : Line → Line) (T : Local)
  (basis : (J.obj T).V ≃ₗ[ℂ] ℂ)
  (inertiaTrivial : ∀ g x, basis ((J.obj T).ρ g x) = basis x)
  (twistComparison : ∀ A, source.obj (twistOne A) ≅ source.obj A ⊗ T)

/-- Literal ordinary twist comparison followed by the SAME tensor map. -/
def twistRepresentationComparison (A : Line) :
    Representation.Equiv (J.obj (source.obj (twistOne A))).ρ
      (Representation.tprod (J.obj (source.obj A)).ρ (J.obj T).ρ) :=
  equivOfIso (J.mapIso (twistComparison A) ≪≫
    (Functor.Monoidal.μIso J (source.obj A) T).symm)

/-- The entire Tate invariant comparison is computed by one-line contraction. -/
def tateInvariantComparison (A : Line) :
    (origin W source).fiber (twistOne A) ≃ₗ[ℂ] (origin W source).fiber A :=
  (invariantsEquiv (twistRepresentationComparison source twistOne T twistComparison A)).trans
    (invariantContraction (J.obj (source.obj A)).ρ (J.obj T).ρ basis inertiaTrivial)

variable (tensorRule : ArithmeticTensorFromWeil.TensorRules W)

include tensorRule

/-- Tensor inverse transfer uses ALL-Weil tensor naturality and ordinary iso naturality. -/
theorem twistRepresentationComparison_operator (A : Line)
    (x : (J.obj (source.obj (twistOne A))).V) :
    twistRepresentationComparison source twistOne T twistComparison A
      (W.localFrobenius.action (source.obj (twistOne A)) x) =
    TensorProduct.map (W.localFrobenius.action (source.obj A)).toLinearMap
      (W.localFrobenius.action T).toLinearMap
      (twistRepresentationComparison source twistOne T twistComparison A x) := by
  let e := equivOfIso (Functor.Monoidal.μIso J (source.obj A) T)
  have inverseTensor (y : (J.obj (source.obj A ⊗ T)).V) :
      e.symm (W.localFrobenius.action (source.obj A ⊗ T) y) =
      TensorProduct.map (W.localFrobenius.action (source.obj A)).toLinearMap
        (W.localFrobenius.action T).toLinearMap (e.symm y) := by
    have he (z : (J.obj (source.obj A ⊗ T)).V) : e (e.symm z) = z :=
      e.toLinearEquiv.apply_symm_apply z
    apply e.toLinearEquiv.injective
    change e (e.symm _) = _
    rw [he]
    have hn := tensorRule.natural (source.obj A) T W.frobenius (e.symm y)
    change e (TensorProduct.map (W.localFrobenius.action (source.obj A)).toLinearMap
      (W.localFrobenius.action T).toLinearMap (e.symm y)) =
      W.localFrobenius.action (source.obj A ⊗ T) (e (e.symm y)) at hn
    rw [he] at hn
    exact hn.symm
  change e.symm (equivOfIso (J.mapIso (twistComparison A))
    (W.localFrobenius.action (source.obj (twistOne A)) x)) = _
  rw [W.localFrobenius.natural, inverseTensor]
  rfl

/-- ONE line Frobenius scalar determines the entire Tate invariant operator. -/
theorem tateInvariantComparison_operator (s : ℂ)
    (lineOperator : ∀ x, basis (W.localFrobenius.action T x) = s * basis x)
    (A : Line) (x : (origin W source).fiber (twistOne A)) :
    tateInvariantComparison W source twistOne T basis inertiaTrivial twistComparison A
      ((origin W source).frobenius (twistOne A) x) =
    s • (origin W source).frobenius A
      (tateInvariantComparison W source twistOne T basis inertiaTrivial twistComparison A x) := by
  apply Subtype.ext
  change contraction basis
      (twistRepresentationComparison source twistOne T twistComparison A
        (W.localFrobenius.action (source.obj (twistOne A)) x.val)) =
    s • W.localFrobenius.action (source.obj A)
      (contraction basis (twistRepresentationComparison source twistOne T twistComparison A x.val))
  rw [twistRepresentationComparison_operator W source twistOne T twistComparison tensorRule]
  exact contraction_tensor_operator basis
    (W.localFrobenius.action (source.obj A)).toLinearMap
    (W.localFrobenius.action T).toLinearMap s lineOperator _

/-- Apply the standard q^-1 coefficient line to the old individual Tate interface. -/
def tateOriginRules (E : Type) [Field E] [Fintype E]
    (lineOperator : ∀ x, basis (W.localFrobenius.action T x) =
      (Fintype.card E : ℂ)⁻¹ * basis x) :
    TateOriginRules E (origin W source) twistOne where
  comparison := tateInvariantComparison W source twistOne T basis inertiaTrivial twistComparison
  frobenius := tateInvariantComparison_operator W source twistOne T basis inertiaTrivial
    twistComparison tensorRule (Fintype.card E : ℂ)⁻¹ lineOperator
end Tate
end PrimeGap182.TypeIII.OriginStalkDataFromIndividualStandardOperations
