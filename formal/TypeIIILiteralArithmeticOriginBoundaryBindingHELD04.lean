import TypeIIIArithmeticTensorFromWeil
import TypeIIIArithmeticBoundaryFromInvariantFunctors

/-!
# HELD literal arithmetic origin/boundary binding

Fix the actual specialization along, actual positive-T inertia fiber J,
its selected monoidal structure and the SAME Weil action W. Define zero
as along composed with J. Canonical localization data supply individual
geometric clauses; the original BS and AZ are computed on this zero.
The ALL-Weil tensor law and guarded categorical dual square compute AP.
The old specialization comparison and inertia covariance follow from
these SAME operators. No BS/AZ/AP/SC or arithmetic realization is supplied.

This is an uncompiled operation-binding leaf. The genuine continuous-adic
interpretation, actual infinity/localization/sign operations and guarded
eligibility are external. It asserts no existence or whole endpoint law.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.LiteralArithmeticOriginBoundaryBindingHELD04
open PublishedPhysicalConstruction PublishedPhaseApplication BoundaryFromSourceModels
open GeometricBoundaryFromFunctors ArithmeticZeroFromSpecialization
open ArithmeticSourceTransport ArithmeticRestrictionFromStalks
open ArithmeticTensorFromWeil RestrictionFrobenius

universe u v p a b c d e f
variable {Input : Type u} [Category.{a} Input] [MonoidalCategory Input]
  {Local : Type v} [Category.{b} Local] [MonoidalCategory Local]
  {Point : Type p} {Parameter : Type} [Category.{c} Parameter] [Abelian Parameter]
  (Obs : CurveDataFromOperations.Observables Input Point)
  (dualInput : Inputᵒᵖ ⥤ Input)
  {H : CohomologyData Input Parameter} (coeffFiber : Parameter ⥤ ModuleCat ℂ)
  {G0 : Type d} [Group G0] {Ginf : Type e} [Group Ginf]
  (along : Input ⥤ Local) [along.Monoidal]
  (J : Local ⥤ FDRep ℂ G0) [J.Monoidal]
  {phi : G0 →* G0} (W : LocalWeilAction.Data J phi)

/- The genuine P1 closed-boundary operations and guarded localization
clauses are fixed on the actual zero=along composed with J. These are
individual ALL-object clauses, not a supplied finished boundary record. -/
variable (infinity : Input ⥤ FDRep ℂ Ginf)
  (dualRestriction : ∀ A, Obs.Lisse A →
    Representation.Equiv ((along ⋙ J).obj (dualInput.obj (op A))).ρ
      (PublishedPhaseApplication.dualRepresentation ((along ⋙ J).obj A)).ρ)
  (positiveSlope : ∀ A, Obs.Isoclinic A 1 →
    Representation.invariants (infinity.obj A).ρ = ⊥)
  (toCompact : ∀ A,
    (Representation.invariants ((along ⋙ J).obj A).ρ ×
      Representation.invariants (infinity.obj A).ρ) →ₗ[ℂ] coeffFiber.obj (H.compact A))
  (boundaryInjective : ∀ A, Obs.Lisse A → Obs.Isoclinic A 1 →
    Function.Injective (toCompact A))
  (boundaryExact : ∀ A, Obs.Lisse A → Obs.TameZero A → Obs.Isoclinic A 1 →
    LinearMap.range (toCompact A) = LinearMap.ker (coeffFiber.map (H.comparison A)).hom)

/-- Assemble only the geometric map interface on the fixed actual zero. -/
def canonicalBoundaryMaps : ArithmeticZeroFromSpecialization.BoundaryMaps
    (Ginf := Ginf) (Obs.curveData dualInput) H coeffFiber dualInput (along ⋙ J) where
  infinity := infinity
  dual := dualRestriction
  positiveSlope := positiveSlope
  toCompact := toCompact
  injective := boundaryInjective
  exact := boundaryExact

/-- The boundary is the literal product of the two inertia invariant spaces. -/
abbrev canonicalBoundarySequence :=
  (canonicalBoundaryMaps (Obs := Obs) (dualInput := dualInput) (H := H)
    (coeffFiber := coeffFiber) (along := along) (J := J) (infinity := infinity)
    (dualRestriction := dualRestriction) (positiveSlope := positiveSlope)
    (toCompact := toCompact) (boundaryInjective := boundaryInjective)
    (boundaryExact := boundaryExact)).data.boundarySequence

/-- The old geometric restriction is computed on zero=along composed with J. -/
abbrev canonicalRestriction :=
  (canonicalBoundaryMaps (Obs := Obs) (dualInput := dualInput) (H := H)
    (coeffFiber := coeffFiber) (along := along) (J := J) (infinity := infinity)
    (dualRestriction := dualRestriction) (positiveSlope := positiveSlope)
    (toCompact := toCompact) (boundaryInjective := boundaryInjective)
    (boundaryExact := boundaryExact)).data.restriction
    (Obs.tensorComparison dualInput) (Obs.dualComparison dualInput)

/- GENERAL compatibility of the genuine tensor fiber with EVERY Weil
operator. The dual clause below is the guarded ALL-object categorical
inverse-Frobenius square on the exact same dual restriction comparison. -/
variable (tensorWeil : ArithmeticTensorFromWeil.TensorRules W)
  (dualOperator : ∀ A (hA : Obs.Lisse A) x,
    (canonicalRestriction (Obs := Obs) (dualInput := dualInput) (H := H)
    (coeffFiber := coeffFiber) (along := along) (J := J) (infinity := infinity)
    (dualRestriction := dualRestriction) (positiveSlope := positiveSlope)
    (toCompact := toCompact) (boundaryInjective := boundaryInjective)
    (boundaryExact := boundaryExact)).dualZero A hA
      (W.localFrobenius.action (along.obj ((Obs.curveData dualInput).dual A)) x) =
    (W.localFrobenius.action (along.obj A)).symm.toLinearMap.dualMap
      ((canonicalRestriction (Obs := Obs) (dualInput := dualInput) (H := H)
    (coeffFiber := coeffFiber) (along := along) (J := J) (infinity := infinity)
    (dualRestriction := dualRestriction) (positiveSlope := positiveSlope)
    (toCompact := toCompact) (boundaryInjective := boundaryInjective)
    (boundaryExact := boundaryExact)).dualZero A hA x))

/-- Tensor Frobenius is derived; the ordinary guarded dual operation is retained. -/
abbrev canonicalArithmeticRestriction :=
  ArithmeticRestrictionFromStalks.Stalks.restriction W.localFrobenius
    (canonicalRestriction (Obs := Obs) (dualInput := dualInput) (H := H)
      (coeffFiber := coeffFiber) (along := along) (J := J) (infinity := infinity)
      (dualRestriction := dualRestriction) (positiveSlope := positiveSlope)
      (toCompact := toCompact) (boundaryInjective := boundaryInjective)
      (boundaryExact := boundaryExact))
    (ArithmeticZeroFromSpecialization.stalks along J)
    (ArithmeticTensorFromWeil.tensorDualRules W along Obs dualInput
      (canonicalBoundaryMaps (Obs := Obs) (dualInput := dualInput) (H := H)
    (coeffFiber := coeffFiber) (along := along) (J := J) (infinity := infinity)
    (dualRestriction := dualRestriction) (positiveSlope := positiveSlope)
    (toCompact := toCompact) (boundaryInjective := boundaryInjective)
    (boundaryExact := boundaryExact)) tensorWeil
      (show ArithmeticTensorFromWeil.DualRule W along Obs dualInput
        (canonicalBoundaryMaps (Obs := Obs) (dualInput := dualInput) (H := H)
    (coeffFiber := coeffFiber) (along := along) (J := J) (infinity := infinity)
    (dualRestriction := dualRestriction) (positiveSlope := positiveSlope)
    (toCompact := toCompact) (boundaryInjective := boundaryInjective)
    (boundaryExact := boundaryExact)) from { natural := dualOperator }))

/-- The former input SC is an output with reflexive geometric comparison. -/
def canonicalSpecialization :=
  (ArithmeticZeroFromSpecialization.stalks along J).specialization W.localFrobenius

omit [MonoidalCategory Input] [MonoidalCategory Local] [along.Monoidal] [J.Monoidal] in
/-- Its original zero action is literally the same geometric Weil lift. -/
theorem canonicalZeroFrobenius (A : Input) (x : ((along ⋙ J).obj A).V) :
    (ArithmeticZeroFromSpecialization.stalks along J).action W.localFrobenius A x =
      W.localFrobenius.action (along.obj A) x :=
  ArithmeticZeroFromSpecialization.action along J W.localFrobenius A x

omit [MonoidalCategory Input] [MonoidalCategory Local] [along.Monoidal] [J.Monoidal] in
/-- Source covariance follows from the same Weil relation, with no second operator. -/
theorem canonicalCovariance (A : Input) (z : G0) (x : ((along ⋙ J).obj A).V) :
    (ArithmeticZeroFromSpecialization.stalks along J).action W.localFrobenius A
        (((along ⋙ J).obj A).ρ z x) =
      ((along ⋙ J).obj A).ρ (phi z)
        ((ArithmeticZeroFromSpecialization.stalks along J).action W.localFrobenius A x) :=
  (ArithmeticZeroFromSpecialization.stalks along J).covariance W.localFrobenius phi
    W.covariance A z x

end PrimeGap182.TypeIII.LiteralArithmeticOriginBoundaryBindingHELD04
