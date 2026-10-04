import TypeIIIArithmeticSourceMaps
import TypeIIITensorListRepresentation

/-!
# Arithmetic source models along the proved source isomorphisms

General specialization and isomorphism naturality transport primitive
scalar-source zero models to the original input objects. Frobenius
normalization is transported on the same maps, including the source
invariant-line vector and the additive origin action.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace PrimeGap182.TypeIII.ArithmeticSourceTransport

open ArithmeticSourceMaps StartingSourceMaps TensorListRepresentation
open PublishedPhaseApplication

universe u v w a b c d
variable {Local : Type w} [Category.{c} Local] {G : Type d} [Group G]
  (J : Local ⥤ FDRep ℂ G)

/-- Frobenius is natural for all local isomorphisms. The action need not
be an inertia-equivariant endomorphism, so no false commutation with
geometric inertia is imposed. -/
structure LocalFrobenius where
  action : ∀ A, (J.obj A).V ≃ₗ[ℂ] (J.obj A).V
  natural : ∀ {A B} (f : A ≅ B) x,
    equivOfIso (J.mapIso f) (action A x) =
      action B (equivOfIso (J.mapIso f) x)

variable {Input : Type v} [Category.{b} Input]
  (along : Input ⥤ Local) (zero : Input → FDRep ℂ G)
  (originalFr : ∀ A, (zero A).V ≃ₗ[ℂ] (zero A).V) (LF : LocalFrobenius J)

/-- General zero-inertia specialization with its arithmetic naturality,
for every input, along the actual selected inverse-image functor. -/
structure SpecializationComparison where
  comparison : ∀ A, Representation.Equiv (zero A).ρ (J.obj (along.obj A)).ρ
  frobenius : ∀ A x, comparison A (originalFr A x) =
    LF.action (along.obj A) (comparison A x)

variable (K E : Type) [Field K] [Field E] [Algebra K E]
  {Line : Type u} [Category.{a} Line]
  {original : (sourceScheme K ⟶ affineLine K) → Line ⥤ Input}
  (P : Pullbacks (Local := Local) K E original) (lambda xi : Eˣ)
  (SC : SpecializationComparison J (P.along (specializationMorphism K E lambda xi)) zero originalFr LF)

/-- Original source restriction, through the proved arithmetic scheme
factorization and the SAME specialization comparison used for all inputs. -/
def sourceRestrictionEquiv (A : Line) (i : Fin 3) :
    Representation.Equiv (zero ((original (inputMorphism K i)).obj A)).ρ
      (J.obj ((P.localEnd (scalarMorphism K E (![1, lambda, xi] i))).obj
        ((P.specialized (localInputMorphism K E)).obj A))).ρ :=
  (SC.comparison ((original (inputMorphism K i)).obj A)).trans
    (equivOfIso (J.mapIso ((sourcePullbackIso K E P lambda xi i).app A)))

/-- The constructed source isomorphism preserves the arithmetic action;
no Frobenius square for a completed family source is supplied. -/
theorem sourceRestrictionEquiv_frobenius (A : Line) (i : Fin 3)
    (x : (zero ((original (inputMorphism K i)).obj A)).V) :
    sourceRestrictionEquiv J zero originalFr LF K E P lambda xi SC A i
      (originalFr ((original (inputMorphism K i)).obj A) x) =
    LF.action ((P.localEnd (scalarMorphism K E (![1, lambda, xi] i))).obj
      ((P.specialized (localInputMorphism K E)).obj A))
      (sourceRestrictionEquiv J zero originalFr LF K E P lambda xi SC A i x) := by
  change equivOfIso (J.mapIso ((sourcePullbackIso K E P lambda xi i).app A))
    (SC.comparison _ (originalFr _ x)) = _
  rw [SC.frobenius]
  exact LF.natural ((sourcePullbackIso K E P lambda xi i).app A) (SC.comparison _ x)

variable {U : Type*} [AddCommGroup U] [Module ℂ U] (rho : Representation ℂ G U)
  (A : Line) (i : Fin 3)
  (model : Representation.Equiv
    (J.obj ((P.localEnd (scalarMorphism K E (![1, lambda, xi] i))).obj
      ((P.specialized (localInputMorphism K E)).obj A))).ρ rho)

/-- A primitive scalar-source model now gives the model on the actual
original source input; the family source identification is derived. -/
def sourceModelEquiv : Representation.Equiv
    (zero ((original (inputMorphism K i)).obj A)).ρ rho :=
  (sourceRestrictionEquiv J zero originalFr LF K E P lambda xi SC A i).trans model

/-- Transport an actual source eigenvector through an arithmetic
comparison, retaining the original Frobenius operator. -/
theorem sourceModel_eigenvector (v : U) (c : ℂ)
    (hline : LF.action ((P.localEnd (scalarMorphism K E (![1, lambda, xi] i))).obj
      ((P.specialized (localInputMorphism K E)).obj A)) (model.toLinearEquiv.symm v) =
      c • model.toLinearEquiv.symm v) :
    originalFr ((original (inputMorphism K i)).obj A)
      ((sourceModelEquiv J zero originalFr LF K E P lambda xi SC rho A i model).toLinearEquiv.symm v) =
    c • (sourceModelEquiv J zero originalFr LF K E P lambda xi SC rho A i model).toLinearEquiv.symm v := by
  let e := sourceRestrictionEquiv J zero originalFr LF K E P lambda xi SC A i
  apply e.toLinearEquiv.injective
  change e.toLinearEquiv (originalFr ((original (inputMorphism K i)).obj A)
      (e.toLinearEquiv.symm (model.toLinearEquiv.symm v))) =
    e.toLinearEquiv (c • e.toLinearEquiv.symm (model.toLinearEquiv.symm v))
  have hn := sourceRestrictionEquiv_frobenius J zero originalFr LF K E P lambda xi SC A i
    (e.toLinearEquiv.symm (model.toLinearEquiv.symm v))
  change e.toLinearEquiv (originalFr ((original (inputMorphism K i)).obj A)
      (e.toLinearEquiv.symm (model.toLinearEquiv.symm v))) =
    LF.action ((P.localEnd (scalarMorphism K E (![1, lambda, xi] i))).obj
      ((P.specialized (localInputMorphism K E)).obj A))
      (e.toLinearEquiv (e.toLinearEquiv.symm (model.toLinearEquiv.symm v))) at hn
  rw [hn, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  exact hline

/-- Trivial additive-origin Frobenius transports through the same
source comparison, without assuming it on the original family input. -/
theorem sourceModel_frobenius_trivial
    (hlocal : ∀ x, model (LF.action ((P.localEnd (scalarMorphism K E (![1, lambda, xi] i))).obj
      ((P.specialized (localInputMorphism K E)).obj A)) x) = model x)
    (x : (zero ((original (inputMorphism K i)).obj A)).V) :
    sourceModelEquiv J zero originalFr LF K E P lambda xi SC rho A i model
      (originalFr ((original (inputMorphism K i)).obj A) x) =
    sourceModelEquiv J zero originalFr LF K E P lambda xi SC rho A i model x := by
  change model (sourceRestrictionEquiv J zero originalFr LF K E P lambda xi SC A i
    (originalFr _ x)) = _
  rw [sourceRestrictionEquiv_frobenius, hlocal]
  rfl

end PrimeGap182.TypeIII.ArithmeticSourceTransport

#print axioms PrimeGap182.TypeIII.ArithmeticSourceTransport.sourceRestrictionEquiv
#print axioms PrimeGap182.TypeIII.ArithmeticSourceTransport.sourceRestrictionEquiv_frobenius
#print axioms PrimeGap182.TypeIII.ArithmeticSourceTransport.sourceModelEquiv
#print axioms PrimeGap182.TypeIII.ArithmeticSourceTransport.sourceModel_eigenvector
#print axioms PrimeGap182.TypeIII.ArithmeticSourceTransport.sourceModel_frobenius_trivial
