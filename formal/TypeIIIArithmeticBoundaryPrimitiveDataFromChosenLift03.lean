import TypeIIIArithmeticBoundaryPrimitiveWeilRealization03
import TypeIIIWholeWeilFromInertiaAndChosenLift02

/-! Pure factory for the exact existing primitive realization DATA signature.
Explicit group normal form reduces all-Weil coefficient compatibility to one
chosen-lift compatibility equation. Standard normal form can be pulled through
an independently supplied injective SAME Weil dictionary. No group dictionary
or standard realization exists by this construction. Other fields are literal. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct MonoidalCategory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryPrimitiveDataFromChosenLift
open LocalWeilAction
universe u v us vs g gs t ts
variable {Local : Type u} [Category.{v} Local] [MonoidalCategory Local]
  {StandardLocal : Type us} [Category.{vs} StandardLocal] [MonoidalCategory StandardLocal]
  {G : Type g} [Group G] {StandardG : Type gs} [Group StandardG]
  {Gi : Type t} [Group Gi] {StandardGi : Type ts} [Group StandardGi]
  (J : Local ⥤ FDRep ℂ G) [J.Monoidal] (phi : G →* G) (D : Data J phi)
  (realization : Local ⥤ StandardLocal) [realization.Monoidal]
  (standardJ : StandardLocal ⥤ FDRep ℂ StandardG) [standardJ.Monoidal]
  (standardPhi : StandardG →* StandardG) (standardD : Data standardJ standardPhi)

/-- The eight original primitive fields and ONE chosen-lift coefficient square.
Normal form remains separate, independently geometric group-recognition DATA. -/
structure ChosenLiftPrimitiveData where
  originGroup : G ≃* StandardG
  infinityGroup : Gi ≃* StandardGi
  coefficient : J ≅ (realization ⋙ standardJ) ⋙
    Action.res (FGModuleCat ℂ) originGroup.toMonoidHom
  coefficientUnit : ∀ z : ℂ,
    (coefficient.app (𝟙_ Local)).hom.hom.hom
      ((Functor.LaxMonoidal.ε J).hom.hom.hom z) =
        (Functor.LaxMonoidal.ε (realization ⋙ standardJ)).hom.hom.hom z
  coefficientTensor : ∀ A B (x : (J.obj A).V) (y : (J.obj B).V),
    (coefficient.app (A ⊗ B)).hom.hom.hom
      ((Functor.LaxMonoidal.μ J A B).hom.hom.hom (x ⊗ₜ[ℂ] y)) =
        (Functor.LaxMonoidal.μ (realization ⋙ standardJ) A B).hom.hom.hom
          (((coefficient.app A).hom.hom.hom x) ⊗ₜ[ℂ]
           ((coefficient.app B).hom.hom.hom y))
  weilMap : D.Weil →* standardD.Weil
  inertia_eq : ∀ q, weilMap (D.inertia q) = standardD.inertia (originGroup q)
  frobenius_eq : weilMap D.frobenius = standardD.frobenius
  chosenLift : ∀ (A : Local) (x : (J.obj A).V),
    (coefficient.app A).hom.hom.hom (D.representation A D.frobenius x) =
      standardD.representation (realization.obj A) standardD.frobenius
        ((coefficient.app A).hom.hom.hom x)

variable (P : ChosenLiftPrimitiveData (Gi := Gi) (StandardGi := StandardGi)
    J phi D realization standardJ standardPhi standardD)
  (nativeNormalForm : ∀ w : D.Weil,
    ∃ q : G, ∃ n : ℤ, w = D.inertia q * D.frobenius ^ n)

/-- Exact original record; native normal form is explicit and does not require
faithfulness of the Weil map. Inertia intertwining follows from the FDRep iso. -/
def toPrimitiveData : ArithmeticBoundaryPrimitiveWeilRealization.PrimitiveData
    (Gi := Gi) (StandardGi := StandardGi)
    J phi D realization standardJ standardPhi standardD where
  originGroup := P.originGroup
  infinityGroup := P.infinityGroup
  coefficient := P.coefficient
  coefficientUnit := P.coefficientUnit
  coefficientTensor := P.coefficientTensor
  weilMap := P.weilMap
  inertia_eq := P.inertia_eq
  frobenius_eq := P.frobenius_eq
  wholeWeil := WholeWeilFromInertiaAndChosenLift.wholeWeil_of_coefficientIso
    J phi D realization standardJ standardPhi standardD P.originGroup P.weilMap
    P.coefficient P.inertia_eq P.frobenius_eq nativeNormalForm P.chosenLift

/-- Standard-group normal form is pulled through the SAME explicitly injective
dictionary. No injectivity premise is imposed by the native-normal-form factory. -/
def toPrimitiveDataFromStandardNormalForm
    (injective : Function.Injective P.weilMap)
    (standardNormalForm : ∀ w : standardD.Weil,
      ∃ q : StandardG, ∃ n : ℤ,
      w = standardD.inertia q * standardD.frobenius ^ n) :
    ArithmeticBoundaryPrimitiveWeilRealization.PrimitiveData
      (Gi := Gi) (StandardGi := StandardGi)
      J phi D realization standardJ standardPhi standardD :=
  toPrimitiveData J phi D realization standardJ standardPhi standardD P
    (WholeWeilFromInertiaAndChosenLift.normalForm_of_injective_dictionary
      D.inertia D.frobenius standardD.inertia standardD.frobenius
      P.originGroup P.weilMap injective P.inertia_eq P.frobenius_eq standardNormalForm)

@[simp] theorem originGroup_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).originGroup = P.originGroup := rfl

@[simp] theorem infinityGroup_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).infinityGroup = P.infinityGroup := rfl

@[simp] theorem coefficient_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).coefficient = P.coefficient := rfl

@[simp] theorem coefficientUnit_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).coefficientUnit = P.coefficientUnit := rfl

@[simp] theorem coefficientTensor_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).coefficientTensor = P.coefficientTensor := rfl

@[simp] theorem weilMap_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).weilMap = P.weilMap := rfl

@[simp] theorem inertia_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).inertia_eq = P.inertia_eq := rfl

@[simp] theorem frobenius_projection :
    (toPrimitiveData J phi D realization standardJ standardPhi standardD P
      nativeNormalForm).frobenius_eq = P.frobenius_eq := rfl

/- Exact original all-Weil field, with no extra selected all-Weil premise. -/
include nativeNormalForm in
theorem wholeWeil_projection (A : Local) (w : D.Weil) (x : (J.obj A).V) :
    (P.coefficient.app A).hom.hom.hom (D.representation A w x) =
      standardD.representation (realization.obj A) (P.weilMap w)
        ((P.coefficient.app A).hom.hom.hom x) :=
  (toPrimitiveData J phi D realization standardJ standardPhi standardD P
    nativeNormalForm).wholeWeil A w x

/- An independently supplied equivalence for the SAME map discharges only
dictionary faithfulness. This theorem asserts no Weil equivalence exists. -/
omit [MonoidalCategory Local] [MonoidalCategory StandardLocal] [J.Monoidal] [standardJ.Monoidal] in
theorem injective_of_weilEquiv (weilMap : D.Weil →* standardD.Weil)
    (weilEquiv : D.Weil ≃* standardD.Weil)
    (sameMap : weilEquiv.toMonoidHom = weilMap) : Function.Injective weilMap := by
  rw [← sameMap]
  exact weilEquiv.injective

end PrimeGap182.TypeIII.ArithmeticBoundaryPrimitiveDataFromChosenLift
