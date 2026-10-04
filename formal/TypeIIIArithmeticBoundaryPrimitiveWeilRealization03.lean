import TypeIIIStandardP1BoundaryPrimitives03
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! Explicit primitive DATA signature for the selected arithmetic functor.
Group identifications are with independently interpreted standard groups.
The record contains no cohomology, connecting arrow, native Fr square,
finite-lisse dual comparison, or finished boundary record. FULL Weil
intertwining and one group-level chosen-lift equality derive Frobenius. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct MonoidalCategory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryPrimitiveWeilRealization
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

/-- One independently geometric primitive realization, not a whole boundary
provider. A current constructor uses this record for ALL finite E/x/y.
Monoidal compatibility refers to literal tensor/unit structure, not a supplied
pairing or contragredient comparison. -/
structure PrimitiveData where
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
  wholeWeil : ∀ A z x,
    (coefficient.app A).hom.hom.hom (D.representation A z x) =
      standardD.representation (realization.obj A) (weilMap z)
        ((coefficient.app A).hom.hom.hom x)

variable (P : PrimitiveData (Gi := Gi) (StandardGi := StandardGi) J phi D realization standardJ standardPhi standardD)

/-- Group conjugation alignment is a consequence of genuine inertia inclusion
and the two group dictionaries; it is not selected data. -/
theorem conjugation_eq (inertiaInjective : Function.Injective standardD.inertia) (q : G) :
    P.originGroup (phi q) = standardPhi (P.originGroup q) := by
  apply inertiaInjective
  apply mul_right_cancel (b := standardD.frobenius)
  have hn := congrArg P.weilMap (D.relation q)
  rw [map_mul, map_mul, P.frobenius_eq, P.inertia_eq, P.inertia_eq] at hn
  exact hn.symm.trans (standardD.relation (P.originGroup q))

/-- The origin fiber Frobenius square follows from full-Weil realization. -/
theorem origin_frobenius_square (A : Local) (x : (J.obj A).V) :
    (P.coefficient.app A).hom.hom.hom (D.localFrobenius.action A x) =
      standardD.localFrobenius.action (realization.obj A)
        ((P.coefficient.app A).hom.hom.hom x) := by
  change (P.coefficient.app A).hom.hom.hom (D.representation A D.frobenius x) =
    standardD.representation (realization.obj A) standardD.frobenius
      ((P.coefficient.app A).hom.hom.hom x)
  rw [← P.frobenius_eq]
  exact P.wholeWeil A D.frobenius x

/-- Standard covariance uses the SAME inherited native conjugation. -/
theorem standard_covariance (inertiaInjective : Function.Injective standardD.inertia)
    (A : Local) (q : G)
    (x : ((realization ⋙ standardJ ⋙
      Action.res (FGModuleCat ℂ) P.originGroup.toMonoidHom).obj A).V) :
    standardD.localFrobenius.action (realization.obj A)
      ((FDRep.ρ ((realization ⋙ standardJ ⋙
        Action.res (FGModuleCat ℂ) P.originGroup.toMonoidHom).obj A)) q x) =
    (FDRep.ρ ((realization ⋙ standardJ ⋙
      Action.res (FGModuleCat ℂ) P.originGroup.toMonoidHom).obj A)) (phi q)
      (standardD.localFrobenius.action (realization.obj A) x) := by
  change standardD.localFrobenius.action (realization.obj A)
      ((standardJ.obj (realization.obj A)).ρ (P.originGroup q) x) =
    (standardJ.obj (realization.obj A)).ρ (P.originGroup (phi q))
      (standardD.localFrobenius.action (realization.obj A) x)
  rw [conjugation_eq J phi D realization standardJ standardPhi standardD P inertiaInjective q]
  exact standardD.covariance (realization.obj A) (P.originGroup q) x

end PrimeGap182.TypeIII.ArithmeticBoundaryPrimitiveWeilRealization

namespace PrimeGap182.TypeIII.StandardP1BoundaryPrimitives
universe nu g t
/-- The canonical geometric inertia inclusion into the standard Weil group is
injective. This general group-definition law refers only to interpreted
standard primitives, not to arbitrary native J/Weil selections. -/
structure PublishedInertiaInclusion
    (interpretation : ∀ S : StandardGmTraceFromFaithfulArithmeticOperations.StandardGmPrimitives.{nu},
      Primitives.{nu,g,t} S → Prop) : Prop where
  origin : ∀ (S : StandardGmTraceFromFaithfulArithmeticOperations.StandardGmPrimitives.{nu})
    (B : Primitives.{nu,g,t} S), interpretation S B →
      ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
      Function.Injective (B.originWeil E h2).inertia
end PrimeGap182.TypeIII.StandardP1BoundaryPrimitives
