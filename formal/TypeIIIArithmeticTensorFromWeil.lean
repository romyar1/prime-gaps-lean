import TypeIIIArithmeticZeroFromSpecialization
import TypeIIICurveDataFromOperations
import TypeIIILocalWeilAction

/-!
# Tensor Frobenius through the same monoidal specialization

General tensor compatibility of the local Weil stalk, for every Weil
element and pair of local sheaves, implies tensor compatibility after any
monoidal specialization. The proof uses the actual composite tensor map
and the Weil action's naturality on the specialization's tensor morphism.
The application then uses exactly the boundary's zero-tensor comparison.
The general local tensor law and separate dual law remain explicit.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ArithmeticTensorFromWeil
open ArithmeticSourceTransport ArithmeticRestrictionFromStalks
open TensorListRepresentation LocalWeilAction

universe u v a b c w z d
section Tensor

variable {Local : Type u} [Category.{v} Local] [MonoidalCategory Local]
  {G : Type w} [Group G] {J : Local ⥤ FDRep ℂ G} [J.Monoidal]
  {phi : G →* G} (W : LocalWeilAction.Data J phi)

/-- The canonical local tensor morphism is equivariant for every Weil
operator. This is the general tensor law of the same arithmetic stalk. -/
structure TensorRules : Prop where
  natural : ∀ A B (g : W.Weil) x,
    (Functor.LaxMonoidal.μ J A B).hom.hom
      (TensorProduct.map (W.representation A g) (W.representation B g) x) =
      W.representation (A ⊗ B) g ((Functor.LaxMonoidal.μ J A B).hom.hom x)

variable {Input : Type a} [Category.{b} Input] [MonoidalCategory Input]
  (along : Input ⥤ Local) [along.Monoidal] (R : TensorRules W)

include R

/-- The composite tensor comparison intertwines every Weil element;
its second map is exactly the image of the specialization's tensor map. -/
theorem tensor_composition (A B : Input) (g : W.Weil)
    (x : ((along ⋙ J).obj A ⊗ (along ⋙ J).obj B).V) :
    equivOfIso (Functor.Monoidal.μIso (along ⋙ J) A B)
      (TensorProduct.map (W.representation (along.obj A) g)
        (W.representation (along.obj B) g) x) =
      W.representation (along.obj (A ⊗ B)) g
        (equivOfIso (Functor.Monoidal.μIso (along ⋙ J) A B) x) := by
  change (Functor.LaxMonoidal.μ (along ⋙ J) A B).hom.hom _ =
    W.representation (along.obj (A ⊗ B)) g
      ((Functor.LaxMonoidal.μ (along ⋙ J) A B).hom.hom x)
  rw [Functor.LaxMonoidal.comp_μ]
  change (J.map (Functor.LaxMonoidal.μ along A B)).hom.hom
      ((Functor.LaxMonoidal.μ J (along.obj A) (along.obj B)).hom.hom _) = _
  rw [R.natural]
  exact W.natural (Functor.LaxMonoidal.μ along A B) g _

/-- Invert the same tensor comparison and evaluate at geometric Frobenius. -/
theorem tensor_inverse (A B : Input) (x : ((along ⋙ J).obj (A ⊗ B)).V) :
    (equivOfIso (Functor.Monoidal.μIso (along ⋙ J) A B)).symm
      (W.localFrobenius.action (along.obj (A ⊗ B)) x) =
      TensorProduct.map (W.localFrobenius.action (along.obj A)).toLinearMap
        (W.localFrobenius.action (along.obj B)).toLinearMap
        ((equivOfIso (Functor.Monoidal.μIso (along ⋙ J) A B)).symm x) := by
  let e := equivOfIso (Functor.Monoidal.μIso (along ⋙ J) A B)
  have he (y : ((along ⋙ J).obj (A ⊗ B)).V) : e (e.symm y) = y :=
    e.toLinearEquiv.apply_symm_apply y
  apply e.toLinearEquiv.injective
  change e (e.symm (W.localFrobenius.action (along.obj (A ⊗ B)) x)) = _
  rw [he]
  have h := tensor_composition W along R A B W.frobenius (e.symm x)
  change e (TensorProduct.map (W.localFrobenius.action (along.obj A)).toLinearMap
    (W.localFrobenius.action (along.obj B)).toLinearMap (e.symm x)) =
      W.localFrobenius.action (along.obj (A ⊗ B)) (e (e.symm x)) at h
  rw [he] at h
  exact h.symm

end Tensor

section Boundary
open PublishedPhysicalConstruction ArithmeticZeroFromSpecialization

variable {Local : Type u} [Category.{v} Local] [MonoidalCategory Local]
  {G : Type w} [Group G] {J : Local ⥤ FDRep ℂ G} [J.Monoidal]
  {phi : G →* G} (W : LocalWeilAction.Data J phi)
  {Input : Type a} [Category.{b} Input] [MonoidalCategory Input]
  (along : Input ⥤ Local) [along.Monoidal]
  {Point : Type c} {C : Type} [Category.{z} C] [Abelian C]
  (O : CurveDataFromOperations.Observables Input Point) (dual : Inputᵒᵖ ⥤ Input)
  {H : CohomologyData Input C} {F : C ⥤ ModuleCat ℂ}
  {Ginf : Type d} [Group Ginf]
  (M : BoundaryMaps (Ginf := Ginf) (O.curveData dual) H F dual (along ⋙ J))

local notation "Z" => M.data.restriction (O.tensorComparison dual) (O.dualComparison dual)
local notation "S" => ArithmeticZeroFromSpecialization.stalks along J

/-- The dual comparison is retained separately; no tensor Frobenius law
for the original source is supplied here. -/
structure DualRule : Prop where
  natural : ∀ A (hA : O.Lisse A) x,
    (Z).dualZero A hA ((S).action W.localFrobenius ((O.curveData dual).dual A) x) =
      ((S).action W.localFrobenius A).symm.toLinearMap.dualMap ((Z).dualZero A hA x)

omit [Abelian C] in
/-- Apply the general local tensor law through specialization and the
boundary's actual tensor comparison, retaining its separate dual law. -/
theorem tensorDualRules (R : TensorRules W) (D : DualRule W along O dual M) :
    ArithmeticRestrictionFromStalks.TensorDualRules W.localFrobenius Z S where
  tensor_natural A B x := by
    change equivOfIso ((along ⋙ J).mapIso (Iso.refl (A ⊗ B)) ≪≫
      (Functor.Monoidal.μIso (along ⋙ J) A B).symm)
        (W.localFrobenius.action (along.obj (A ⊗ B)) x) =
      TensorProduct.map (W.localFrobenius.action (along.obj A)).toLinearMap
        (W.localFrobenius.action (along.obj B)).toLinearMap
        (equivOfIso ((along ⋙ J).mapIso (Iso.refl (A ⊗ B)) ≪≫
          (Functor.Monoidal.μIso (along ⋙ J) A B).symm) x)
    have h : (along ⋙ J).mapIso (Iso.refl (A ⊗ B)) ≪≫
        (Functor.Monoidal.μIso (along ⋙ J) A B).symm =
        (Functor.Monoidal.μIso (along ⋙ J) A B).symm := by
      ext
      simp
    rw [h]
    exact tensor_inverse W along R A B x
  dual_natural := D.natural

end Boundary

end PrimeGap182.TypeIII.ArithmeticTensorFromWeil

#print axioms PrimeGap182.TypeIII.ArithmeticTensorFromWeil.tensor_composition
#print axioms PrimeGap182.TypeIII.ArithmeticTensorFromWeil.tensor_inverse

#print axioms PrimeGap182.TypeIII.ArithmeticTensorFromWeil.tensorDualRules
