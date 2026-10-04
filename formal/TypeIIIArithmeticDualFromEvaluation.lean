import TypeIIIArithmeticTensorFromWeil

/-!
# Contragredient Frobenius from the same evaluation morphism

The general local Weil unit law and tensor law imply invariance of every
source evaluation morphism after monoidal specialization. Identifying the
existing dual-stalk comparison with this evaluation pairing then gives its
contragredient Frobenius equation, with the inverse action on the argument.
The evaluation data have no Frobenius compatibility premise. The perfect
dual-stalk comparison is required only for lisse source objects; the
actual second Kloosterman factor already has that proof.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

namespace PrimeGap182.TypeIII.ArithmeticDualFromEvaluation
open LocalWeilAction ArithmeticTensorFromWeil TensorListRepresentation

universe u v a b w c z d
variable {Local : Type u} [Category.{v} Local] [MonoidalCategory Local]
  {G : Type w} [Group G] {J : Local ⥤ FDRep ℂ G} [J.Monoidal]
  {phi : G →* G} (W : LocalWeilAction.Data J phi)

/-- The tensor unit has trivial action for every element of the common
Weil group. This is a general local-stalk unit law. -/
structure UnitRules : Prop where
  action : ∀ (g : W.Weil) x, W.representation (𝟙_ Local) g x = x

variable {Input : Type a} [Category.{b} Input] [MonoidalCategory Input]
  (along : Input ⥤ Local) [along.Monoidal] (U : UnitRules W)

include U in
omit [J.Monoidal] in
/-- The image of the source unit is trivial under the same Weil action,
using the actual unit isomorphism of the specialization functor. -/
theorem unit_action (g : W.Weil) (x : ((along ⋙ J).obj (𝟙_ Input)).V) :
    W.representation (along.obj (𝟙_ Input)) g x = x := by
  let e := equivOfIso (J.mapIso (Functor.Monoidal.εIso along))
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
  change W.representation (along.obj (𝟙_ Input)) g
      ((J.map (Functor.Monoidal.εIso along).hom).hom.hom y) = _
  rw [← W.natural, U.action]
  rfl

variable (dual : Inputᵒᵖ ⥤ Input)
  (ev : ∀ A, dual.obj (op A) ⊗ A ⟶ 𝟙_ Input)

/-- Evaluate through the actual source morphism and the two canonical
monoidal comparisons of the composite stalk functor. -/
def pairing (A : Input) (x : ((along ⋙ J).obj (dual.obj (op A))).V)
    (y : ((along ⋙ J).obj A).V) : ℂ :=
  (equivOfIso (Functor.Monoidal.εIso (along ⋙ J))).toLinearEquiv.symm
    (((along ⋙ J).map (ev A)).hom.hom
      ((Functor.LaxMonoidal.μ (along ⋙ J) (dual.obj (op A)) A).hom.hom (x ⊗ₜ[ℂ] y)))

variable (R : ArithmeticTensorFromWeil.TensorRules W)

include U R in
/-- Every evaluation morphism is invariant: tensor equivariance, then
naturality of that exact morphism, then the unit law. -/
theorem pairing_invariant (A : Input) (g : W.Weil)
    (x : ((along ⋙ J).obj (dual.obj (op A))).V) (y : ((along ⋙ J).obj A).V) :
    pairing along dual ev A
      (W.representation (along.obj (dual.obj (op A))) g x)
      (W.representation (along.obj A) g y) = pairing along dual ev A x y := by
  have ht := tensor_composition W along R (dual.obj (op A)) A g (x ⊗ₜ[ℂ] y)
  simp only [TensorProduct.map_tmul] at ht
  change (Functor.LaxMonoidal.μ (along ⋙ J) (dual.obj (op A)) A).hom.hom
      (W.representation (along.obj (dual.obj (op A))) g x ⊗ₜ[ℂ]
        W.representation (along.obj A) g y) =
    W.representation (along.obj (dual.obj (op A) ⊗ A)) g
      ((Functor.LaxMonoidal.μ (along ⋙ J) (dual.obj (op A)) A).hom.hom (x ⊗ₜ[ℂ] y)) at ht
  unfold pairing
  rw [ht]
  have hn := W.natural (along.map (ev A)) g
    ((Functor.LaxMonoidal.μ (along ⋙ J) (dual.obj (op A)) A).hom.hom (x ⊗ₜ[ℂ] y))
  change ((along ⋙ J).map (ev A)).hom.hom
      (W.representation (along.obj (dual.obj (op A) ⊗ A)) g
        ((Functor.LaxMonoidal.μ (along ⋙ J) (dual.obj (op A)) A).hom.hom (x ⊗ₜ[ℂ] y))) =
    W.representation (along.obj (𝟙_ Input)) g
      (((along ⋙ J).map (ev A)).hom.hom
        ((Functor.LaxMonoidal.μ (along ⋙ J) (dual.obj (op A)) A).hom.hom (x ⊗ₜ[ℂ] y))) at hn
  rw [hn, unit_action W along U]

variable (Good : Input → Prop) (e : ∀ A, Good A → ((along ⋙ J).obj (dual.obj (op A))).V ≃ₗ[ℂ]
  Module.Dual ℂ ((along ⋙ J).obj A).V)

/-- The supplied dual-stalk comparison is the pairing induced by the
same source evaluation morphism. This equation contains no Weil operator. -/
structure Comparison : Prop where
  evaluation : ∀ A (hA : Good A) x y, e A hA x y = pairing along dual ev A x y

include U R in
/-- Evaluation invariance forces the contragredient action, with the
inverse Frobenius on the argument rather than an extra arithmetic premise. -/
theorem contragredient (P : Comparison along dual ev Good e) (A : Input) (hA : Good A)
    (x : ((along ⋙ J).obj (dual.obj (op A))).V) :
    e A hA (W.localFrobenius.action (along.obj (dual.obj (op A))) x) =
      (W.localFrobenius.action (along.obj A)).symm.toLinearMap.dualMap (e A hA x) := by
  apply LinearMap.ext
  intro y
  change e A hA (W.localFrobenius.action (along.obj (dual.obj (op A))) x) y =
    e A hA x ((W.localFrobenius.action (along.obj A)).symm y)
  rw [P.evaluation, P.evaluation]
  have h := pairing_invariant W along U dual ev R A W.frobenius x
    ((W.localFrobenius.action (along.obj A)).symm y)
  change pairing along dual ev A
      (W.localFrobenius.action (along.obj (dual.obj (op A))) x)
      (W.localFrobenius.action (along.obj A)
        ((W.localFrobenius.action (along.obj A)).symm y)) =
      pairing along dual ev A x ((W.localFrobenius.action (along.obj A)).symm y) at h
  rw [(W.localFrobenius.action (along.obj A)).apply_symm_apply] at h
  exact h

section Boundary
open PublishedPhysicalConstruction ArithmeticZeroFromSpecialization
variable {Point : Type c} {C : Type} [Category.{z} C] [Abelian C]
  (O : CurveDataFromOperations.Observables Input Point)
  {H : CohomologyData Input C} {F : C ⥤ ModuleCat ℂ}
  {Ginf : Type d} [Group Ginf]
  (M : BoundaryMaps (Ginf := Ginf) (O.curveData dual) H F dual (along ⋙ J))

include U R in
omit [Abelian C] in
/-- The boundary uses its original dual comparison, identified with the
same evaluation pairing; its former Frobenius clause is now derived. -/
theorem boundary_dualRule
    (P : Comparison along dual ev O.Lisse (fun A hA => (M.dual A hA).toLinearEquiv)) :
    ArithmeticTensorFromWeil.DualRule W along O dual M where
  natural A hA x := by
    change (equivOfIso ((along ⋙ J).mapIso (Iso.refl (dual.obj (op A))))).trans
        (M.dual A hA) (W.localFrobenius.action (along.obj (dual.obj (op A))) x) =
      (W.localFrobenius.action (along.obj A)).symm.toLinearMap.dualMap
        ((equivOfIso ((along ⋙ J).mapIso (Iso.refl (dual.obj (op A))))).trans (M.dual A hA) x)
    have h : (along ⋙ J).mapIso (Iso.refl (dual.obj (op A))) =
        Iso.refl ((along ⋙ J).obj (dual.obj (op A))) := by
      ext
      simp
    rw [h]
    exact contragredient W along U dual ev R O.Lisse (fun A hA => (M.dual A hA).toLinearEquiv) P A hA x

end Boundary

end PrimeGap182.TypeIII.ArithmeticDualFromEvaluation

#print axioms PrimeGap182.TypeIII.ArithmeticDualFromEvaluation.unit_action
#print axioms PrimeGap182.TypeIII.ArithmeticDualFromEvaluation.pairing
#print axioms PrimeGap182.TypeIII.ArithmeticDualFromEvaluation.pairing_invariant

#print axioms PrimeGap182.TypeIII.ArithmeticDualFromEvaluation.contragredient
#print axioms PrimeGap182.TypeIII.ArithmeticDualFromEvaluation.boundary_dualRule
