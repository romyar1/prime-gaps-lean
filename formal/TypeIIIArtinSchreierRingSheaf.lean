import TypeIIIArtinSchreierSheafProjection
import Mathlib.Algebra.GroupWithZero.Invertible

/-!
# The Artin--Schreier character sheaf with ring coefficients

The coefficient ring is commutative and p is a unit. The construction
uses the existing free sheaf of the actual cover, with its actual deck
maps. Averaging uses the inverse of this unit, so it also makes sense
over finite torsion coefficient rings that are not fields.

The actual average is idempotent and its image is a retract. Its stalk
is the image of the explicit average on the actual free cover fiber.
This module supplies no cohomology or weight estimate.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R)

section RingCoefficients

variable (E : Type u) [CommRing E] [Invertible (p : E)]
  (ψ : AddChar (ZMod p) E)

/-- The actual positive-weight character average over a coefficient
ring in which p is invertible. -/
def artinSchreierRingCharacterPresheafAverage :
    artinSchreierFreePresheaf p f E ⟶ artinSchreierFreePresheaf p f E :=
  ⅟(p : E) • ∑ a : ZMod p,
    ψ a • artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a)

/-- Sheafification of the actual ring-coefficient character average. -/
def artinSchreierRingCharacterSheafAverage :
    artinSchreierFreeSheaf p f E ⟶ artinSchreierFreeSheaf p f E :=
  (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
    (artinSchreierRingCharacterPresheafAverage p f E ψ)

/-- The actual character image sheaf with p-unit ring coefficients. -/
def artinSchreierRingCharacterImageSheaf :
    Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E) :=
  Abelian.image (artinSchreierRingCharacterSheafAverage p f E ψ)

/-- The actual stalk of the image sheaf is the image of the actual
stalk endomorphism, using exactness of the point fiber functor. -/
def artinSchreierRingCharacterImageSheaf_stalkImageIso
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    (Φ.sheafFiber (A := ModuleCat.{u} E)).obj
        (artinSchreierRingCharacterImageSheaf p f E ψ) ≅
      Abelian.image
        (Φ.sheafFiber.map (artinSchreierRingCharacterSheafAverage p f E ψ)) :=
  Abelian.PreservesImage.iso Φ.sheafFiber
    (artinSchreierRingCharacterSheafAverage p f E ψ)

/-- The same positive-weight average on the free module of the
actual fiber of the finite étale cover. -/
def artinSchreierRingCharacterFreeFiberAverage
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    (ModuleCat.free E).obj (Φ.fiber.obj (artinSchreierEtaleObject p f)) ⟶
      (ModuleCat.free E).obj (Φ.fiber.obj (artinSchreierEtaleObject p f)) :=
  ⅟(p : E) • ∑ a : ZMod p,
    ψ a • (ModuleCat.free E).map (Φ.fiber.map (artinSchreierEtaleDeck p f a))

set_option backward.isDefEq.respectTransparency.types false in
/-- The original free-sheaf stalk comparison intertwines the actual
ring-coefficient average and the explicit cover-fiber average. -/
theorem artinSchreierRingCharacterSheafAverage_stalk
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology) :
    Φ.sheafFiber.map (artinSchreierRingCharacterSheafAverage p f E ψ) ≫
        (artinSchreierFreeSheaf_stalkIso p f E Φ).hom =
      (artinSchreierFreeSheaf_stalkIso p f E Φ).hom ≫
        artinSchreierRingCharacterFreeFiberAverage p f E ψ Φ := by
  let := etaleModulePresheafFiber_linear E Φ
  let : (Φ.presheafFiber (A := ModuleCat.{u} E)).Additive :=
    { map_add := by
        intro P Q g h
        apply Φ.presheafFiber_hom_ext
        intro X x
        simp only [Φ.toPresheafFiber_naturality, NatTrans.app_add,
          Preadditive.add_comp, Preadditive.comp_add] }
  let F := presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E) ⋙
    Φ.sheafFiber
  let : F.Linear E := Functor.linear_of_iso E
    (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u} E)).symm
  let : F.Additive := Functor.additive_of_iso
    (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u} E)).symm
  change F.map (artinSchreierRingCharacterPresheafAverage p f E ψ) ≫ _ = _
  simp only [artinSchreierRingCharacterPresheafAverage,
    artinSchreierRingCharacterFreeFiberAverage, Functor.map_smul, Functor.map_sum,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum]
  apply congrArg (fun h => ⅟(p : E) • h)
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun h => ψ a • h)
    (artinSchreierFreeSheaf_stalk_naturality p f E Φ (artinSchreierEtaleDeck p f a))

/-- A deck map after the positive average has the negative character
scalar. The identity is proved by reindexing the actual deck maps. -/
theorem artinSchreierRingCharacterPresheafAverage_comp_deck (b : ZMod p) :
    artinSchreierRingCharacterPresheafAverage p f E ψ ≫
        artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f b) =
      ψ (-b) • artinSchreierRingCharacterPresheafAverage p f E ψ := by
  have hsum :
      (∑ a : ZMod p, ψ a • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f (a + b))) =
      ψ (-b) • ∑ a : ZMod p, ψ a • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f a) := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addRight b) _ _ ?_
    intro a
    change ψ a • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f (a + b)) =
      ψ (-b) • (ψ (a + b) • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f (a + b)))
    have hψ : ψ (-b) * ψ (a + b) = ψ a := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      abel
    rw [smul_smul, hψ]
  simp only [artinSchreierRingCharacterPresheafAverage,
    CategoryTheory.Linear.smul_comp, Preadditive.sum_comp,
    artinSchreierFreePresheafMap_deck_add]
  rw [hsum, smul_comm]

/-- The p-unit normalization makes the actual average idempotent. -/
theorem artinSchreierRingCharacterPresheafAverage_idempotent :
    artinSchreierRingCharacterPresheafAverage p f E ψ ≫
        artinSchreierRingCharacterPresheafAverage p f E ψ =
      artinSchreierRingCharacterPresheafAverage p f E ψ := by
  change artinSchreierRingCharacterPresheafAverage p f E ψ ≫
      (⅟(p : E) • ∑ a : ZMod p, ψ a •
        artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a)) = _
  simp only [CategoryTheory.Linear.comp_smul, Preadditive.comp_sum,
    artinSchreierRingCharacterPresheafAverage_comp_deck, smul_smul,
    ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_smul,
    Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [← Nat.cast_smul_eq_nsmul E, smul_smul, invOf_mul_self, one_smul]

/-- The actual sheafification preserves this idempotence. -/
theorem artinSchreierRingCharacterSheafAverage_idempotent :
    artinSchreierRingCharacterSheafAverage p f E ψ ≫
        artinSchreierRingCharacterSheafAverage p f E ψ =
      artinSchreierRingCharacterSheafAverage p f E ψ := by
  change (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
      (artinSchreierRingCharacterPresheafAverage p f E ψ) ≫
      (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
        (artinSchreierRingCharacterPresheafAverage p f E ψ) = _
  rw [← Functor.map_comp, artinSchreierRingCharacterPresheafAverage_idempotent]
  rfl

/-- The actual ring-coefficient image factorization. -/
def artinSchreierRingCharacterSheafRetraction :
    artinSchreierFreeSheaf p f E ⟶ artinSchreierRingCharacterImageSheaf p f E ψ :=
  Abelian.factorThruImage (artinSchreierRingCharacterSheafAverage p f E ψ)

/-- Factorization through the actual image gives the original average. -/
theorem artinSchreierRingCharacterSheafRetraction_comp_inclusion :
    artinSchreierRingCharacterSheafRetraction p f E ψ ≫
        Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ) =
      artinSchreierRingCharacterSheafAverage p f E ψ :=
  Abelian.image.fac _

/-- Idempotence makes the actual image inclusion split. -/
theorem artinSchreierRingCharacterSheafInclusion_comp_retraction :
    Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ) ≫
        artinSchreierRingCharacterSheafRetraction p f E ψ =
      𝟙 (artinSchreierRingCharacterImageSheaf p f E ψ) := by
  let P := artinSchreierRingCharacterSheafAverage p f E ψ
  change Abelian.image.ι P ≫ Abelian.factorThruImage P = 𝟙 _
  apply (cancel_epi (Abelian.factorThruImage P)).mp
  apply (cancel_mono (Abelian.image.ι P)).mp
  calc
    (Abelian.factorThruImage P ≫
        (Abelian.image.ι P ≫ Abelian.factorThruImage P)) ≫ Abelian.image.ι P =
        (Abelian.factorThruImage P ≫ Abelian.image.ι P) ≫
          (Abelian.factorThruImage P ≫ Abelian.image.ι P) := by
      simp only [Category.assoc]
    _ = P ≫ P := by rw [Abelian.image.fac]
    _ = P := artinSchreierRingCharacterSheafAverage_idempotent p f E ψ
    _ = (Abelian.factorThruImage P ≫ 𝟙 _) ≫ Abelian.image.ι P := by
      rw [Category.comp_id, Abelian.image.fac]

/-- The actual character image sheaf is a retract of the original
free sheaf, over every commutative coefficient ring with p invertible. -/
def artinSchreierRingCharacterImageSheafRetract :
    Retract (artinSchreierRingCharacterImageSheaf p f E ψ)
      (artinSchreierFreeSheaf p f E) where
  i := Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)
  r := artinSchreierRingCharacterSheafRetraction p f E ψ
  retract := artinSchreierRingCharacterSheafInclusion_comp_retraction p f E ψ

end RingCoefficients

section FieldSpecialization

variable (E : Type u) [Field E] [Invertible (p : E)]
  (ψ : AddChar (ZMod p) E)

/-- Over a field, the ring average is literally the existing average;
the inverse of the unit agrees with field inversion. -/
theorem artinSchreierRingCharacterPresheafAverage_field :
    artinSchreierRingCharacterPresheafAverage p f E ψ =
      artinSchreierCharacterPresheafAverage p f E ψ := by
  simp only [artinSchreierRingCharacterPresheafAverage,
    artinSchreierCharacterPresheafAverage, invOf_eq_inv]

/-- The ring construction preserves the actual field-coefficient
sheaf endomorphism already used by the trace theorems. -/
theorem artinSchreierRingCharacterSheafAverage_field :
    artinSchreierRingCharacterSheafAverage p f E ψ =
      artinSchreierCharacterSheafAverage p f E ψ := by
  simp only [artinSchreierRingCharacterSheafAverage,
    artinSchreierCharacterSheafAverage,
    artinSchreierRingCharacterPresheafAverage_field]
  rfl

/-- The p-unit ring image sheaf is the existing field image sheaf
when the coefficient ring is a field. -/
theorem artinSchreierRingCharacterImageSheaf_field :
    artinSchreierRingCharacterImageSheaf p f E ψ =
      artinSchreierCharacterImageSheaf p f E ψ := by
  simp only [artinSchreierRingCharacterImageSheaf,
    artinSchreierCharacterImageSheaf, artinSchreierRingCharacterSheafAverage_field]

end FieldSpecialization

#print axioms artinSchreierRingCharacterPresheafAverage
#print axioms artinSchreierRingCharacterSheafAverage
#print axioms artinSchreierRingCharacterImageSheaf
#print axioms artinSchreierRingCharacterImageSheaf_stalkImageIso
#print axioms artinSchreierRingCharacterFreeFiberAverage
#print axioms artinSchreierRingCharacterSheafAverage_stalk
#print axioms artinSchreierRingCharacterPresheafAverage_comp_deck
#print axioms artinSchreierRingCharacterPresheafAverage_idempotent
#print axioms artinSchreierRingCharacterSheafAverage_idempotent
#print axioms artinSchreierRingCharacterSheafRetraction
#print axioms artinSchreierRingCharacterSheafRetraction_comp_inclusion
#print axioms artinSchreierRingCharacterSheafInclusion_comp_retraction
#print axioms artinSchreierRingCharacterImageSheafRetract
#print axioms artinSchreierRingCharacterPresheafAverage_field
#print axioms artinSchreierRingCharacterSheafAverage_field
#print axioms artinSchreierRingCharacterImageSheaf_field

end PrimeGap182.TypeIII
