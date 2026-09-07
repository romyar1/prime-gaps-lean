import TypeIIIArtinSchreierCoefficientMaps
import TypeIIIArtinSchreierRingGenerator
import TypeIIIEtaleCoefficientRestriction

/-!
# Coefficient change on the actual character generator and its germ

The original free-sheaf coefficient map preserves the sheafified identity
generator. Its compatibility with the actual averaging projectors then
shows that the original character-image map preserves the projected
identity section. On stalks the resulting square uses the original germ
maps and the canonical scalar-restriction fiber comparison.

The arguments allow commutative coefficient rings with zero divisors.
No basis or compatibility of stalks is assumed.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ScalarMap

variable {E E' : Type u} [CommRing E] [CommRing E']

/-- The literal coefficient ring map, regarded as a linear map after
restriction of scalars on its target. -/
def coefficientRingModuleMap (r : E →+* E') :
    ModuleCat.of E E ⟶ (ModuleCat.restrictScalars r).obj (ModuleCat.of E' E') :=
  ModuleCat.ofHom (X := ModuleCat.of E E)
    (Y := (ModuleCat.restrictScalars r).obj (ModuleCat.of E' E'))
    { toFun := r
      map_add' := r.map_add
      map_smul' := by
        intro a x
        change r (a * x) = r a * r x
        exact r.map_mul a x }

@[simp] theorem coefficientRingModuleMap_apply (r : E →+* E') (a : E) :
    coefficientRingModuleMap r a = r a := rfl

end ScalarMap

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R) {E E' : Type u} [CommRing E] [CommRing E']

/-- Coefficient change preserves the original sheafified identity
generator before applying any character projector. -/
theorem artinSchreierFreeSheafCoefficientMap_identitySection (r : E →+* E') :
    (artinSchreierFreeSheafCoefficientMap p f r).hom.app
        (op (artinSchreierEtaleObject p f))
        (artinSchreierFreeSheafIdentitySection p f E) =
      artinSchreierFreeSheafIdentitySection p f E' := by
  let Y := artinSchreierEtaleObject p f
  let x : (shrinkYoneda.{u}.obj Y).obj (op Y) :=
    shrinkYonedaObjObjEquiv.symm (𝟙 Y)
  have h := congrArg (fun η => η.app (op Y) (ModuleCat.freeMk x))
    (artinSchreierFreeSheafCoefficientMap_unit p f r)
  change (artinSchreierFreeSheafCoefficientMap p f r).hom.app (op Y)
      (artinSchreierFreeSheafIdentitySection p f E) =
    (toSheafify (Spec (.of R)).smallEtaleTopology
      (artinSchreierFreePresheaf p f E')).app (op Y)
        ((freeModuleCoefficientMap r).app _ (ModuleCat.freeMk x)) at h
  rw [freeModuleCoefficientMap_generator] at h
  exact h

/-- The actual image retraction is fixed by its averaging projector. -/
theorem artinSchreierRingCharacterSheafAverage_comp_retraction
    [Invertible (p : E)] (ψ : AddChar (ZMod p) E) :
    artinSchreierRingCharacterSheafAverage p f E ψ ≫
        artinSchreierRingCharacterSheafRetraction p f E ψ =
      artinSchreierRingCharacterSheafRetraction p f E ψ := by
  rw [← artinSchreierRingCharacterSheafRetraction_comp_inclusion p f E ψ,
    Category.assoc, artinSchreierRingCharacterSheafInclusion_comp_retraction,
    Category.comp_id]

section CharacterMap

variable [Invertible (p : E)] [Invertible (p : E')]
  (ψ : AddChar (ZMod p) E) (ψ' : AddChar (ZMod p) E')
  (r : E →+* E') (hψ : ∀ a, r (ψ a) = ψ' a)

include hψ

/-- Retraction through the original source image commutes with the
original coefficient map and the actual target image retraction. -/
theorem artinSchreierRingCharacterSheafRetraction_coefficientMap :
    artinSchreierRingCharacterSheafRetraction p f E ψ ≫
        artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r =
      artinSchreierFreeSheafCoefficientMap p f r ≫
        (etaleModuleCoefficientRestriction R r).map
          (artinSchreierRingCharacterSheafRetraction p f E' ψ') := by
  rw [artinSchreierRingCharacterSheafCoefficientMap, ← Category.assoc,
    artinSchreierRingCharacterSheafRetraction_comp_inclusion,
    ← Category.assoc,
    artinSchreierRingCharacterSheafAverage_coefficientMap p f ψ ψ' r hψ,
    Category.assoc, ← Functor.map_comp,
    artinSchreierRingCharacterSheafAverage_comp_retraction]

/-- The original character coefficient map preserves the actual
projected identity section. -/
theorem artinSchreierRingCharacterSheafCoefficientMap_identitySection :
    (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r).hom.app
        (op (artinSchreierEtaleObject p f))
        (artinSchreierRingCharacterIdentitySection p f E ψ) =
      artinSchreierRingCharacterIdentitySection p f E' ψ' := by
  have h := congrArg
    (fun g => g.hom.app (op (artinSchreierEtaleObject p f))
      (artinSchreierFreeSheafIdentitySection p f E))
    (artinSchreierRingCharacterSheafRetraction_coefficientMap p f ψ ψ' r hψ)
  change (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r).hom.app
      (op (artinSchreierEtaleObject p f))
      (artinSchreierRingCharacterIdentitySection p f E ψ) =
    (artinSchreierRingCharacterSheafRetraction p f E' ψ').hom.app
      (op (artinSchreierEtaleObject p f))
      ((artinSchreierFreeSheafCoefficientMap p f r).hom.app
        (op (artinSchreierEtaleObject p f))
        (artinSchreierFreeSheafIdentitySection p f E)) at h
  rw [artinSchreierFreeSheafCoefficientMap_identitySection] at h
  exact h

/-- Scalar multiples of the actual generator obey the literal ring map. -/
theorem artinSchreierRingCharacterSheafCoefficientMap_sectionMap :
    artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
        (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r).hom.app
          (op (artinSchreierEtaleObject p f)) =
      coefficientRingModuleMap r ≫ (ModuleCat.restrictScalars r).map
        (artinSchreierRingCharacterIdentitySectionMap p f E' ψ') := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r).hom.app
      (op (artinSchreierEtaleObject p f))
      (a • artinSchreierRingCharacterIdentitySection p f E ψ) =
    r a • artinSchreierRingCharacterIdentitySection p f E' ψ'
  rw [map_smul, artinSchreierRingCharacterSheafCoefficientMap_identitySection
    p f ψ ψ' r hψ]
  rfl

/-- The original character coefficient map on the actual stalk, composed
with the canonical scalar-restriction comparison, sends the actual
generator germ according to the literal coefficient ring map. -/
theorem artinSchreierRingCharacterSheafCoefficientMap_stalk_generator
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology)
    (t : Φ.fiber.obj (artinSchreierEtaleObject p f)) :
    (artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
      Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
        (artinSchreierRingCharacterImageSheaf p f E ψ).obj) ≫
        Φ.sheafFiber.map (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r) ≫
          (Φ.sheafFiberCompIso (ModuleCat.restrictScalars r)).hom.app
            (artinSchreierRingCharacterImageSheaf p f E' ψ') =
      coefficientRingModuleMap r ≫ (ModuleCat.restrictScalars r).map
        (artinSchreierRingCharacterIdentitySectionMap p f E' ψ' ≫
          Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
            (artinSchreierRingCharacterImageSheaf p f E' ψ').obj) := by
  let Y := artinSchreierEtaleObject p f
  let L := artinSchreierRingCharacterImageSheaf p f E ψ
  let L' := artinSchreierRingCharacterImageSheaf p f E' ψ'
  let M := ModuleCat.restrictScalars r
  let c := artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r
  let g := artinSchreierRingCharacterIdentitySectionMap p f E ψ
  let g' := artinSchreierRingCharacterIdentitySectionMap p f E' ψ'
  have hn : Φ.toPresheafFiber Y t L.obj ≫ Φ.sheafFiber.map c =
      c.hom.app (op Y) ≫ Φ.toPresheafFiber Y t (L'.obj ⋙ M) :=
    Φ.toPresheafFiber_naturality c.hom Y t
  have hg : Φ.toPresheafFiber Y t (L'.obj ⋙ M) ≫
      (Φ.sheafFiberCompIso M).hom.app L' = M.map (Φ.toPresheafFiber Y t L'.obj) :=
    Φ.toPresheafFiber_presheafFiberCompIso_hom_app M Y t L'.obj
  change (g ≫ Φ.toPresheafFiber Y t L.obj) ≫ Φ.sheafFiber.map c ≫
    (Φ.sheafFiberCompIso M).hom.app L' =
      coefficientRingModuleMap r ≫ M.map (g' ≫ Φ.toPresheafFiber Y t L'.obj)
  calc
    _ = g ≫ (Φ.toPresheafFiber Y t L.obj ≫ Φ.sheafFiber.map c) ≫
        (Φ.sheafFiberCompIso M).hom.app L' := by simp only [Category.assoc]
    _ = (g ≫ c.hom.app (op Y)) ≫
        (Φ.toPresheafFiber Y t (L'.obj ⋙ M) ≫
          (Φ.sheafFiberCompIso M).hom.app L') := by
      rw [hn]
      simp only [Category.assoc]
    _ = (coefficientRingModuleMap r ≫ M.map g') ≫
        M.map (Φ.toPresheafFiber Y t L'.obj) := by
      rw [hg, artinSchreierRingCharacterSheafCoefficientMap_sectionMap p f ψ ψ' r hψ]
    _ = _ := by rw [Functor.map_comp, Category.assoc]

end CharacterMap

#print axioms coefficientRingModuleMap
#print axioms coefficientRingModuleMap_apply
#print axioms artinSchreierFreeSheafCoefficientMap_identitySection
#print axioms artinSchreierRingCharacterSheafAverage_comp_retraction
#print axioms artinSchreierRingCharacterSheafRetraction_coefficientMap
#print axioms artinSchreierRingCharacterSheafCoefficientMap_identitySection
#print axioms artinSchreierRingCharacterSheafCoefficientMap_sectionMap
#print axioms artinSchreierRingCharacterSheafCoefficientMap_stalk_generator

end PrimeGap182.TypeIII
