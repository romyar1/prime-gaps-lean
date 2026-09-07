import TypeIIISheafOverStalk
import TypeIIIEtaleSliceSite
import TypeIIIAlgebraicallyClosedEtalePoints
import TypeIIIArtinSchreierRingGenerator

/-!
# Local triviality with p-unit coefficient rings

The projected identity section defines a map from the actual constant
module sheaf on the slice site of the Artin--Schreier cover. Its stalk
map is invertible because evaluation at the lifted root sends the
section germ to the unit 1/p; the inverse multiplies evaluation by p.

Conservative algebraically closed points show that the constructed
map is a sheaf isomorphism. The coefficient ring may have zero divisors.
This is an actual local trivialization, with no supplied stalk, rank,
or local-constancy hypothesis and no cohomological assertion.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open SheafOverStalk
open scoped Classical

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R) (E : Type u) [CommRing E] [Invertible (p : E)] (ψ : AddChar (ZMod p) E)

/-- The actual global map on the cover site obtained from the projected
identity section of the character image sheaf. -/
def artinSchreierRingCharacterLocalTrivializationMap :
    (constantSheaf ((Spec (.of R)).smallEtaleTopology.over
      (artinSchreierEtaleObject p f)) (ModuleCat.{u} E)).obj (ModuleCat.of E E) ⟶
      (artinSchreierRingCharacterImageSheaf p f E ψ).over
        (artinSchreierEtaleObject p f) :=
  constantSheafMapOfSection Over.mkIdTerminal (ModuleCat.of E E)
    ((artinSchreierRingCharacterImageSheaf p f E ψ).over (artinSchreierEtaleObject p f))
    (artinSchreierRingCharacterIdentitySectionMap p f E ψ)

/-- Under the actual constant and slice stalk comparisons, the global
map is exactly the original germ of the projected identity section. -/
theorem artinSchreierRingCharacterLocalTrivializationMap_stalk
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology)
    (t : Φ.fiber.obj (artinSchreierEtaleObject p f)) :
    (constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
        (Φ.over t).sheafFiber.map
          (artinSchreierRingCharacterLocalTrivializationMap p f E ψ) ≫
        (sheafOverStalkIso Φ t (artinSchreierRingCharacterImageSheaf p f E ψ)).hom =
      artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
        Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
          (artinSchreierRingCharacterImageSheaf p f E ψ).obj := by
  let Y := artinSchreierEtaleObject p f
  let F := artinSchreierRingCharacterImageSheaf p f E ψ
  let t₀ : (Φ.over t).fiber.obj (Over.mk (𝟙 Y)) := ⟨t, by
    change Φ.fiber.map (𝟙 Y) t = t
    exact ConcreteCategory.congr_hom (Φ.fiber.map_id Y) t⟩
  have h := constantSheafMapOfSection_stalk (Φ.over t) Over.mkIdTerminal
    (ModuleCat.of E E) (F.over Y) (artinSchreierRingCharacterIdentitySectionMap p f E ψ) t₀
  change (constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
    (Φ.over t).sheafFiber.map (artinSchreierRingCharacterLocalTrivializationMap p f E ψ) =
      artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
        (Φ.over t).toPresheafFiber (Over.mk (𝟙 Y)) t₀ (F.over Y).obj at h
  calc
    _ = ((constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
        (Φ.over t).sheafFiber.map
          (artinSchreierRingCharacterLocalTrivializationMap p f E ψ)) ≫
        (sheafOverStalkIso Φ t F).hom := (Category.assoc _ _ _).symm
    _ = (artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
        (Φ.over t).toPresheafFiber (Over.mk (𝟙 Y)) t₀ (F.over Y).obj) ≫
        (sheafOverStalkIso Φ t F).hom :=
      congrArg (fun q => q ≫ (sheafOverStalkIso Φ t F).hom) h
    _ = artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
        ((Φ.over t).toPresheafFiber (Over.mk (𝟙 Y)) t₀ (F.over Y).obj ≫
        (sheafOverStalkIso Φ t F).hom) := Category.assoc _ _ _
    _ = _ := congrArg (fun q => artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫ q)
      (presheafOverStalkIso_germ Φ t F.obj (Over.mk (𝟙 Y)) t₀)

/-- The map on the slice has an invertible actual stalk at every lift
of an algebraically closed geometric point of the original affine base. -/
theorem artinSchreierRingCharacterLocalTrivializationMap_stalk_isIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (q : Spec (.of Ω) ⟶ Spec (.of R))
    (t : (Scheme.pointSmallEtale q).fiber.obj (artinSchreierEtaleObject p f)) :
    IsIso (((Scheme.pointSmallEtale q).over t).sheafFiber.map
      (artinSchreierRingCharacterLocalTrivializationMap p f E ψ)) := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective q
  let : Algebra R Ω := g.hom.toAlgebra
  let : CharP Ω p := artinSchreierPointField_charP p R Ω
  let : Algebra (ZMod p) Ω := (ZMod.castHom (dvd_refl p) Ω).toAlgebra
  let Φ := Scheme.pointSmallEtale (Spec.map g)
  let F := artinSchreierRingCharacterImageSheaf p f E ψ
  let e := constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)
  let d := sheafOverStalkIso Φ t F
  let m := (Φ.over t).sheafFiber.map
    (artinSchreierRingCharacterLocalTrivializationMap p f E ψ)
  have hc : IsIso (e.inv ≫ m ≫ d.hom) := by
    change IsIso ((constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
      (Φ.over t).sheafFiber.map
        (artinSchreierRingCharacterLocalTrivializationMap p f E ψ) ≫
      (sheafOverStalkIso Φ t F).hom)
    rw [artinSchreierRingCharacterLocalTrivializationMap_stalk]
    exact artinSchreierRingCharacterIdentitySectionMap_stalk_isIso p R Ω Ω f E ψ t
  exact (isIso_comp_right_iff m d.hom).mp
    ((isIso_comp_left_iff e.inv (m ≫ d.hom)).mp hc)

/-- The actual section map is an isomorphism of sheaves on the cover site.
The stalk detection is supplied by the proved geometric point family. -/
theorem artinSchreierRingCharacterLocalTrivializationMap_isIso :
    IsIso (artinSchreierRingCharacterLocalTrivializationMap p f E ψ) := by
  let S := Spec (.of R)
  let Y := artinSchreierEtaleObject p f
  have hP := (algebraicClosureEtalePoints_isConservative S).over Y
  apply ((hP.jointlyReflectIsomorphisms (ModuleCat.{u} E)).isIso_iff
    (artinSchreierRingCharacterLocalTrivializationMap p f E ψ)).mpr
  rintro ⟨_, ⟨⟨⟨_, ⟨s⟩⟩, t⟩⟩⟩
  exact artinSchreierRingCharacterLocalTrivializationMap_stalk_isIso p f E ψ
    (AlgebraicClosure (S.residueField s)) (algebraicClosureEtalePointMap S s) t

/-- The actual character image sheaf becomes the constant rank-one
module sheaf on its finite étale Artin--Schreier cover. -/
def artinSchreierRingCharacterLocalTrivialization :
    (artinSchreierRingCharacterImageSheaf p f E ψ).over (artinSchreierEtaleObject p f) ≅
      (constantSheaf ((Spec (.of R)).smallEtaleTopology.over
        (artinSchreierEtaleObject p f)) (ModuleCat.{u} E)).obj (ModuleCat.of E E) := by
  let := artinSchreierRingCharacterLocalTrivializationMap_isIso p f E ψ
  exact (asIso (artinSchreierRingCharacterLocalTrivializationMap p f E ψ)).symm

/-- Local constancy is witnessed by the actual constant-sheaf isomorphism. -/
theorem artinSchreierRingCharacterImageSheaf_over_isConstant :
    Sheaf.IsConstant
      ((Spec (.of R)).smallEtaleTopology.over (artinSchreierEtaleObject p f))
      ((artinSchreierRingCharacterImageSheaf p f E ψ).over (artinSchreierEtaleObject p f)) :=
  Sheaf.isConstant_of_iso _ (artinSchreierRingCharacterLocalTrivialization p f E ψ)

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterLocalTrivializationMap
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterLocalTrivializationMap_stalk
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterLocalTrivializationMap_stalk_isIso
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterLocalTrivializationMap_isIso
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterLocalTrivialization
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterImageSheaf_over_isConstant
