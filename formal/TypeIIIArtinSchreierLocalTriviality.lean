import TypeIIISheafOverStalk
import TypeIIIEtaleSliceSite
import TypeIIIAlgebraicallyClosedEtalePoints
import TypeIIIArtinSchreierCharacterGenerator

/-!
# Local triviality of the actual Artin--Schreier character sheaf

The projected identity section defines a map from the constant module
sheaf on the slice site over the actual Artin--Schreier cover.  Its
stalk map is the germ of that section: the projected delta function has
value 1/p at its chosen lift and spans the actual character stalk.
Conservative algebraically closed geometric points therefore show
that this constructed map is an isomorphism.

The coefficient field may be finite.  The hypothesis that p is nonzero
in it is essential.  These are actual locally constant module sheaves;
no compactly supported cohomology or ell-adic comparison is asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open SheafOverStalk
open scoped Classical

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R) (E : Type u) [Field E] (ψ : AddChar (ZMod p) E)

/-- The actual global map on the cover site obtained from the projected
identity section of the character image sheaf. -/
def artinSchreierCharacterLocalTrivializationMap :
    (constantSheaf ((Spec (.of R)).smallEtaleTopology.over
      (artinSchreierEtaleObject p f)) (ModuleCat.{u} E)).obj (ModuleCat.of E E) ⟶
      (artinSchreierCharacterImageSheaf p f E ψ).over
        (artinSchreierEtaleObject p f) :=
  constantSheafMapOfSection Over.mkIdTerminal (ModuleCat.of E E)
    ((artinSchreierCharacterImageSheaf p f E ψ).over (artinSchreierEtaleObject p f))
    (artinSchreierCharacterIdentitySectionMap p f E ψ)

/-- Under the actual constant and slice stalk comparisons, the global
map is exactly the original germ of the projected identity section. -/
theorem artinSchreierCharacterLocalTrivializationMap_stalk
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology)
    (t : Φ.fiber.obj (artinSchreierEtaleObject p f)) :
    (constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
        (Φ.over t).sheafFiber.map
          (artinSchreierCharacterLocalTrivializationMap p f E ψ) ≫
        (sheafOverStalkIso Φ t (artinSchreierCharacterImageSheaf p f E ψ)).hom =
      artinSchreierCharacterIdentitySectionMap p f E ψ ≫
        Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
          (artinSchreierCharacterImageSheaf p f E ψ).obj := by
  let Y := artinSchreierEtaleObject p f
  let F := artinSchreierCharacterImageSheaf p f E ψ
  let t₀ : (Φ.over t).fiber.obj (Over.mk (𝟙 Y)) := ⟨t, by
    change Φ.fiber.map (𝟙 Y) t = t
    exact ConcreteCategory.congr_hom (Φ.fiber.map_id Y) t⟩
  have h := constantSheafMapOfSection_stalk (Φ.over t) Over.mkIdTerminal
    (ModuleCat.of E E) (F.over Y) (artinSchreierCharacterIdentitySectionMap p f E ψ) t₀
  change (constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
    (Φ.over t).sheafFiber.map (artinSchreierCharacterLocalTrivializationMap p f E ψ) =
      artinSchreierCharacterIdentitySectionMap p f E ψ ≫
        (Φ.over t).toPresheafFiber (Over.mk (𝟙 Y)) t₀ (F.over Y).obj at h
  calc
    _ = ((constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
        (Φ.over t).sheafFiber.map
          (artinSchreierCharacterLocalTrivializationMap p f E ψ)) ≫
        (sheafOverStalkIso Φ t F).hom := (Category.assoc _ _ _).symm
    _ = (artinSchreierCharacterIdentitySectionMap p f E ψ ≫
        (Φ.over t).toPresheafFiber (Over.mk (𝟙 Y)) t₀ (F.over Y).obj) ≫
        (sheafOverStalkIso Φ t F).hom :=
      congrArg (fun q => q ≫ (sheafOverStalkIso Φ t F).hom) h
    _ = artinSchreierCharacterIdentitySectionMap p f E ψ ≫
        ((Φ.over t).toPresheafFiber (Over.mk (𝟙 Y)) t₀ (F.over Y).obj ≫
        (sheafOverStalkIso Φ t F).hom) := Category.assoc _ _ _
    _ = _ := congrArg (fun q => artinSchreierCharacterIdentitySectionMap p f E ψ ≫ q)
      (presheafOverStalkIso_germ Φ t F.obj (Over.mk (𝟙 Y)) t₀)

/-- The map on the slice has an invertible actual stalk at every lift
of an algebraically closed geometric point of the original affine base. -/
theorem artinSchreierCharacterLocalTrivializationMap_stalk_isIso
    (hpE : (p : E) ≠ 0) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (q : Spec (.of Ω) ⟶ Spec (.of R))
    (t : (Scheme.pointSmallEtale q).fiber.obj (artinSchreierEtaleObject p f)) :
    IsIso (((Scheme.pointSmallEtale q).over t).sheafFiber.map
      (artinSchreierCharacterLocalTrivializationMap p f E ψ)) := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective q
  let : Algebra R Ω := g.hom.toAlgebra
  let : CharP Ω p := artinSchreierPointField_charP p R Ω
  let : Algebra (ZMod p) Ω := (ZMod.castHom (dvd_refl p) Ω).toAlgebra
  let Φ := Scheme.pointSmallEtale (Spec.map g)
  let F := artinSchreierCharacterImageSheaf p f E ψ
  let e := constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)
  let d := sheafOverStalkIso Φ t F
  let m := (Φ.over t).sheafFiber.map
    (artinSchreierCharacterLocalTrivializationMap p f E ψ)
  have hc : IsIso (e.inv ≫ m ≫ d.hom) := by
    change IsIso ((constantSheafStalkIso (Φ.over t) (ModuleCat.of E E)).inv ≫
      (Φ.over t).sheafFiber.map
        (artinSchreierCharacterLocalTrivializationMap p f E ψ) ≫
      (sheafOverStalkIso Φ t F).hom)
    rw [artinSchreierCharacterLocalTrivializationMap_stalk]
    exact artinSchreierCharacterIdentitySectionMap_stalk_isIso p R Ω Ω f E ψ hpE t
  exact (isIso_comp_right_iff m d.hom).mp
    ((isIso_comp_left_iff e.inv (m ≫ d.hom)).mp hc)

/-- The actual section map is an isomorphism of sheaves on the cover site.
The stalk detection is supplied by the proved geometric point family. -/
theorem artinSchreierCharacterLocalTrivializationMap_isIso (hpE : (p : E) ≠ 0) :
    IsIso (artinSchreierCharacterLocalTrivializationMap p f E ψ) := by
  let S := Spec (.of R)
  let Y := artinSchreierEtaleObject p f
  have hP := (algebraicClosureEtalePoints_isConservative S).over Y
  apply ((hP.jointlyReflectIsomorphisms (ModuleCat.{u} E)).isIso_iff
    (artinSchreierCharacterLocalTrivializationMap p f E ψ)).mpr
  rintro ⟨_, ⟨⟨⟨_, ⟨s⟩⟩, t⟩⟩⟩
  exact artinSchreierCharacterLocalTrivializationMap_stalk_isIso p f E ψ hpE
    (AlgebraicClosure (S.residueField s)) (algebraicClosureEtalePointMap S s) t

/-- The actual character image sheaf becomes the constant rank-one
module sheaf on its finite étale Artin--Schreier cover. -/
def artinSchreierCharacterLocalTrivialization (hpE : (p : E) ≠ 0) :
    (artinSchreierCharacterImageSheaf p f E ψ).over (artinSchreierEtaleObject p f) ≅
      (constantSheaf ((Spec (.of R)).smallEtaleTopology.over
        (artinSchreierEtaleObject p f)) (ModuleCat.{u} E)).obj (ModuleCat.of E E) := by
  letI := artinSchreierCharacterLocalTrivializationMap_isIso p f E ψ hpE
  exact (asIso (artinSchreierCharacterLocalTrivializationMap p f E ψ)).symm

/-- Local constancy is witnessed by the actual constant-sheaf isomorphism. -/
theorem artinSchreierCharacterImageSheaf_over_isConstant (hpE : (p : E) ≠ 0) :
    Sheaf.IsConstant
      ((Spec (.of R)).smallEtaleTopology.over (artinSchreierEtaleObject p f))
      ((artinSchreierCharacterImageSheaf p f E ψ).over (artinSchreierEtaleObject p f)) :=
  Sheaf.isConstant_of_iso _ (artinSchreierCharacterLocalTrivialization p f E ψ hpE)

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierCharacterLocalTrivializationMap
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterLocalTrivializationMap_stalk
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterLocalTrivializationMap_stalk_isIso
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterLocalTrivializationMap_isIso
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterLocalTrivialization
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheaf_over_isConstant
