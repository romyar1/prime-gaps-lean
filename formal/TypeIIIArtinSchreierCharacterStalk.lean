import TypeIIIArtinSchreierSheaf
import TypeIIIArtinSchreierStalkFunctions
import TypeIIIArtinSchreierProjection
import Mathlib.Algebra.Category.ModuleCat.Images

/-!
# The rank-one stalk of the actual Artin--Schreier character image sheaf

The ambient stalk is identified with functions on the actual polynomial
root fiber.  The sheaf's positive-weight deck average becomes the
explicit negative-weight function projector.  When p is nonzero in E,
the stalk of the image sheaf is linearly equivalent to the actual
character submodule.  Algebraic closedness supplies a root and proves
rank one.

These are statements about an actual module-valued sheaf and its point
fiber.  No Frobenius operator or compact cohomology is defined here.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (K Ω : Type u) [Field K] [CharP K p]
  [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [Algebra K Ω]
  [Algebra (ZMod p) K] [Algebra (ZMod p) Ω] [IsScalarTower (ZMod p) K Ω]
  (f : K) (E : Type u) [Field E]

/-- The actual ambient stalk of the free module sheaf at the chosen
geometric point of the affine base. -/
abbrev ArtinSchreierAmbientStalk : ModuleCat.{u} E :=
  (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj
      (artinSchreierFreeSheaf p f E)

/-- The actual ambient stalk is the space of functions on the literal
root fiber, via the proved sheaf and cover comparisons. -/
def artinSchreierAmbientStalkEquivFunctions :
    ArtinSchreierAmbientStalk p K Ω f E ≃ₗ[E]
      (ArtinSchreierFiber p K Ω f → E) :=
  (artinSchreierFreeSheaf_stalkIso p f E
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))).toLinearEquiv.trans
    (artinSchreierSiteFreeEquivFunctions p K Ω f E)

/-- The positive-weight free-fiber average is exactly the explicit
function projector after the proved inverse deck action. -/
theorem artinSchreierSiteFreeEquivFunctions_average (ψ : AddChar (ZMod p) E)
    (v : (ModuleCat.free E).obj (ArtinSchreierSiteFiber p K Ω f)) :
    artinSchreierSiteFreeEquivFunctions p K Ω f E
        (artinSchreierCharacterFreeFiberAverage p f E ψ
          (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) v) =
      artinSchreierCharacterProjection p K Ω f E ψ
        (artinSchreierSiteFreeEquivFunctions p K Ω f E v) := by
  funext z
  change artinSchreierSiteFreeEquivFunctions p K Ω f E
      ((artinSchreierCharacterFreeFiberAverage p f E ψ
        (Scheme.pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))).hom v) z = _
  simp only [artinSchreierCharacterFreeFiberAverage, ModuleCat.hom_smul,
    ModuleCat.hom_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
    artinSchreierSiteFreeEquivFunctions_deck_apply,
    artinSchreierCharacterProjection_apply, smul_eq_mul]
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
  intro a
  simp only [Equiv.neg_apply, neg_neg]

/-- The actual stalk endomorphism induced by the sheaf average. -/
def artinSchreierAmbientStalkAverage (ψ : AddChar (ZMod p) E) :
    ArtinSchreierAmbientStalk p K Ω f E →ₗ[E]
      ArtinSchreierAmbientStalk p K Ω f E :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map
      (artinSchreierCharacterSheafAverage p f E ψ)).hom

/-- The actual ambient stalk average is the explicit root function
projector, with no rank, action, or comparison hypothesis. -/
theorem artinSchreierAmbientStalkEquivFunctions_average (ψ : AddChar (ZMod p) E)
    (v : ArtinSchreierAmbientStalk p K Ω f E) :
    artinSchreierAmbientStalkEquivFunctions p K Ω f E
        (artinSchreierAmbientStalkAverage p K Ω f E ψ v) =
      artinSchreierCharacterProjection p K Ω f E ψ
        (artinSchreierAmbientStalkEquivFunctions p K Ω f E v) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  have h := congrArg (fun g => g v)
    (artinSchreierCharacterSheafAverage_stalk p f E ψ Φ)
  change artinSchreierSiteFreeEquivFunctions p K Ω f E
      ((artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        (artinSchreierAmbientStalkAverage p K Ω f E ψ v)) = _
  change (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
      (artinSchreierAmbientStalkAverage p K Ω f E ψ v) = _ at h
  rw [h]
  exact artinSchreierSiteFreeEquivFunctions_average p K Ω f E ψ _

/-- The range of the actual stalk average is exactly the character
space under the explicit ambient equivalence. -/
def artinSchreierAmbientRangeEquivCharacter (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    LinearMap.range (artinSchreierAmbientStalkAverage p K Ω f E ψ) ≃ₗ[E]
      artinSchreierCharacterSpace p K Ω f E ψ where
  toFun v := ⟨artinSchreierAmbientStalkEquivFunctions p K Ω f E v.val, by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw, artinSchreierAmbientStalkEquivFunctions_average]
    exact artinSchreierCharacterProjection_mem p K Ω f E ψ _⟩
  invFun v := ⟨(artinSchreierAmbientStalkEquivFunctions p K Ω f E).symm v.val, by
    refine ⟨(artinSchreierAmbientStalkEquivFunctions p K Ω f E).symm v.val, ?_⟩
    apply (artinSchreierAmbientStalkEquivFunctions p K Ω f E).injective
    rw [artinSchreierAmbientStalkEquivFunctions_average, LinearEquiv.apply_symm_apply,
      artinSchreierCharacterProjection_eq_self p K Ω f E ψ hpE v.val v.property]⟩
  left_inv v := by
    apply Subtype.ext
    exact (artinSchreierAmbientStalkEquivFunctions p K Ω f E).symm_apply_apply v.val
  right_inv v := by
    apply Subtype.ext
    exact (artinSchreierAmbientStalkEquivFunctions p K Ω f E).apply_symm_apply v.val
  map_add' v w := by
    apply Subtype.ext
    exact (artinSchreierAmbientStalkEquivFunctions p K Ω f E).map_add v.val w.val
  map_smul' c v := by
    apply Subtype.ext
    exact (artinSchreierAmbientStalkEquivFunctions p K Ω f E).map_smul c v.val

/-- The actual stalk of the image sheaf at the geometric base point. -/
abbrev ArtinSchreierCharacterStalk (ψ : AddChar (ZMod p) E) : ModuleCat.{u} E :=
  (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj
      (artinSchreierCharacterImageSheaf p f E ψ)

/-- The actual sheaf stalk is the character submodule on the actual
polynomial-root fiber.  Image preservation and the linear range
comparison are the proved categorical isomorphisms. -/
def artinSchreierCharacterStalkEquiv (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    ArtinSchreierCharacterStalk p K Ω f E ψ ≃ₗ[E]
      artinSchreierCharacterSpace p K Ω f E ψ := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let S := Φ.sheafFiber.map (artinSchreierCharacterSheafAverage p f E ψ)
  exact ((artinSchreierCharacterImageSheaf_stalkImageIso p f E ψ Φ) ≪≫
    Abelian.imageIsoImage S ≪≫ ModuleCat.imageIsoRange S).toLinearEquiv.trans
      (artinSchreierAmbientRangeEquivCharacter p K Ω f E ψ hpE)

/-- The stalk map induced by the actual sheaf-image inclusion. -/
def artinSchreierCharacterStalkInclusion (ψ : AddChar (ZMod p) E) :
    ArtinSchreierCharacterStalk p K Ω f E ψ →ₗ[E]
      ArtinSchreierAmbientStalk p K Ω f E :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map
      (Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ))).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The character-space equivalence agrees with the actual inclusion
into the ambient stalk.  This records the diagram needed to transport
actions that arise independently from the site point. -/
theorem artinSchreierCharacterStalkEquiv_val (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) (v : ArtinSchreierCharacterStalk p K Ω f E ψ) :
    (artinSchreierCharacterStalkEquiv p K Ω f E ψ hpE v).val =
      artinSchreierAmbientStalkEquivFunctions p K Ω f E
        (artinSchreierCharacterStalkInclusion p K Ω f E ψ v) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let S := Φ.sheafFiber.map (artinSchreierCharacterSheafAverage p f E ψ)
  have h :
      ((artinSchreierCharacterImageSheaf_stalkImageIso p f E ψ Φ) ≪≫
        Abelian.imageIsoImage S ≪≫ ModuleCat.imageIsoRange S).hom ≫
          ModuleCat.ofHom (LinearMap.range S.hom).subtype =
        Φ.sheafFiber.map
          (Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ)) := by
    simp only [Iso.trans_hom, Category.assoc,
      ModuleCat.imageIsoRange_hom_subtype,
      Abelian.imageIsoImage_hom_comp_image_ι,
      artinSchreierCharacterImageSheaf_stalkImageIso]
    exact Abelian.PreservesImage.iso_hom_ι Φ.sheafFiber
      (artinSchreierCharacterSheafAverage p f E ψ)
  exact congrArg (artinSchreierAmbientStalkEquivFunctions p K Ω f E)
    (congrArg (fun g => g v) h)

/-- Every such actual geometric stalk is one-dimensional.  A root is
obtained from algebraic closedness, rather than supplied as a premise. -/
theorem artinSchreierCharacterStalk_finrank (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    Module.finrank E (ArtinSchreierCharacterStalk p K Ω f E ψ) = 1 := by
  rw [(artinSchreierCharacterStalkEquiv p K Ω f E ψ hpE).finrank_eq]
  exact artinSchreierCharacterSpace_finrank p K Ω f E ψ
    (artinSchreierGeometricRoot p K Ω f)

/-- Finite dimensionality of the actual geometric stalk, with root
existence discharged. -/
theorem artinSchreierCharacterStalk_finiteDimensional (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    FiniteDimensional E (ArtinSchreierCharacterStalk p K Ω f E ψ) := by
  let := artinSchreierCharacterSpace_finiteDimensional p K Ω f E ψ
    (artinSchreierGeometricRoot p K Ω f)
  exact (artinSchreierCharacterStalkEquiv p K Ω f E ψ hpE).symm.finiteDimensional

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.ArtinSchreierAmbientStalk
#print axioms PrimeGap182.TypeIII.artinSchreierAmbientStalkEquivFunctions
#print axioms PrimeGap182.TypeIII.artinSchreierSiteFreeEquivFunctions_average
#print axioms PrimeGap182.TypeIII.artinSchreierAmbientStalkAverage
#print axioms PrimeGap182.TypeIII.artinSchreierAmbientStalkEquivFunctions_average
#print axioms PrimeGap182.TypeIII.artinSchreierAmbientRangeEquivCharacter
#print axioms PrimeGap182.TypeIII.ArtinSchreierCharacterStalk
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalkEquiv
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalkInclusion
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalkEquiv_val
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalk_finrank
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalk_finiteDimensional
