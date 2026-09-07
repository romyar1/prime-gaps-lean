import TypeIIIArtinSchreierPointFiber
import TypeIIIArtinSchreierSheaf
import TypeIIIArtinSchreierProjection
import Mathlib.Algebra.Category.ModuleCat.Images

/-!
# Character-image stalks at points of an arbitrary affine base

For a compatible tower R → K → Ω with Ω algebraically closed, the
actual stalk of the Artin--Schreier image sheaf on Spec R is the
character space on the roots of z^p-z=f(K).  The cover, image sheaf,
and stalk stay on the original base Spec R.  The map R → K may have
a nonzero kernel.

The actual positive-weight deck average becomes the explicit function
projector through the proved negative deck action.  When p is nonzero
in the coefficient field, the image-stalk comparison and its inclusion
diagram follow from preservation of images.  Root existence over Ω
then gives finite dimensionality and rank one, with no supplied root
or rank premise.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra (ZMod p) Ω] (f : R)

section RingAmbient

variable (E : Type u) [CommRing E]

/-- The actual ambient stalk at the geometric point of the original
affine base.  Its definition does not change the base to K. -/
abbrev ArtinSchreierPointAmbientStalk : ModuleCat.{u} E :=
  (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).sheafFiber.obj
      (artinSchreierFreeSheaf p f E)

/-- The actual ambient stalk is the function space on the specialized
root fiber, via the sheaf comparison and the original quotient cover. -/
def artinSchreierPointAmbientStalkEquivFunctions :
    ArtinSchreierPointAmbientStalk p R Ω f E ≃ₗ[E]
      (ArtinSchreierFiber p K Ω (algebraMap R K f) → E) :=
  (artinSchreierFreeSheaf_stalkIso p f E
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))).toLinearEquiv.trans
    (artinSchreierPointFreeEquivFunctions p R K Ω f E)

end RingAmbient

variable (E : Type u) [Field E]

/-- The original site's positive-weight free-fiber average becomes
the explicit negative-weight projector on the specialized roots. -/
theorem artinSchreierPointFreeEquivFunctions_average (ψ : AddChar (ZMod p) E)
    (v : (ModuleCat.free E).obj (ArtinSchreierPointSiteFiber p R Ω f)) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        (artinSchreierCharacterFreeFiberAverage p f E ψ
          (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) v) =
      artinSchreierCharacterProjection p K Ω (algebraMap R K f) E ψ
        (artinSchreierPointFreeEquivFunctions p R K Ω f E v) := by
  funext z
  change artinSchreierPointFreeEquivFunctions p R K Ω f E
      ((artinSchreierCharacterFreeFiberAverage p f E ψ
        (Scheme.pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))).hom v) z = _
  simp only [artinSchreierCharacterFreeFiberAverage, ModuleCat.hom_smul,
    ModuleCat.hom_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
    artinSchreierPointFreeEquivFunctions_deck_apply,
    artinSchreierCharacterProjection_apply, smul_eq_mul]
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
  intro a
  simp only [Equiv.neg_apply, neg_neg]

/-- The actual stalk endomorphism induced by the original sheaf average. -/
def artinSchreierPointAmbientStalkAverage (ψ : AddChar (ZMod p) E) :
    ArtinSchreierPointAmbientStalk p R Ω f E →ₗ[E]
      ArtinSchreierPointAmbientStalk p R Ω f E :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).sheafFiber.map
      (artinSchreierCharacterSheafAverage p f E ψ)).hom

/-- The actual ambient stalk average agrees with the explicit root
projector through the proved stalk equivalence. -/
theorem artinSchreierPointAmbientStalkEquivFunctions_average
    (ψ : AddChar (ZMod p) E) (v : ArtinSchreierPointAmbientStalk p R Ω f E) :
    artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E
        (artinSchreierPointAmbientStalkAverage p R Ω f E ψ v) =
      artinSchreierCharacterProjection p K Ω (algebraMap R K f) E ψ
        (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E v) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  have h := congrArg (fun g => g v)
    (artinSchreierCharacterSheafAverage_stalk p f E ψ Φ)
  change artinSchreierPointFreeEquivFunctions p R K Ω f E
      ((artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        (artinSchreierPointAmbientStalkAverage p R Ω f E ψ v)) = _
  change (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
      (artinSchreierPointAmbientStalkAverage p R Ω f E ψ v) = _ at h
  rw [h]
  exact artinSchreierPointFreeEquivFunctions_average p R K Ω f E ψ _

/-- Under the ambient equivalence, the range of the actual stalk
average is precisely the specialized character space. -/
def artinSchreierPointAmbientRangeEquivCharacter (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    LinearMap.range (artinSchreierPointAmbientStalkAverage p R Ω f E ψ) ≃ₗ[E]
      artinSchreierCharacterSpace p K Ω (algebraMap R K f) E ψ where
  toFun v := ⟨artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E v.val, by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw, artinSchreierPointAmbientStalkEquivFunctions_average]
    exact artinSchreierCharacterProjection_mem p K Ω (algebraMap R K f) E ψ _⟩
  invFun v := ⟨(artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).symm v.val, by
    refine ⟨(artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).symm v.val, ?_⟩
    apply (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).injective
    rw [artinSchreierPointAmbientStalkEquivFunctions_average,
      LinearEquiv.apply_symm_apply,
      artinSchreierCharacterProjection_eq_self p K Ω (algebraMap R K f) E ψ
        hpE v.val v.property]⟩
  left_inv v := by
    apply Subtype.ext
    exact (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).symm_apply_apply v.val
  right_inv v := by
    apply Subtype.ext
    exact (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).apply_symm_apply v.val
  map_add' v w := by
    apply Subtype.ext
    exact (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).map_add v.val w.val
  map_smul' c v := by
    apply Subtype.ext
    exact (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).map_smul c v.val

/-- The actual stalk of the original character image sheaf. -/
abbrev ArtinSchreierPointCharacterStalk (ψ : AddChar (ZMod p) E) : ModuleCat.{u} E :=
  (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).sheafFiber.obj
      (artinSchreierCharacterImageSheaf p f E ψ)

/-- Preservation of images identifies the actual image-sheaf stalk
with the character space on the specialized root fiber. -/
def artinSchreierPointCharacterStalkEquiv (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    ArtinSchreierPointCharacterStalk p R Ω f E ψ ≃ₗ[E]
      artinSchreierCharacterSpace p K Ω (algebraMap R K f) E ψ := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let S := Φ.sheafFiber.map (artinSchreierCharacterSheafAverage p f E ψ)
  exact ((artinSchreierCharacterImageSheaf_stalkImageIso p f E ψ Φ) ≪≫
    Abelian.imageIsoImage S ≪≫ ModuleCat.imageIsoRange S).toLinearEquiv.trans
      (artinSchreierPointAmbientRangeEquivCharacter p R K Ω f E ψ hpE)

/-- The stalk map induced by the actual image-sheaf inclusion. -/
def artinSchreierPointCharacterStalkInclusion (ψ : AddChar (ZMod p) E) :
    ArtinSchreierPointCharacterStalk p R Ω f E ψ →ₗ[E]
      ArtinSchreierPointAmbientStalk p R Ω f E :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).sheafFiber.map
      (Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ))).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The character-space equivalence respects the actual inclusion
into the ambient stalk on the original base. -/
theorem artinSchreierPointCharacterStalkEquiv_val (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) (v : ArtinSchreierPointCharacterStalk p R Ω f E ψ) :
    (artinSchreierPointCharacterStalkEquiv p R K Ω f E ψ hpE v).val =
      artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E
        (artinSchreierPointCharacterStalkInclusion p R Ω f E ψ v) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
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
  exact congrArg (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E)
    (congrArg (fun g => g v) h)

include K in
/-- Every such actual image-sheaf stalk has rank one when p is nonzero
in the coefficient field.  Algebraic closedness supplies the root. -/
theorem artinSchreierPointCharacterStalk_finrank (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    Module.finrank E (ArtinSchreierPointCharacterStalk p R Ω f E ψ) = 1 := by
  rw [(artinSchreierPointCharacterStalkEquiv p R K Ω f E ψ hpE).finrank_eq]
  exact artinSchreierCharacterSpace_finrank p K Ω (algebraMap R K f) E ψ
    (artinSchreierGeometricRoot p K Ω (algebraMap R K f))

include K in
/-- The actual image-sheaf stalk is finite-dimensional, with no
supplied finiteness or rank hypothesis. -/
theorem artinSchreierPointCharacterStalk_finiteDimensional (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) :
    FiniteDimensional E (ArtinSchreierPointCharacterStalk p R Ω f E ψ) := by
  let := artinSchreierCharacterSpace_finiteDimensional p K Ω (algebraMap R K f) E ψ
    (artinSchreierGeometricRoot p K Ω (algebraMap R K f))
  exact (artinSchreierPointCharacterStalkEquiv p R K Ω f E ψ hpE).symm.finiteDimensional

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.ArtinSchreierPointAmbientStalk
#print axioms PrimeGap182.TypeIII.artinSchreierPointAmbientStalkEquivFunctions
#print axioms PrimeGap182.TypeIII.artinSchreierPointFreeEquivFunctions_average
#print axioms PrimeGap182.TypeIII.artinSchreierPointAmbientStalkAverage
#print axioms PrimeGap182.TypeIII.artinSchreierPointAmbientStalkEquivFunctions_average
#print axioms PrimeGap182.TypeIII.artinSchreierPointAmbientRangeEquivCharacter
#print axioms PrimeGap182.TypeIII.ArtinSchreierPointCharacterStalk
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalkEquiv
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalkInclusion
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalkEquiv_val
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalk_finrank
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalk_finiteDimensional
