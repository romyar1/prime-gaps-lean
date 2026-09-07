import TypeIIIArtinSchreierPointStalk
import TypeIIIArtinSchreierRingProjection
import TypeIIIArtinSchreierRingSheaf

/-!
# Actual character-image stalks over commutative coefficient rings

The p-unit character image sheaf remains on the original affine base
Spec R.  At a compatible point R → K → Ω with Ω algebraically closed,
its actual stalk is identified with the existing character module of
functions on the roots of z^p-z=f(K).  This follows from the actual free
stalk comparison, the negative deck action on functions, and preservation
of images by the stalk functor.

Evaluation at an actual root gives a linear equivalence with the
coefficient ring.  Existence of roots over Ω discharges the root choice
for freeness, finite generation, and rank one.  No freeness, comparison,
or local constancy premise is supplied.  The coefficient ring need only
be commutative with p invertible; it need not be a field or a domain.
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
  (E : Type u) [CommRing E] [Invertible (p : E)] (ψ : AddChar (ZMod p) E)

/-- The actual positive-weight deck average on the original site's
free fiber becomes the negative-weight projector on root functions. -/
theorem artinSchreierRingPointFreeEquivFunctions_average
    (v : (ModuleCat.free E).obj (ArtinSchreierPointSiteFiber p R Ω f)) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        (artinSchreierRingCharacterFreeFiberAverage p f E ψ
          (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) v) =
      artinSchreierRingCharacterProjection p K Ω (algebraMap R K f) E ψ
        (artinSchreierPointFreeEquivFunctions p R K Ω f E v) := by
  funext z
  change artinSchreierPointFreeEquivFunctions p R K Ω f E
      ((artinSchreierRingCharacterFreeFiberAverage p f E ψ
        (Scheme.pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))).hom v) z = _
  simp only [artinSchreierRingCharacterFreeFiberAverage, ModuleCat.hom_smul,
    ModuleCat.hom_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
    artinSchreierPointFreeEquivFunctions_deck_apply,
    artinSchreierRingCharacterProjection_apply, smul_eq_mul]
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
  intro a
  simp only [Equiv.neg_apply, neg_neg]

/-- The ambient stalk endomorphism induced by the actual ring average. -/
def artinSchreierRingPointAmbientStalkAverage :
    ArtinSchreierPointAmbientStalk p R Ω f E →ₗ[E]
      ArtinSchreierPointAmbientStalk p R Ω f E :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).sheafFiber.map
      (artinSchreierRingCharacterSheafAverage p f E ψ)).hom

/-- The shared ambient stalk equivalence intertwines the actual sheaf
average and the ring-coefficient root projector. -/
theorem artinSchreierRingPointAmbientStalkEquivFunctions_average
    (v : ArtinSchreierPointAmbientStalk p R Ω f E) :
    artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E
        (artinSchreierRingPointAmbientStalkAverage p R Ω f E ψ v) =
      artinSchreierRingCharacterProjection p K Ω (algebraMap R K f) E ψ
        (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E v) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  have h := congrArg (fun g => g v)
    (artinSchreierRingCharacterSheafAverage_stalk p f E ψ Φ)
  change artinSchreierPointFreeEquivFunctions p R K Ω f E
      ((artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        (artinSchreierRingPointAmbientStalkAverage p R Ω f E ψ v)) = _
  change (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
      (artinSchreierRingPointAmbientStalkAverage p R Ω f E ψ v) = _ at h
  rw [h]
  exact artinSchreierRingPointFreeEquivFunctions_average p R K Ω f E ψ _

/-- The literal range of the actual stalk average is identified with
the existing character module through the shared ambient equivalence. -/
def artinSchreierRingPointAmbientRangeEquivCharacter :
    LinearMap.range (artinSchreierRingPointAmbientStalkAverage p R Ω f E ψ) ≃ₗ[E]
      artinSchreierCharacterSpace p K Ω (algebraMap R K f) E ψ where
  toFun v := ⟨artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E v.val, by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw, artinSchreierRingPointAmbientStalkEquivFunctions_average]
    exact artinSchreierRingCharacterProjection_mem p K Ω (algebraMap R K f) E ψ _⟩
  invFun v := ⟨(artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).symm v.val, by
    refine ⟨(artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).symm v.val, ?_⟩
    apply (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E).injective
    rw [artinSchreierRingPointAmbientStalkEquivFunctions_average,
      LinearEquiv.apply_symm_apply,
      artinSchreierRingCharacterProjection_eq_self p K Ω (algebraMap R K f) E ψ
        v.val v.property]⟩
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

/-- The actual image-sheaf stalk on Spec R, with the p-unit coefficients. -/
abbrev ArtinSchreierRingPointCharacterStalk : ModuleCat.{u} E :=
  (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).sheafFiber.obj
      (artinSchreierRingCharacterImageSheaf p f E ψ)

/-- Preservation of actual images gives the character-space comparison
without an assumed rank or identification of the image stalk. -/
def artinSchreierRingPointCharacterStalkEquiv :
    ArtinSchreierRingPointCharacterStalk p R Ω f E ψ ≃ₗ[E]
      artinSchreierCharacterSpace p K Ω (algebraMap R K f) E ψ := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let S := Φ.sheafFiber.map (artinSchreierRingCharacterSheafAverage p f E ψ)
  exact ((artinSchreierRingCharacterImageSheaf_stalkImageIso p f E ψ Φ) ≪≫
    Abelian.imageIsoImage S ≪≫ ModuleCat.imageIsoRange S).toLinearEquiv.trans
      (artinSchreierRingPointAmbientRangeEquivCharacter p R K Ω f E ψ)

/-- The actual stalk map induced by the ring image-sheaf inclusion. -/
def artinSchreierRingPointCharacterStalkInclusion :
    ArtinSchreierRingPointCharacterStalk p R Ω f E ψ →ₗ[E]
      ArtinSchreierPointAmbientStalk p R Ω f E :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).sheafFiber.map
      (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ))).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The constructed comparison respects inclusion into the actual
ambient stalk of the original free sheaf on Spec R. -/
theorem artinSchreierRingPointCharacterStalkEquiv_val
    (v : ArtinSchreierRingPointCharacterStalk p R Ω f E ψ) :
    (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ v).val =
      artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E
        (artinSchreierRingPointCharacterStalkInclusion p R Ω f E ψ v) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let S := Φ.sheafFiber.map (artinSchreierRingCharacterSheafAverage p f E ψ)
  have h :
      ((artinSchreierRingCharacterImageSheaf_stalkImageIso p f E ψ Φ) ≪≫
        Abelian.imageIsoImage S ≪≫ ModuleCat.imageIsoRange S).hom ≫
          ModuleCat.ofHom (LinearMap.range S.hom).subtype =
        Φ.sheafFiber.map
          (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)) := by
    simp only [Iso.trans_hom, Category.assoc,
      ModuleCat.imageIsoRange_hom_subtype,
      Abelian.imageIsoImage_hom_comp_image_ι,
      artinSchreierRingCharacterImageSheaf_stalkImageIso]
    exact Abelian.PreservesImage.iso_hom_ι Φ.sheafFiber
      (artinSchreierRingCharacterSheafAverage p f E ψ)
  exact congrArg (artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E)
    (congrArg (fun g => g v) h)

/-- Root evaluation is an explicit linear equivalence from the actual
image-sheaf stalk to the coefficient ring. -/
def artinSchreierRingPointCharacterStalkEvaluationEquiv
    (z₀ : ArtinSchreierFiber p K Ω (algebraMap R K f)) :
    ArtinSchreierRingPointCharacterStalk p R Ω f E ψ ≃ₗ[E] E :=
  (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ).trans
    (artinSchreierCharacterEvaluationEquiv p K Ω (algebraMap R K f) E ψ z₀)

/-- The evaluation equivalence reads the actual included stalk element
in its root coordinate, which is useful for proving a section is a generator. -/
theorem artinSchreierRingPointCharacterStalkEvaluationEquiv_apply
    (z₀ : ArtinSchreierFiber p K Ω (algebraMap R K f))
    (v : ArtinSchreierRingPointCharacterStalk p R Ω f E ψ) :
    artinSchreierRingPointCharacterStalkEvaluationEquiv p R K Ω f E ψ z₀ v =
      artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E
        (artinSchreierRingPointCharacterStalkInclusion p R Ω f E ψ v) z₀ := by
  change (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ v).val z₀ = _
  rw [artinSchreierRingPointCharacterStalkEquiv_val]

include K in
/-- Existence of a root over Ω proves freeness of the actual stalk. -/
theorem artinSchreierRingPointCharacterStalk_free :
    Module.Free E (ArtinSchreierRingPointCharacterStalk p R Ω f E ψ) :=
  Module.Free.of_equiv
    (artinSchreierRingPointCharacterStalkEvaluationEquiv p R K Ω f E ψ
      (artinSchreierGeometricRoot p K Ω (algebraMap R K f))).symm

include K in
/-- Finite generation is transferred from E along the constructed
stalk equivalence, with its root supplied by algebraic closedness. -/
theorem artinSchreierRingPointCharacterStalk_finite :
    Module.Finite E (ArtinSchreierRingPointCharacterStalk p R Ω f E ψ) :=
  Module.Finite.equiv
    (artinSchreierRingPointCharacterStalkEvaluationEquiv p R K Ω f E ψ
      (artinSchreierGeometricRoot p K Ω (algebraMap R K f))).symm

include K in
/-- The rank-one conclusion for the original image-sheaf stalk follows
from its explicit equivalence with the coefficient ring. -/
theorem artinSchreierRingPointCharacterStalk_finrank :
    Module.finrank E (ArtinSchreierRingPointCharacterStalk p R Ω f E ψ) = 1 := by
  rw [(artinSchreierRingPointCharacterStalkEvaluationEquiv p R K Ω f E ψ
    (artinSchreierGeometricRoot p K Ω (algebraMap R K f))).finrank_eq]
  exact CommSemiring.finrank_self E

#print axioms artinSchreierRingPointFreeEquivFunctions_average
#print axioms artinSchreierRingPointAmbientStalkAverage
#print axioms artinSchreierRingPointAmbientStalkEquivFunctions_average
#print axioms artinSchreierRingPointAmbientRangeEquivCharacter
#print axioms ArtinSchreierRingPointCharacterStalk
#print axioms artinSchreierRingPointCharacterStalkEquiv
#print axioms artinSchreierRingPointCharacterStalkInclusion
#print axioms artinSchreierRingPointCharacterStalkEquiv_val
#print axioms artinSchreierRingPointCharacterStalkEvaluationEquiv
#print axioms artinSchreierRingPointCharacterStalkEvaluationEquiv_apply
#print axioms artinSchreierRingPointCharacterStalk_free
#print axioms artinSchreierRingPointCharacterStalk_finite
#print axioms artinSchreierRingPointCharacterStalk_finrank

end PrimeGap182.TypeIII
