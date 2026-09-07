import TypeIIIArtinSchreierBaseChange
import TypeIIIArtinSchreierScheme
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Scheme base change for the actual Artin--Schreier cover

The categorical pullback of the constructed affine cover is the spectrum
of its tensor product algebra. The proved quotient base-change equivalence
identifies this with the Artin--Schreier cover over the new base ring. The
identification respects the structure map to that base.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

variable (p : ℕ) {R : Type u} [CommRing R]
  (S : Type u) [CommRing S] [Algebra R S] (f : R)

/-- Base change of the actual scheme cover is the same polynomial cover
over the new coefficient ring. -/
def artinSchreierSchemeBaseChangeIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (artinSchreierSchemeMap p f) ≅
      artinSchreierScheme p S (algebraMap R S f) :=
  (pullbackSpecIso R S (ArtinSchreierCover p R f)) ≪≫
    Scheme.Spec.mapIso
      (artinSchreierCover_baseChangeEquiv p S f).symm.toRingEquiv.toCommRingCatIso.op

/-- The base-change isomorphism preserves the projection to the new base. -/
theorem artinSchreierSchemeBaseChangeIso_over :
    (artinSchreierSchemeBaseChangeIso p S f).hom ≫
        artinSchreierSchemeMap p (algebraMap R S f) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (artinSchreierSchemeMap p f) := by
  change ((pullbackSpecIso R S (ArtinSchreierCover p R f)).hom ≫
      Spec.map (CommRingCat.ofHom
        (artinSchreierCover_baseChangeEquiv p S f).symm.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap S (ArtinSchreierCover p S (algebraMap R S f)))) = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hc : (artinSchreierCover_baseChangeEquiv p S f).symm.toRingHom.comp
      (algebraMap S (ArtinSchreierCover p S (algebraMap R S f))) =
      algebraMap S (S ⊗[R] ArtinSchreierCover p R f) := by
    ext s
    exact (artinSchreierCover_baseChangeEquiv p S f).symm.commutes s
  rw [hc]
  exact pullbackSpecIso_hom_fst' R S (ArtinSchreierCover p R f)

#print axioms artinSchreierSchemeBaseChangeIso
#print axioms artinSchreierSchemeBaseChangeIso_over

end PrimeGap182.TypeIII
