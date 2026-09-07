import TypeIIIArtinSchreierTorsor
import TypeIIIArtinSchreierDeck
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Limits

/-!
# Étale-local triviality of the actual Artin--Schreier cover

The actual self-pullback of the finite étale cover is isomorphic to the
disjoint union of `p` copies of the cover. On component `a`, the two
projections are the identity and the actual deck translation by `a`.
Thus the algebraic torsor identity is realized as a scheme isomorphism
over the cover, with its structure maps explicitly identified.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] (f : R)

omit [CharP R p] in
/-- The finite disjoint union of affine copies is the spectrum of their
product ring, retaining the small prime-field index in any universe. -/
theorem artinSchreierScheme_sigmaSpec_isIso :
    IsIso (sigmaSpec (fun _ : ZMod p => CommRingCat.of (ArtinSchreierCover p R f))) := by
  let F := fun _ : ZMod p => Spec (CommRingCat.of (ArtinSchreierCover p R f))
  let e : ULift.{u} (ZMod p) ≃ ZMod p := Equiv.ulift
  let er := RingEquiv.piCongrLeft' (fun _ : ZMod p => ArtinSchreierCover p R f) e.symm
  let I := Scheme.Spec.mapIso er.toCommRingCatIso.op
  have hs : sigmaSpec (fun _ : ZMod p => CommRingCat.of (ArtinSchreierCover p R f)) =
      (Sigma.reindex e F).inv ≫
        sigmaSpec (fun _ : ULift.{u} (ZMod p) => CommRingCat.of (ArtinSchreierCover p R f)) ≫
          I.hom := by
    apply Sigma.hom_ext
    intro a
    have hi : Sigma.ι (fun _ : ZMod p => Spec (CommRingCat.of (ArtinSchreierCover p R f))) a ≫
        (Sigma.reindex e F).inv =
        Sigma.ι (fun _ : ULift.{u} (ZMod p) => Spec (CommRingCat.of (ArtinSchreierCover p R f)))
          (ULift.up a) :=
      Sigma.ι_reindex_inv e F (ULift.up a)
    rw [← Category.assoc, ← Category.assoc, hi, ι_sigmaSpec, ι_sigmaSpec]
    change Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : ZMod p => ArtinSchreierCover p R f) a)) =
      Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : ULift.{u} (ZMod p) => ArtinSchreierCover p R f) (ULift.up a))) ≫
        Spec.map (CommRingCat.ofHom er.toRingHom)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [hs]
  infer_instance

/-- The self-pullback is the actual disjoint union indexed by the prime field. -/
def artinSchreierSchemeTorsorIso :
    (∐ fun _ : ZMod p => artinSchreierScheme p R f) ≅
      pullback (artinSchreierSchemeMap p f) (artinSchreierSchemeMap p f) := by
  change (∐ fun _ : ZMod p => Spec (CommRingCat.of (ArtinSchreierCover p R f))) ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f))))
  letI : IsIso (sigmaSpec (fun _ : ZMod p => CommRingCat.of (ArtinSchreierCover p R f))) :=
    artinSchreierScheme_sigmaSpec_isIso p f
  exact asIso (sigmaSpec (fun _ : ZMod p => CommRingCat.of (ArtinSchreierCover p R f))) ≪≫
    Scheme.Spec.mapIso
      (artinSchreierCover_torsorEquiv p f).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R (ArtinSchreierCover p R f) (ArtinSchreierCover p R f)).symm

/-- A component of the scheme isomorphism is the spectrum of the
corresponding component of the actual tensor-product torsor map. -/
theorem artinSchreierSchemeTorsorIso_component (a : ZMod p) :
    Sigma.ι (fun _ : ZMod p => artinSchreierScheme p R f) a ≫
        (artinSchreierSchemeTorsorIso p f).hom =
      Spec.map (CommRingCat.ofHom
        (artinSchreierCover_torsorComponent p f a).toRingHom) ≫
        (pullbackSpecIso R (ArtinSchreierCover p R f) (ArtinSchreierCover p R f)).inv := by
  change Sigma.ι _ a ≫
      (sigmaSpec (fun _ : ZMod p => CommRingCat.of (ArtinSchreierCover p R f)) ≫
        (Spec.map (CommRingCat.ofHom (artinSchreierCover_torsorEquiv p f).toRingHom) ≫
          (pullbackSpecIso R (ArtinSchreierCover p R f) (ArtinSchreierCover p R f)).inv)) = _
  rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hc := congrArg AlgHom.toRingHom (artinSchreierCover_torsorEquiv_component p f a)
  exact congrArg
    (fun g => Spec.map (CommRingCat.ofHom g) ≫
      (pullbackSpecIso R (ArtinSchreierCover p R f) (ArtinSchreierCover p R f)).inv) hc

set_option backward.isDefEq.respectTransparency.types false in
/-- Over each component, the first projection is the identity. -/
theorem artinSchreierSchemeTorsorIso_fst (a : ZMod p) :
    Sigma.ι (fun _ : ZMod p => artinSchreierScheme p R f) a ≫
        (artinSchreierSchemeTorsorIso p f).hom ≫
        pullback.fst (artinSchreierSchemeMap p f) (artinSchreierSchemeMap p f) =
      𝟙 (artinSchreierScheme p R f) := by
  rw [← Category.assoc, artinSchreierSchemeTorsorIso_component]
  change (Spec.map (CommRingCat.ofHom
      (artinSchreierCover_torsorComponent p f a).toRingHom) ≫
      (pullbackSpecIso R (ArtinSchreierCover p R f) (ArtinSchreierCover p R f)).inv) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f)))) =
      𝟙 (Spec (CommRingCat.of (ArtinSchreierCover p R f)))
  rw [Category.assoc,
    pullbackSpecIso_inv_fst', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hc : (artinSchreierCover_torsorComponent p f a).toRingHom.comp
      (algebraMap (ArtinSchreierCover p R f)
        (ArtinSchreierCover p R f ⊗[R] ArtinSchreierCover p R f)) =
      RingHom.id (ArtinSchreierCover p R f) := by
    apply RingHom.ext
    intro x
    exact (artinSchreierCover_torsorComponent p f a).commutes x
  rw [hc]
  exact Spec.map_id _

set_option backward.isDefEq.respectTransparency.types false in
/-- Over component `a`, the second projection is the actual deck map. -/
theorem artinSchreierSchemeTorsorIso_snd (a : ZMod p) :
    Sigma.ι (fun _ : ZMod p => artinSchreierScheme p R f) a ≫
        (artinSchreierSchemeTorsorIso p f).hom ≫
        pullback.snd (artinSchreierSchemeMap p f) (artinSchreierSchemeMap p f) =
      (artinSchreierEtaleDeck p f a).left := by
  rw [← Category.assoc, artinSchreierSchemeTorsorIso_component]
  change (Spec.map (CommRingCat.ofHom
      (artinSchreierCover_torsorComponent p f a).toRingHom) ≫
      (pullbackSpecIso R (ArtinSchreierCover p R f) (ArtinSchreierCover p R f)).inv) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f)))) =
      (artinSchreierEtaleDeck p f a).left
  rw [Category.assoc,
    pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hc : (artinSchreierCover_torsorComponent p f a).toRingHom.comp
      (Algebra.TensorProduct.includeRight : ArtinSchreierCover p R f →ₐ[R]
        ArtinSchreierCover p R f ⊗[R] ArtinSchreierCover p R f).toRingHom =
      (artinSchreierCover_translationHom p f a).toRingHom := by
    apply RingHom.ext
    intro x
    change 1 * artinSchreierCover_translationHom p f a x = _
    exact one_mul _
  change Spec.map (CommRingCat.ofHom
      ((artinSchreierCover_torsorComponent p f a).toRingHom.comp
        (Algebra.TensorProduct.includeRight : ArtinSchreierCover p R f →ₐ[R]
          ArtinSchreierCover p R f ⊗[R] ArtinSchreierCover p R f).toRingHom)) =
      Spec.map (CommRingCat.ofHom (artinSchreierCover_translationHom p f a).toRingHom)
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) hc

#print axioms artinSchreierScheme_sigmaSpec_isIso
#print axioms artinSchreierSchemeTorsorIso
#print axioms artinSchreierSchemeTorsorIso_component
#print axioms artinSchreierSchemeTorsorIso_fst
#print axioms artinSchreierSchemeTorsorIso_snd

end PrimeGap182.TypeIII
