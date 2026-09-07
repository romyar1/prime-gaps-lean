import TypeIIIArtinSchreierPointGenerator
import TypeIIIArtinSchreierPointStalk
import TypeIIIArtinSchreierSheafProjection

/-!
# The identity section generates the actual character stalk

Apply the canonical image factorization to the free identity section
on the Artin--Schreier cover.  Its germ, followed by the actual image
inclusion and the ambient stalk comparison, is the character average
of the corresponding free basis vector.  The established nonzero
self-evaluation makes this character-section germ nonzero when p is
nonzero in the coefficient field.

The actual character stalk has proved dimension one.  Therefore the
map sending a scalar to the germ of its multiple of this section is
an isomorphism.  The section and the stalk map are defined before any
nonvanishing or rank argument, and the base stays Spec R.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

section CharacterSection

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R) (E : Type u) [Field E] (ψ : AddChar (ZMod p) E)

/-- The actual character section obtained from the canonical image
factorization applied to the free identity section. -/
def artinSchreierCharacterIdentitySection :
    (artinSchreierCharacterImageSheaf p f E ψ).obj.obj
      (op (artinSchreierEtaleObject p f)) :=
  (artinSchreierCharacterSheafRetraction p f E ψ).hom.app
    (op (artinSchreierEtaleObject p f)) (artinSchreierFreeSheafIdentitySection p f E)

/-- Scalar multiples of the actual character identity section. -/
def artinSchreierCharacterIdentitySectionMap :
    ModuleCat.of E E ⟶ (artinSchreierCharacterImageSheaf p f E ψ).obj.obj
      (op (artinSchreierEtaleObject p f)) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton E _
    (artinSchreierCharacterIdentitySection p f E ψ))

@[simp] theorem artinSchreierCharacterIdentitySectionMap_apply (a : E) :
    artinSchreierCharacterIdentitySectionMap p f E ψ a =
      a • artinSchreierCharacterIdentitySection p f E ψ := rfl

/-- Including the character section into the ambient sheaf gives the
actual average of the free identity section. -/
theorem artinSchreierCharacterIdentitySection_inclusion :
    (Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ)).hom.app
        (op (artinSchreierEtaleObject p f))
        (artinSchreierCharacterIdentitySection p f E ψ) =
      (artinSchreierCharacterSheafAverage p f E ψ).hom.app
        (op (artinSchreierEtaleObject p f)) (artinSchreierFreeSheafIdentitySection p f E) := by
  exact congrArg
    (fun g => g.hom.app (op (artinSchreierEtaleObject p f))
      (artinSchreierFreeSheafIdentitySection p f E))
    (artinSchreierCharacterSheafRetraction_comp_inclusion p f E ψ)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual character-section germ, included into the ambient stalk,
is the average of the basis vector at the lifted site point. -/
theorem artinSchreierCharacterIdentitySection_germ_inclusion
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology)
    (t : Φ.fiber.obj (artinSchreierEtaleObject p f)) :
    (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        ((Φ.sheafFiber.map
          (Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ)))
          (Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
            (artinSchreierCharacterImageSheaf p f E ψ).obj
              (artinSchreierCharacterIdentitySection p f E ψ))) =
      artinSchreierCharacterFreeFiberAverage p f E ψ Φ (ModuleCat.freeMk t) := by
  let Y := artinSchreierEtaleObject p f
  let F := artinSchreierFreeSheaf p f E
  let L := artinSchreierCharacterImageSheaf p f E ψ
  let P := artinSchreierCharacterSheafAverage p f E ψ
  let i := Abelian.image.ι P
  let s₀ := artinSchreierFreeSheafIdentitySection p f E
  let s := artinSchreierCharacterIdentitySection p f E ψ
  let e := artinSchreierFreeSheaf_stalkIso p f E Φ
  have hi := Φ.toPresheafFiber_naturality_apply i.hom Y t s
  have hP := Φ.toPresheafFiber_naturality_apply P.hom Y t s₀
  have hA := congrArg (fun g => g (Φ.toPresheafFiber Y t F.obj s₀))
    (artinSchreierCharacterSheafAverage_stalk p f E ψ Φ)
  calc
    _ = e.hom (Φ.toPresheafFiber Y t F.obj (i.hom.app (op Y) s)) :=
      congrArg (fun v => e.hom v) hi
    _ = e.hom (Φ.toPresheafFiber Y t F.obj (P.hom.app (op Y) s₀)) :=
      congrArg (fun v => e.hom (Φ.toPresheafFiber Y t F.obj v))
        (artinSchreierCharacterIdentitySection_inclusion p f E ψ)
    _ = e.hom ((Φ.sheafFiber.map P) (Φ.toPresheafFiber Y t F.obj s₀)) :=
      congrArg (fun v => e.hom v) hP.symm
    _ = artinSchreierCharacterFreeFiberAverage p f E ψ Φ
        (e.hom (Φ.toPresheafFiber Y t F.obj s₀)) := hA
    _ = _ := congrArg (fun v => artinSchreierCharacterFreeFiberAverage p f E ψ Φ v)
      (artinSchreierFreeSheaf_stalkIso_identityGerm p f E Φ t)

end CharacterSection

section GeometricGenerator

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra (ZMod p) Ω] (f : R) (E : Type u) [Field E] (ψ : AddChar (ZMod p) E)

include K in
/-- The actual character-section germ is nonzero at every such lifted
geometric point when p is nonzero in the coefficient field. -/
theorem artinSchreierCharacterIdentitySection_germ_ne_zero (hpE : (p : E) ≠ 0)
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).toPresheafFiber
        (artinSchreierEtaleObject p f) t (artinSchreierCharacterImageSheaf p f E ψ).obj
          (artinSchreierCharacterIdentitySection p f E ψ) ≠ 0 := by
  intro h
  have hg := artinSchreierCharacterIdentitySection_germ_inclusion p f E ψ
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) t
  rw [h] at hg
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let i := Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ)
  let e := artinSchreierFreeSheaf_stalkIso p f E Φ
  have hz : e.hom ((Φ.sheafFiber.map i) 0) = 0 :=
    (congrArg (fun v => e.hom v) ((Φ.sheafFiber.map i).hom.map_zero)).trans
      e.hom.hom.map_zero
  exact artinSchreierPointFreeAverage_freeMk_ne_zero p R K Ω f E ψ hpE t
    (hg.symm.trans hz)

include K in
set_option backward.isDefEq.respectTransparency.types false in
/-- The section gives an actual isomorphism from E to the original
image-sheaf stalk.  Nonvanishing and dimension one are proved inputs. -/
theorem artinSchreierCharacterIdentitySectionMap_stalk_isIso (hpE : (p : E) ≠ 0)
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    IsIso (artinSchreierCharacterIdentitySectionMap p f E ψ ≫
      (Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).toPresheafFiber
          (artinSchreierEtaleObject p f) t (artinSchreierCharacterImageSheaf p f E ψ).obj) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let Y := artinSchreierEtaleObject p f
  let L := artinSchreierCharacterImageSheaf p f E ψ
  let s := artinSchreierCharacterIdentitySection p f E ψ
  have hs : Φ.toPresheafFiber Y t L.obj s ≠ 0 :=
    artinSchreierCharacterIdentitySection_germ_ne_zero p R K Ω f E ψ hpE t
  have hd : Module.finrank E ((Φ.presheafFiber (A := ModuleCat.{u} E)).obj L.obj) = 1 :=
    artinSchreierPointCharacterStalk_finrank p R K Ω f E ψ hpE
  let g := (artinSchreierCharacterIdentitySectionMap p f E ψ ≫
    Φ.toPresheafFiber Y t L.obj).hom
  have hg (a : E) : g a = a • Φ.toPresheafFiber Y t L.obj s :=
    (Φ.toPresheafFiber Y t L.obj).hom.map_smul a s
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective g
  constructor
  · intro a b hab
    exact smul_left_injective E hs ((hg a).symm.trans (hab.trans (hg b)))
  · intro v
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hs v
    exact ⟨c, (hg c).trans hc⟩

end GeometricGenerator

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierCharacterIdentitySection
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterIdentitySectionMap
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterIdentitySectionMap_apply
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterIdentitySection_inclusion
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterIdentitySection_germ_inclusion
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterIdentitySection_germ_ne_zero
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterIdentitySectionMap_stalk_isIso
