import TypeIIIArtinSchreierPointGenerator
import TypeIIIArtinSchreierRingStalk

/-!
# The actual character section with p-unit ring coefficients

The image factorization projects the existing identity section of the
free sheaf. At a lifted geometric point, root evaluation sends its germ
to the unit 1/p. The map from the coefficient ring to the actual stalk
therefore has an explicit inverse: evaluate and multiply by p.

This argument uses invertibility, not a vector-space dimension argument,
and works for commutative coefficient rings with zero divisors.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

section CharacterSection

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R) (E : Type u) [CommRing E] [Invertible (p : E)]
  (ψ : AddChar (ZMod p) E)

/-- Project the actual free identity section through the actual
ring-coefficient image factorization. -/
def artinSchreierRingCharacterIdentitySection :
    (artinSchreierRingCharacterImageSheaf p f E ψ).obj.obj
      (op (artinSchreierEtaleObject p f)) :=
  (artinSchreierRingCharacterSheafRetraction p f E ψ).hom.app
    (op (artinSchreierEtaleObject p f)) (artinSchreierFreeSheafIdentitySection p f E)

/-- Scalar multiples of this actual section. -/
def artinSchreierRingCharacterIdentitySectionMap :
    ModuleCat.of E E ⟶ (artinSchreierRingCharacterImageSheaf p f E ψ).obj.obj
      (op (artinSchreierEtaleObject p f)) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton E _
    (artinSchreierRingCharacterIdentitySection p f E ψ))

@[simp] theorem artinSchreierRingCharacterIdentitySectionMap_apply (a : E) :
    artinSchreierRingCharacterIdentitySectionMap p f E ψ a =
      a • artinSchreierRingCharacterIdentitySection p f E ψ := rfl

/-- The section's actual image inclusion is the original average
applied to the free identity section. -/
theorem artinSchreierRingCharacterIdentitySection_inclusion :
    (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)).hom.app
        (op (artinSchreierEtaleObject p f))
        (artinSchreierRingCharacterIdentitySection p f E ψ) =
      (artinSchreierRingCharacterSheafAverage p f E ψ).hom.app
        (op (artinSchreierEtaleObject p f)) (artinSchreierFreeSheafIdentitySection p f E) := by
  exact congrArg
    (fun g => g.hom.app (op (artinSchreierEtaleObject p f))
      (artinSchreierFreeSheafIdentitySection p f E))
    (artinSchreierRingCharacterSheafRetraction_comp_inclusion p f E ψ)

set_option backward.isDefEq.respectTransparency.types false in
/-- The section's germ, followed by the actual image inclusion and
stalk comparison, is the explicit average of the lifted basis vector. -/
theorem artinSchreierRingCharacterIdentitySection_germ_inclusion
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology)
    (t : Φ.fiber.obj (artinSchreierEtaleObject p f)) :
    (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        ((Φ.sheafFiber.map
          (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)))
          (Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
            (artinSchreierRingCharacterImageSheaf p f E ψ).obj
              (artinSchreierRingCharacterIdentitySection p f E ψ))) =
      artinSchreierRingCharacterFreeFiberAverage p f E ψ Φ (ModuleCat.freeMk t) := by
  let Y := artinSchreierEtaleObject p f
  let F := artinSchreierFreeSheaf p f E
  let L := artinSchreierRingCharacterImageSheaf p f E ψ
  let P := artinSchreierRingCharacterSheafAverage p f E ψ
  let i := Abelian.image.ι P
  let s₀ := artinSchreierFreeSheafIdentitySection p f E
  let s := artinSchreierRingCharacterIdentitySection p f E ψ
  let e := artinSchreierFreeSheaf_stalkIso p f E Φ
  have hi := Φ.toPresheafFiber_naturality_apply i.hom Y t s
  have hP := Φ.toPresheafFiber_naturality_apply P.hom Y t s₀
  have hA := congrArg (fun g => g (Φ.toPresheafFiber Y t F.obj s₀))
    (artinSchreierRingCharacterSheafAverage_stalk p f E ψ Φ)
  calc
    _ = e.hom (Φ.toPresheafFiber Y t F.obj (i.hom.app (op Y) s)) :=
      congrArg (fun v => e.hom v) hi
    _ = e.hom (Φ.toPresheafFiber Y t F.obj (P.hom.app (op Y) s₀)) :=
      congrArg (fun v => e.hom (Φ.toPresheafFiber Y t F.obj v))
        (artinSchreierRingCharacterIdentitySection_inclusion p f E ψ)
    _ = e.hom ((Φ.sheafFiber.map P) (Φ.toPresheafFiber Y t F.obj s₀)) :=
      congrArg (fun v => e.hom v) hP.symm
    _ = artinSchreierRingCharacterFreeFiberAverage p f E ψ Φ
        (e.hom (Φ.toPresheafFiber Y t F.obj s₀)) := hA
    _ = _ := congrArg (fun v => artinSchreierRingCharacterFreeFiberAverage p f E ψ Φ v)
      (artinSchreierFreeSheaf_stalkIso_identityGerm p f E Φ t)

end CharacterSection

section GeometricGenerator

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra (ZMod p) Ω] (f : R) (E : Type u) [CommRing E] [Invertible (p : E)]
  (ψ : AddChar (ZMod p) E)

/-- Evaluation of the actual projected free basis vector at its own
root is the inverse unit p⁻¹. -/
theorem artinSchreierRingPointFreeAverage_freeMk_self
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        (artinSchreierRingCharacterFreeFiberAverage p f E ψ
          (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) (ModuleCat.freeMk t))
        (artinSchreierPointSiteEquivRoots p R Ω f K t) = ⅟(p : E) := by
  rw [artinSchreierRingPointFreeEquivFunctions_average]
  have hδ : artinSchreierPointFreeEquivFunctions p R K Ω f E (ModuleCat.freeMk t) =
      fun z => if z = artinSchreierPointSiteEquivRoots p R Ω f K t then 1 else 0 := by
    funext z
    rw [artinSchreierPointFreeEquivFunctions_freeMk]
    simp only [eq_comm]
  rw [hδ]
  exact artinSchreierRingCharacterProjection_delta_self p K Ω (algebraMap R K f) E ψ _

/-- Through the actual character-stalk comparison, evaluation of the
section germ at the lifted root is exactly the inverse unit. -/
theorem artinSchreierRingCharacterIdentitySection_germ_evaluation
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ
      ((Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).toPresheafFiber
          (artinSchreierEtaleObject p f) t
          (artinSchreierRingCharacterImageSheaf p f E ψ).obj
            (artinSchreierRingCharacterIdentitySection p f E ψ))).val
      (artinSchreierPointSiteEquivRoots p R Ω f K t) = ⅟(p : E) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let v : ArtinSchreierRingPointCharacterStalk p R Ω f E ψ :=
    Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
      (artinSchreierRingCharacterImageSheaf p f E ψ).obj
        (artinSchreierRingCharacterIdentitySection p f E ψ)
  change (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ v).val
    (artinSchreierPointSiteEquivRoots p R Ω f K t) = _
  rw [artinSchreierRingPointCharacterStalkEquiv_val]
  change artinSchreierPointFreeEquivFunctions p R K Ω f E
      ((artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        ((Φ.sheafFiber.map
          (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)))
          (Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
            (artinSchreierRingCharacterImageSheaf p f E ψ).obj
              (artinSchreierRingCharacterIdentitySection p f E ψ))))
      (artinSchreierPointSiteEquivRoots p R Ω f K t) = _
  rw [artinSchreierRingCharacterIdentitySection_germ_inclusion]
  exact artinSchreierRingPointFreeAverage_freeMk_self p R K Ω f E ψ t

include K in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual section gives an isomorphism from E to the actual
image-sheaf stalk. Its inverse is evaluation at the lifted root followed
by multiplication by p. No field or nonvanishing argument is used. -/
theorem artinSchreierRingCharacterIdentitySectionMap_stalk_isIso
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    IsIso (artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
      (Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).toPresheafFiber
          (artinSchreierEtaleObject p f) t
          (artinSchreierRingCharacterImageSheaf p f E ψ).obj) := by
  let Φ := Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let Y := artinSchreierEtaleObject p f
  let L := artinSchreierRingCharacterImageSheaf p f E ψ
  let s := artinSchreierRingCharacterIdentitySection p f E ψ
  let z := artinSchreierPointSiteEquivRoots p R Ω f K t
  let e := (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ).trans
    (artinSchreierCharacterEvaluationEquiv p K Ω (algebraMap R K f) E ψ z)
  let g : E →ₗ[E] ArtinSchreierRingPointCharacterStalk p R Ω f E ψ :=
    (artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
    Φ.toPresheafFiber Y t L.obj).hom
  let w : ArtinSchreierRingPointCharacterStalk p R Ω f E ψ :=
    Φ.toPresheafFiber Y t L.obj s
  have hg (a : E) : g a = a • w :=
    (Φ.toPresheafFiber Y t L.obj).hom.map_smul a s
  have he : e w = ⅟(p : E) :=
    artinSchreierRingCharacterIdentitySection_germ_evaluation p R K Ω f E ψ t
  have hge (a : E) : e (g a) = a * ⅟(p : E) := by
    rw [hg, map_smul, he, smul_eq_mul]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective g
  constructor
  · intro a b hab
    have h := congrArg (fun v => e v * (p : E)) hab
    simpa only [hge, mul_assoc, invOf_mul_self, mul_one] using h
  · intro v
    refine ⟨e v * (p : E), e.injective ?_⟩
    rw [hge, mul_assoc, mul_invOf_self, mul_one]

end GeometricGenerator

#print axioms artinSchreierRingCharacterIdentitySection
#print axioms artinSchreierRingCharacterIdentitySectionMap
#print axioms artinSchreierRingCharacterIdentitySectionMap_apply
#print axioms artinSchreierRingCharacterIdentitySection_inclusion
#print axioms artinSchreierRingCharacterIdentitySection_germ_inclusion
#print axioms artinSchreierRingPointFreeAverage_freeMk_self
#print axioms artinSchreierRingCharacterIdentitySection_germ_evaluation
#print axioms artinSchreierRingCharacterIdentitySectionMap_stalk_isIso

end PrimeGap182.TypeIII
