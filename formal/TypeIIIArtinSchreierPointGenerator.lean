import TypeIIIArtinSchreierPointStalk

/-!
# The projected identity section at actual geometric points

The identity of the Artin--Schreier covering object gives a section of
the free representable sheaf.  At a lifted site point, its actual germ
maps to the corresponding free basis vector through the canonical
stalk comparison.  Projecting this vector and evaluating at the same
root gives p⁻¹.  Thus, when p is nonzero in the coefficient field, the
projected section is nonzero on every such geometric fiber.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

section IdentityGerm

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R) (E : Type u) [CommRing E]

/-- The actual section obtained by sheafifying the free generator
corresponding to the identity of the covering object. -/
def artinSchreierFreeSheafIdentitySection :
    (artinSchreierFreeSheaf p f E).obj.obj (op (artinSchreierEtaleObject p f)) :=
  (CategoryTheory.toSheafify (Spec (.of R)).smallEtaleTopology
    (artinSchreierFreePresheaf p f E)).app (op (artinSchreierEtaleObject p f))
      (ModuleCat.freeMk (shrinkYonedaObjObjEquiv.symm (𝟙 (artinSchreierEtaleObject p f))))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual identity-section germ maps to the basis vector indexed
by the lifted point, through all three canonical stalk comparisons. -/
theorem artinSchreierFreeSheaf_stalkIso_identityGerm
    (Φ : GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology)
    (t : Φ.fiber.obj (artinSchreierEtaleObject p f)) :
    (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        (Φ.toPresheafFiber (artinSchreierEtaleObject p f) t
          (artinSchreierFreeSheaf p f E).obj
            (artinSchreierFreeSheafIdentitySection p f E)) =
      ModuleCat.freeMk t := by
  let : (ModuleCat.free E).IsLeftAdjoint := (ModuleCat.adj E).isLeftAdjoint
  let Y := artinSchreierEtaleObject p f
  let P := shrinkYoneda.{u}.obj Y ⋙ ModuleCat.free E
  let Q := sheafify (Spec (.of R)).smallEtaleTopology P
  let η := CategoryTheory.toSheafify (Spec (.of R)).smallEtaleTopology P
  let x₀ : (shrinkYoneda.{u}.obj Y).obj (op Y) :=
    shrinkYonedaObjObjEquiv.symm (𝟙 Y)
  let e₁ : Φ.presheafFiber.obj Q ≅ Φ.presheafFiber.obj P :=
    (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u} E)).app P
  let e₂ : Φ.presheafFiber.obj P ≅
      (ModuleCat.free E).obj (Φ.presheafFiber.obj (shrinkYoneda.{u}.obj Y)) :=
    (Φ.presheafFiberCompIso (ModuleCat.free E)).app (shrinkYoneda.{u}.obj Y)
  let e₃ : Φ.presheafFiber.obj (shrinkYoneda.{u}.obj Y) ≅ Φ.fiber.obj Y :=
    Φ.shrinkYonedaCompPresheafFiberIso.app Y
  have h₁ :
      η.app (op Y) ≫ Φ.toPresheafFiber Y t Q ≫
        e₁.hom = Φ.toPresheafFiber Y t P := by
    rw [← Category.assoc, ← Φ.toPresheafFiber_naturality η Y t]
    change (Φ.toPresheafFiber Y t P ≫ e₁.inv) ≫ e₁.hom = _
    simp
  have h₁v := congrArg (fun g => g (ModuleCat.freeMk x₀)) h₁
  have h₂ := Φ.toPresheafFiber_presheafFiberCompIso_hom_app
    (ModuleCat.free E) Y t (shrinkYoneda.{u}.obj Y)
  have h₂v := congrArg (fun g => g (ModuleCat.freeMk x₀)) h₂
  simp only [ModuleCat.comp_apply] at h₁v h₂v
  change e₂.hom (Φ.toPresheafFiber Y t P (ModuleCat.freeMk x₀)) =
    (ModuleCat.free E).map (Φ.toPresheafFiber Y t (shrinkYoneda.{u}.obj Y))
      (ModuleCat.freeMk x₀) at h₂v
  change (ModuleCat.free E).map e₃.hom
      (e₂.hom (e₁.hom (Φ.toPresheafFiber Y t Q
        (η.app (op Y) (ModuleCat.freeMk x₀))))) = _
  rw [h₁v, h₂v, ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  have h₃ : e₃.inv t = Φ.toPresheafFiber Y t (shrinkYoneda.{u}.obj Y) x₀ :=
    Φ.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber t
  rw [← h₃]
  exact congrArg (fun x => ModuleCat.freeMk x) (e₃.toEquiv.apply_symm_apply t)

end IdentityGerm

section ProjectedGenerator

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra (ZMod p) Ω] (f : R)

section RingDelta

variable (E : Type u) [CommRing E]

/-- A free basis vector becomes the delta function at its actual
specialized root coordinate. -/
@[simp] theorem artinSchreierPointFreeEquivFunctions_freeMk
    (t : ArtinSchreierPointSiteFiber p R Ω f)
    (z : ArtinSchreierFiber p K Ω (algebraMap R K f)) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E (ModuleCat.freeMk t) z =
      if artinSchreierPointSiteEquivRoots p R Ω f K t = z then 1 else 0 := by
  rw [artinSchreierPointFreeEquivFunctions_apply]
  change (Finsupp.single t (1 : E))
      ((artinSchreierPointSiteEquivRoots p R Ω f K).symm z) = _
  simp only [Finsupp.single_apply, Equiv.eq_symm_apply]

end RingDelta

variable (E : Type u) [Field E]

/-- Projecting a basis vector and evaluating at that same root gives
p⁻¹.  Freeness of the actual root translations removes every other term. -/
theorem artinSchreierPointFreeAverage_freeMk_self (ψ : AddChar (ZMod p) E)
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        (artinSchreierCharacterFreeFiberAverage p f E ψ
          (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) (ModuleCat.freeMk t))
        (artinSchreierPointSiteEquivRoots p R Ω f K t) = (p : E)⁻¹ := by
  rw [artinSchreierPointFreeEquivFunctions_average,
    artinSchreierCharacterProjection_apply]
  let z := artinSchreierPointSiteEquivRoots p R Ω f K t
  have hf (a : ZMod p) :
      z = artinSchreierFiberTranslate p K Ω (algebraMap R K f) a z ↔ a = 0 := by
    constructor
    · intro h
      apply artinSchreierFiberTranslate_injective p K Ω (algebraMap R K f) z
      exact h.symm.trans (artinSchreierFiberTranslate_zero p K Ω (algebraMap R K f) z).symm
    · rintro rfl
      exact (artinSchreierFiberTranslate_zero p K Ω (algebraMap R K f) z).symm
  have hs :
      (∑ a : ZMod p, ψ (-a) *
        artinSchreierPointFreeEquivFunctions p R K Ω f E (ModuleCat.freeMk t)
          (artinSchreierFiberTranslate p K Ω (algebraMap R K f) a z)) = 1 := by
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · rw [artinSchreierFiberTranslate_zero, artinSchreierPointFreeEquivFunctions_freeMk]
      simp [z]
    · intro a _ha ha
      rw [artinSchreierPointFreeEquivFunctions_freeMk, ite_eq_right ((hf a).not.mpr ha)]
      simp
    · simp
  change (p : E)⁻¹ * _ = _
  rw [hs, mul_one]

/-- The self-evaluation of the projected basis vector is nonzero when
p is nonzero in the coefficient field. -/
theorem artinSchreierPointFreeAverage_freeMk_self_ne_zero (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) (t : ArtinSchreierPointSiteFiber p R Ω f) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        (artinSchreierCharacterFreeFiberAverage p f E ψ
          (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) (ModuleCat.freeMk t))
        (artinSchreierPointSiteEquivRoots p R Ω f K t) ≠ 0 := by
  rw [artinSchreierPointFreeAverage_freeMk_self]
  exact inv_ne_zero hpE

include K in
/-- The actual projected free basis vector is nonzero, as detected by
its proved root-coordinate evaluation. -/
theorem artinSchreierPointFreeAverage_freeMk_ne_zero (ψ : AddChar (ZMod p) E)
    (hpE : (p : E) ≠ 0) (t : ArtinSchreierPointSiteFiber p R Ω f) :
    artinSchreierCharacterFreeFiberAverage p f E ψ
        (Scheme.pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) (ModuleCat.freeMk t) ≠ 0 := by
  intro h
  have hz := artinSchreierPointFreeAverage_freeMk_self_ne_zero p R K Ω f E ψ hpE t
  rw [h, map_zero, Pi.zero_apply] at hz
  exact hz rfl

end ProjectedGenerator

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierFreeSheafIdentitySection
#print axioms PrimeGap182.TypeIII.artinSchreierFreeSheaf_stalkIso_identityGerm
#print axioms PrimeGap182.TypeIII.artinSchreierPointFreeEquivFunctions_freeMk
#print axioms PrimeGap182.TypeIII.artinSchreierPointFreeAverage_freeMk_self
#print axioms PrimeGap182.TypeIII.artinSchreierPointFreeAverage_freeMk_self_ne_zero
#print axioms PrimeGap182.TypeIII.artinSchreierPointFreeAverage_freeMk_ne_zero
