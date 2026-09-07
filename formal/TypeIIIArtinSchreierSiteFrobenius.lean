import TypeIIIArtinSchreierSheaf
import TypeIIIArtinSchreierStalkFunctions
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Frobenius from the actual geometric point of the small étale site

An automorphism of the geometric coefficient field over the base gives
an actual automorphism of `Spec Ω` over the base.  Precomposition gives a
natural automorphism of the small étale fiber functor.  Mathlib's point
morphism construction then induces natural automorphisms of the actual
presheaf and sheaf fiber functors, including module-valued stalks.

For a finite base field and an algebraic geometric coefficient field,
the arithmetic automorphism is the actual `card K`-power field map.  Its
action on the Artin--Schreier site fiber is proved using the spectrum
diagrams and agrees with applying this field map to algebra homomorphisms.
Geometric Frobenius uses the inverse field automorphism.
-/

noncomputable section

universe u v w v₂ w₂

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

section FieldAutomorphism

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]

/-- The actual geometric point of the small étale site supplied by the
given separably closed coefficient field. -/
abbrev smallEtaleGeometricPoint :
    GrothendieckTopology.Point.{u} (Spec (.of R)).smallEtaleTopology :=
  Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))

/-- The spectrum of a coefficient-field automorphism is a map over the
actual base scheme, by its algebra compatibility. -/
def smallEtaleFieldOverHom (σ : Ω ≃ₐ[R] Ω) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap R Ω))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext r
    exact σ.commutes r)

/-- The inverse field automorphism gives the actual inverse scheme map. -/
def smallEtaleFieldOverIso (σ : Ω ≃ₐ[R] Ω) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) where
  hom := smallEtaleFieldOverHom R Ω σ
  inv := smallEtaleFieldOverHom R Ω σ.symm
  hom_inv_id := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom σ.symm.toAlgHom.toRingHom) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : σ.toAlgHom.toRingHom.comp σ.symm.toAlgHom.toRingHom = RingHom.id Ω := by
      ext x
      exact σ.apply_symm_apply x
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom σ.symm.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : σ.symm.toAlgHom.toRingHom.comp σ.toAlgHom.toRingHom = RingHom.id Ω := by
      ext x
      exact σ.symm_apply_apply x
    rw [h, CommRingCat.ofHom_id, Spec.map_id]

/-- Precomposition by the actual `Spec σ` gives a natural automorphism of
the entire small étale fiber functor. -/
def smallEtaleFieldFiberIso (σ : Ω ≃ₐ[R] Ω) :
    (smallEtaleGeometricPoint R Ω).fiber ≅ (smallEtaleGeometricPoint R Ω).fiber :=
  Functor.isoWhiskerLeft (Scheme.Etale.forget (Spec (.of R)))
    (coyoneda.mapIso (smallEtaleFieldOverIso R Ω σ).op)

/-- On every étale object this is literal precomposition of scheme points. -/
@[simp] theorem smallEtaleFieldFiberIso_hom_left (σ : Ω ≃ₐ[R] Ω)
    (Y : (Spec (.of R)).Etale) (t : (smallEtaleGeometricPoint R Ω).fiber.obj Y) :
    ((smallEtaleFieldFiberIso R Ω σ).hom.app Y t).left =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ t.left := rfl

/-- Package the actual fiber automorphism as an isomorphism of site
points, using Mathlib's opposite-direction convention for point maps. -/
def smallEtaleFieldPointIso (σ : Ω ≃ₐ[R] Ω) :
    smallEtaleGeometricPoint R Ω ≅ smallEtaleGeometricPoint R Ω where
  hom := ⟨(smallEtaleFieldFiberIso R Ω σ).hom⟩
  inv := ⟨(smallEtaleFieldFiberIso R Ω σ).inv⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleFieldFiberIso R Ω σ).inv_hom_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleFieldFiberIso R Ω σ).hom_inv_id

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The point morphism acts on actual presheaf fibers by the colimit
construction, independently of any Artin--Schreier comparison isomorphism. -/
def smallEtaleFieldPresheafFiberIso (σ : Ω ≃ₐ[R] Ω) :
    (smallEtaleGeometricPoint R Ω).presheafFiber (A := A) ≅
      (smallEtaleGeometricPoint R Ω).presheafFiber (A := A) where
  hom := (smallEtaleFieldPointIso R Ω σ).hom.presheafFiber
  inv := (smallEtaleFieldPointIso R Ω σ).inv.presheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, Iso.inv_hom_id,
      GrothendieckTopology.Point.Hom.presheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, Iso.hom_inv_id,
      GrothendieckTopology.Point.Hom.presheafFiber_id]

/-- The same actual point isomorphism induces a natural automorphism on
the stalk functor for arbitrary sheaves with these coefficients. -/
def smallEtaleFieldSheafFiberIso (σ : Ω ≃ₐ[R] Ω) :
    (smallEtaleGeometricPoint R Ω).sheafFiber (A := A) ≅
      (smallEtaleGeometricPoint R Ω).sheafFiber (A := A) where
  hom := (smallEtaleFieldPointIso R Ω σ).hom.sheafFiber
  inv := (smallEtaleFieldPointIso R Ω σ).inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- On a germ represented on an actual étale neighborhood, the induced
presheaf-fiber map changes the point by precomposition with `Spec σ`. -/
theorem smallEtaleFieldPresheafFiberIso_germ (σ : Ω ≃ₐ[R] Ω)
    (Y : (Spec (.of R)).Etale) (t : (smallEtaleGeometricPoint R Ω).fiber.obj Y)
    (P : (Spec (.of R)).Etaleᵒᵖ ⥤ A) :
    (smallEtaleGeometricPoint R Ω).toPresheafFiber Y t P ≫
        (smallEtaleFieldPresheafFiberIso R Ω A σ).hom.app P =
      (smallEtaleGeometricPoint R Ω).toPresheafFiber Y
        ((smallEtaleFieldFiberIso R Ω σ).hom.app Y t) P := by
  change _ ≫ (smallEtaleFieldPointIso R Ω σ).hom.presheafFiber.app P = _
  rw [GrothendieckTopology.Point.Hom.presheafFiber_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _]
  rfl

end FieldAutomorphism

section PointComparisons

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]

/-- The inverse representable-stalk comparison sends a point to the germ
of the identity, so the actual point action commutes with that comparison. -/
theorem smallEtaleFieldPresheafFiberIso_shrinkYoneda_inv (σ : Ω ≃ₐ[R] Ω)
    (Y : (Spec (.of R)).Etale) :
    (smallEtaleGeometricPoint R Ω).shrinkYonedaCompPresheafFiberIso.inv.app Y ≫
        (smallEtaleFieldPresheafFiberIso R Ω (Type u) σ).hom.app (shrinkYoneda.{u}.obj Y) =
      (smallEtaleFieldFiberIso R Ω σ).hom.app Y ≫
        (smallEtaleGeometricPoint R Ω).shrinkYonedaCompPresheafFiberIso.inv.app Y := by
  apply ConcreteCategory.hom_ext
  intro t
  have h := ConcreteCategory.congr_hom
    (smallEtaleFieldPresheafFiberIso_germ R Ω (Type u) σ Y t (shrinkYoneda.{u}.obj Y))
    (shrinkYonedaObjObjEquiv.{u}.symm (𝟙 Y))
  exact (congrArg
    ((smallEtaleFieldPresheafFiberIso R Ω (Type u) σ).hom.app (shrinkYoneda.{u}.obj Y))
    ((smallEtaleGeometricPoint R Ω).shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber t)).trans
      (h.trans ((smallEtaleGeometricPoint R Ω).shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber
        ((smallEtaleFieldFiberIso R Ω σ).hom.app Y t)).symm)

/-- Point naturality of the actual representable-stalk comparison. -/
theorem smallEtaleFieldPresheafFiberIso_shrinkYoneda (σ : Ω ≃ₐ[R] Ω)
    (Y : (Spec (.of R)).Etale) :
    (smallEtaleFieldPresheafFiberIso R Ω (Type u) σ).hom.app (shrinkYoneda.{u}.obj Y) ≫
        (smallEtaleGeometricPoint R Ω).shrinkYonedaCompPresheafFiberIso.hom.app Y =
      (smallEtaleGeometricPoint R Ω).shrinkYonedaCompPresheafFiberIso.hom.app Y ≫
        (smallEtaleFieldFiberIso R Ω σ).hom.app Y := by
  apply (cancel_epi
    ((smallEtaleGeometricPoint R Ω).shrinkYonedaCompPresheafFiberIso.inv.app Y)).mp
  rw [← Category.assoc, smallEtaleFieldPresheafFiberIso_shrinkYoneda_inv]
  simp

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]
  {B : Type v₂} [Category.{w₂} B] [HasColimitsOfSize.{u, u} B]

/-- The colimit comparison with a filtered-colimit-preserving coefficient
functor is natural for the actual coefficient-field point action. -/
theorem smallEtaleFieldPresheafFiberIso_compFunctor
    (F : A ⥤ B) [PreservesFilteredColimitsOfSize.{u, u} F]
    (σ : Ω ≃ₐ[R] Ω) (P : (Spec (.of R)).Etaleᵒᵖ ⥤ A) :
    (smallEtaleFieldPresheafFiberIso R Ω B σ).hom.app (P ⋙ F) ≫
        ((smallEtaleGeometricPoint R Ω).presheafFiberCompIso F).hom.app P =
      ((smallEtaleGeometricPoint R Ω).presheafFiberCompIso F).hom.app P ≫
        F.map ((smallEtaleFieldPresheafFiberIso R Ω A σ).hom.app P) := by
  apply (smallEtaleGeometricPoint R Ω).presheafFiber_hom_ext
  intro Y t
  rw [← Category.assoc, smallEtaleFieldPresheafFiberIso_germ,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app]
  rw [← Category.assoc,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app,
    ← F.map_comp, smallEtaleFieldPresheafFiberIso_germ]

/-- The sheafification comparison is natural for the actual point action;
this follows from naturality at the sheafification unit and its stalk isomorphism. -/
theorem smallEtaleFieldSheafFiberIso_sheafification
    [HasProducts.{u} A] [HasWeakSheafify (Spec (.of R)).smallEtaleTopology A]
    (σ : Ω ≃ₐ[R] Ω) (P : (Spec (.of R)).Etaleᵒᵖ ⥤ A) :
    (smallEtaleFieldSheafFiberIso R Ω A σ).hom.app
        ((presheafToSheaf (Spec (.of R)).smallEtaleTopology A).obj P) ≫
          ((smallEtaleGeometricPoint R Ω).presheafToSheafCompSheafFiberIso A).hom.app P =
      ((smallEtaleGeometricPoint R Ω).presheafToSheafCompSheafFiberIso A).hom.app P ≫
        (smallEtaleFieldPresheafFiberIso R Ω A σ).hom.app P := by
  let e := ((smallEtaleGeometricPoint R Ω).presheafToSheafCompSheafFiberIso A).app P
  apply (cancel_epi e.inv).mp
  have h : e.inv ≫ (smallEtaleFieldSheafFiberIso R Ω A σ).hom.app
      ((presheafToSheaf (Spec (.of R)).smallEtaleTopology A).obj P) =
        (smallEtaleFieldPresheafFiberIso R Ω A σ).hom.app P ≫ e.inv :=
    (smallEtaleFieldPresheafFiberIso R Ω A σ).hom.naturality
      (CategoryTheory.toSheafify (Spec (.of R)).smallEtaleTopology P)
  change e.inv ≫ (_ ≫ e.hom) = e.inv ≫ (e.hom ≫ _)
  rw [← Category.assoc, h]
  simp

end PointComparisons

section ActualStalkComparison

variable (p : ℕ) [Fact p.Prime] {R Ω : Type u} [CommRing R] [CharP R p]
  [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (f : R) (E : Type u) [CommRing E]

/-- The actual point-induced module stalk action agrees, under the
proved stalk comparison, with pushing free generators by the site-fiber
permutation.  This is derived from all three canonical comparisons. -/
theorem artinSchreierFreeSheaf_stalk_fieldAutomorphism (σ : Ω ≃ₐ[R] Ω) :
    (smallEtaleFieldSheafFiberIso R Ω (ModuleCat.{u} E) σ).hom.app
        (artinSchreierFreeSheaf p f E) ≫
          (artinSchreierFreeSheaf_stalkIso p f E (smallEtaleGeometricPoint R Ω)).hom =
      (artinSchreierFreeSheaf_stalkIso p f E (smallEtaleGeometricPoint R Ω)).hom ≫
        (ModuleCat.free E).map
          ((smallEtaleFieldFiberIso R Ω σ).hom.app (artinSchreierEtaleObject p f)) := by
  let : (ModuleCat.free E).IsLeftAdjoint := (ModuleCat.adj E).isLeftAdjoint
  have h₁ := smallEtaleFieldSheafFiberIso_sheafification R Ω (ModuleCat.{u} E) σ
    (artinSchreierFreePresheaf p f E)
  have h₂ := smallEtaleFieldPresheafFiberIso_compFunctor R Ω (Type u) (ModuleCat.free E) σ
    (shrinkYoneda.{u}.obj (artinSchreierEtaleObject p f))
  have h₃ := congrArg (fun h => (ModuleCat.free E).map h)
    (smallEtaleFieldPresheafFiberIso_shrinkYoneda R Ω σ (artinSchreierEtaleObject p f))
  simp only [Functor.map_comp] at h₃
  dsimp only [artinSchreierFreeSheaf_stalkIso, artinSchreierFreeSheaf,
    artinSchreierFreePresheaf] at *
  change _ ≫ (_ ≫ _ ≫ _) = (_ ≫ _ ≫ _) ≫ _
  simp only [Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ ((ModuleCat.free E).map _), h₂]
  simp only [Category.assoc]
  rw [h₃]

end ActualStalkComparison

section ActualArtinSchreierFiber

variable (p : ℕ) [Fact p.Prime] (K Ω : Type u) [Field K] [CharP K p]
  [Field Ω] [IsSepClosed Ω] [Algebra K Ω] (f : K)

/-- On the Artin--Schreier object, the site-functor action agrees with
composition of the actual coordinate homomorphism with the field map. -/
theorem smallEtaleFieldFiberIso_artinSchreierPoint (σ : Ω ≃ₐ[K] Ω)
    (g : ArtinSchreierCover p K f →ₐ[K] Ω) :
    (smallEtaleFieldFiberIso K Ω σ).hom.app (artinSchreierEtaleObject p f)
        (artinSchreierEtaleFiberPoint p f g) =
      artinSchreierEtaleFiberPoint p f (σ.toAlgHom.comp g) := by
  apply Over.OverMorphism.ext
  rw [smallEtaleFieldFiberIso_hom_left, artinSchreierEtaleFiberPoint_left,
    artinSchreierEtaleFiberPoint_left]
  change Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom g.toRingHom) =
      Spec.map (CommRingCat.ofHom (σ.toAlgHom.comp g).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Reading the algebra homomorphism from any actual site point
intertwines the site action with the coefficient-field automorphism. -/
theorem smallEtaleFieldFiberIso_artinSchreierHom (σ : Ω ≃ₐ[K] Ω)
    (t : ArtinSchreierSiteFiber p K Ω f) :
    (artinSchreierHomEquivEtaleFiber p f).symm
        ((smallEtaleFieldFiberIso K Ω σ).hom.app (artinSchreierEtaleObject p f) t) =
      σ.toAlgHom.comp ((artinSchreierHomEquivEtaleFiber p f).symm t) := by
  obtain ⟨g, rfl⟩ := (artinSchreierHomEquivEtaleFiber p f).surjective t
  change (artinSchreierHomEquivEtaleFiber p f).symm
      ((smallEtaleFieldFiberIso K Ω σ).hom.app (artinSchreierEtaleObject p f)
        (artinSchreierEtaleFiberPoint p f g)) = _
  rw [smallEtaleFieldFiberIso_artinSchreierPoint]
  change (artinSchreierHomEquivEtaleFiber p f).symm
      ((artinSchreierHomEquivEtaleFiber p f) (σ.toAlgHom.comp g)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end ActualArtinSchreierFiber

section FiniteFieldFrobenius

variable (K Ω : Type u) [Field K] [Fintype K] [Field Ω]
  [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]

/-- Arithmetic Frobenius is the actual `card K`-power automorphism of the
algebraic geometric coefficient field. -/
def smallEtaleArithmeticFrobenius : Ω ≃ₐ[K] Ω :=
  FiniteField.frobeniusAlgEquivOfAlgebraic K Ω

omit [IsSepClosed Ω] in
@[simp] theorem smallEtaleArithmeticFrobenius_apply (x : Ω) :
    smallEtaleArithmeticFrobenius K Ω x = x ^ Fintype.card K := rfl

/-- Arithmetic Frobenius acts naturally on the whole geometric fiber
functor by its actual spectrum map. -/
def smallEtaleArithmeticFrobeniusFiberIso :
    (smallEtaleGeometricPoint K Ω).fiber ≅ (smallEtaleGeometricPoint K Ω).fiber :=
  smallEtaleFieldFiberIso K Ω (smallEtaleArithmeticFrobenius K Ω)

/-- Geometric Frobenius uses the inverse arithmetic field automorphism. -/
def smallEtaleGeometricFrobeniusFiberIso :
    (smallEtaleGeometricPoint K Ω).fiber ≅ (smallEtaleGeometricPoint K Ω).fiber :=
  smallEtaleFieldFiberIso K Ω (smallEtaleArithmeticFrobenius K Ω).symm

variable (E : Type u) [CommRing E]

/-- Arithmetic Frobenius on actual module sheaf stalks stores the
arithmetic permutation on geometric points. -/
def smallEtaleArithmeticFrobeniusModuleStalkIso :
    (smallEtaleGeometricPoint K Ω).sheafFiber (A := ModuleCat.{u} E) ≅
      (smallEtaleGeometricPoint K Ω).sheafFiber (A := ModuleCat.{u} E) :=
  smallEtaleFieldSheafFiberIso K Ω (ModuleCat.{u} E)
    (smallEtaleArithmeticFrobenius K Ω)

/-- The induced geometric Frobenius automorphism of the actual functor
taking module sheaves to their stalks at this geometric point. -/
def smallEtaleGeometricFrobeniusModuleStalkIso :
    (smallEtaleGeometricPoint K Ω).sheafFiber (A := ModuleCat.{u} E) ≅
      (smallEtaleGeometricPoint K Ω).sheafFiber (A := ModuleCat.{u} E) :=
  smallEtaleFieldSheafFiberIso K Ω (ModuleCat.{u} E)
    (smallEtaleArithmeticFrobenius K Ω).symm

variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP Ω p]
  [Algebra (ZMod p) K] [Algebra (ZMod p) Ω] [IsScalarTower (ZMod p) K Ω] (f : K)

/-- On the actual Artin--Schreier site fiber, arithmetic Frobenius is the
proved power-map permutation of roots, obtained from the site action. -/
theorem artinSchreierSiteFiberEquivRoots_arithmeticFrobenius
    (t : ArtinSchreierSiteFiber p K Ω f) :
    artinSchreierSiteFiberEquivRoots p K Ω f
        ((smallEtaleArithmeticFrobeniusFiberIso K Ω).hom.app
          (artinSchreierEtaleObject p f) t) =
      artinSchreierArithmeticFrobenius p K Ω f
        (artinSchreierSiteFiberEquivRoots p K Ω f t) := by
  change artinSchreierHomEquivFiber p K Ω f
      ((artinSchreierHomEquivEtaleFiber p f).symm
        ((smallEtaleFieldFiberIso K Ω (smallEtaleArithmeticFrobenius K Ω)).hom.app
          (artinSchreierEtaleObject p f) t)) = _
  rw [smallEtaleFieldFiberIso_artinSchreierHom]
  exact artinSchreierHomEquivFiber_frobenius p K Ω f
    ((artinSchreierHomEquivEtaleFiber p f).symm t)

end FiniteFieldFrobenius

#print axioms smallEtaleGeometricPoint
#print axioms smallEtaleFieldOverHom
#print axioms smallEtaleFieldOverIso
#print axioms smallEtaleFieldFiberIso
#print axioms smallEtaleFieldFiberIso_hom_left
#print axioms smallEtaleFieldPointIso
#print axioms smallEtaleFieldPresheafFiberIso
#print axioms smallEtaleFieldSheafFiberIso
#print axioms smallEtaleFieldPresheafFiberIso_germ
#print axioms smallEtaleFieldPresheafFiberIso_shrinkYoneda_inv
#print axioms smallEtaleFieldPresheafFiberIso_shrinkYoneda
#print axioms smallEtaleFieldPresheafFiberIso_compFunctor
#print axioms smallEtaleFieldSheafFiberIso_sheafification
#print axioms artinSchreierFreeSheaf_stalk_fieldAutomorphism
#print axioms smallEtaleFieldFiberIso_artinSchreierPoint
#print axioms smallEtaleFieldFiberIso_artinSchreierHom
#print axioms smallEtaleArithmeticFrobenius
#print axioms smallEtaleArithmeticFrobenius_apply
#print axioms smallEtaleArithmeticFrobeniusFiberIso
#print axioms smallEtaleGeometricFrobeniusFiberIso
#print axioms smallEtaleArithmeticFrobeniusModuleStalkIso
#print axioms smallEtaleGeometricFrobeniusModuleStalkIso
#print axioms artinSchreierSiteFiberEquivRoots_arithmeticFrobenius

end PrimeGap182.TypeIII
