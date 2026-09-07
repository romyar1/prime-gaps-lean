import TypeIIIArtinSchreierCover
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The finite étale Artin--Schreier scheme

The scheme in this file is the spectrum of the actual quotient algebra
constructed in TypeIIIArtinSchreierCover.  Its structural morphism is the
spectrum of the algebra map.  Finiteness and étaleness follow from the
proved algebraic properties of that quotient, so no morphism property is
assumed in the construction of its object in the small étale site.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry Polynomial
open scoped Classical

section Scheme

variable (p : ℕ) (R : Type u) [CommRing R]

/-- The spectrum of the literal Artin--Schreier quotient algebra. -/
def artinSchreierScheme (f : R) : Scheme.{u} :=
  Spec (.of (ArtinSchreierCover p R f))

variable {R}

/-- The actual structure morphism induced by the quotient's algebra map. -/
def artinSchreierSchemeMap (f : R) :
    artinSchreierScheme p R f ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f)))

variable [Fact p.Prime] [CharP R p]

/-- The scheme morphism is finite because its coordinate algebra is finite. -/
theorem artinSchreierSchemeMap_finite (f : R) :
    IsFinite (artinSchreierSchemeMap p f) := by
  change IsFinite
    (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f))))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr (artinSchreierCover_finite p f)

/-- The scheme morphism is étale by the proved standard étale presentation. -/
theorem artinSchreierSchemeMap_etale (f : R) :
    AlgebraicGeometry.Etale (artinSchreierSchemeMap p f) := by
  change AlgebraicGeometry.Etale
    (Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f))))
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  exact RingHom.etale_algebraMap.mpr (artinSchreierCover_etale p f)

/-- The nonzero free quotient is faithfully flat over its coefficient ring. -/
theorem artinSchreierCover_faithfullyFlat (f : R) :
    Module.FaithfullyFlat R (ArtinSchreierCover p R f) := by
  let : Nontrivial R := artinSchreierBase_nontrivial p
  have hd : 0 < (artinSchreierPolynomial p f).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, artinSchreierPolynomial_natDegree]
    exact (Fact.out : p.Prime).pos
  have hinj := AdjoinRoot.of.injective_of_monic_of_degree_pos
    (artinSchreierPolynomial_monic p f) hd
  let : Nontrivial (ArtinSchreierCover p R f) := Function.Injective.nontrivial hinj
  let := artinSchreierCover_free p f
  infer_instance

/-- Positive free rank makes the actual spectrum morphism surjective. -/
theorem artinSchreierSchemeMap_surjective (f : R) :
    AlgebraicGeometry.Surjective (artinSchreierSchemeMap p f) := by
  have hff : (algebraMap R (ArtinSchreierCover p R f)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr (artinSchreierCover_faithfullyFlat p f)
  exact (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f)))).mpr hff |>.2

set_option backward.isDefEq.respectTransparency.types false in
/-- The one actual finite étale morphism is an étale covering of the base. -/
def artinSchreierEtaleCover (f : R) :
    (Spec (.of R)).Cover (Scheme.precoverage @AlgebraicGeometry.Etale) :=
  .singleton (artinSchreierSchemeMap p f) (by
    rw [Scheme.singleton_mem_precoverage_iff]
    exact ⟨(artinSchreierSchemeMap_surjective p f).surj,
      artinSchreierSchemeMap_etale p f⟩)

/-- The finite étale quotient defines an actual object of the small étale site. -/
def artinSchreierEtaleObject (f : R) : (Spec (.of R)).Etale := by
  letI := artinSchreierSchemeMap_etale p f
  exact Scheme.Etale.mk (artinSchreierSchemeMap p f)

/-- The underlying scheme of the site object is the displayed quotient spectrum. -/
@[simp] theorem artinSchreierEtaleObject_left (f : R) :
    (artinSchreierEtaleObject p f).left = artinSchreierScheme p R f := rfl

/-- The structural map of the site object is the actual spectrum map. -/
@[simp] theorem artinSchreierEtaleObject_hom (f : R) :
    (artinSchreierEtaleObject p f).hom = artinSchreierSchemeMap p f := rfl

/-- The structural arrow in the small étale category goes to the base object. -/
def artinSchreierEtaleToBase (f : R) :
    artinSchreierEtaleObject p f ⟶ Scheme.Etale.mk (𝟙 (Spec (.of R))) :=
  MorphismProperty.Over.homMk (artinSchreierSchemeMap p f) (by
    change artinSchreierSchemeMap p f ≫ 𝟙 _ = artinSchreierSchemeMap p f
    exact Category.comp_id _)

/-- The singleton structural arrow generates a covering sieve in the actual
small étale topology. -/
theorem artinSchreierEtaleToBase_covering (f : R) :
    Sieve.ofArrows (fun _ : PUnit => artinSchreierEtaleObject p f)
      (fun _ => artinSchreierEtaleToBase p f) ∈
        Scheme.smallEtaleTopology (Spec (.of R))
          (Scheme.Etale.mk (𝟙 (Spec (.of R)))) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  change (⋃ _ : PUnit, Set.range (artinSchreierSchemeMap p f)) = Set.univ
  simpa only [Set.iUnion_const] using
    Set.range_eq_univ.mpr (artinSchreierSchemeMap_surjective p f).surj

end Scheme

section Points

variable (p : ℕ) {R Ω : Type u} [CommRing R] [CommRing Ω] [Algebra R Ω] (f : R)

/-- An algebra homomorphism into a coefficient extension gives its actual
affine scheme point by applying the spectrum functor. -/
def artinSchreierSchemePoint (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    Spec (.of Ω) ⟶ artinSchreierScheme p R f :=
  Spec.map (CommRingCat.ofHom g.toRingHom)

/-- The affine point lies over the specified base point, as a scheme diagram. -/
theorem artinSchreierSchemePoint_over (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    artinSchreierSchemePoint p f g ≫ artinSchreierSchemeMap p f =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact g.commutes x

/-- Recovering the coordinate-ring map from this scheme point gives the
original homomorphism. -/
@[simp] theorem artinSchreierSchemePoint_preimage
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    Spec.preimage (artinSchreierSchemePoint p f g) = CommRingCat.ofHom g.toRingHom :=
  Spec.preimage_map _

/-- On the actual geometric point the distinguished coordinate is evaluated
by the same algebra homomorphism as in the polynomial-root fiber. -/
@[simp] theorem artinSchreierSchemePoint_root
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (Spec.preimage (artinSchreierSchemePoint p f g)).hom (artinSchreierRoot p f) =
      g (artinSchreierRoot p f) := by
  rw [artinSchreierSchemePoint_preimage]
  rfl

end Points

section GeometricSitePoint

variable (p : ℕ) [Fact p.Prime] {R Ω : Type u} [CommRing R] [CharP R p]
  [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (f : R)

/-- The same quotient homomorphism gives an element of the actual geometric
fiber functor on the small étale site. -/
def artinSchreierEtaleFiberPoint (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.obj
        (artinSchreierEtaleObject p f) :=
  Over.homMk (artinSchreierSchemePoint p f g) (artinSchreierSchemePoint_over p f g)

/-- Forgetting the site-fiber element returns precisely the spectrum of the
given quotient homomorphism. -/
@[simp] theorem artinSchreierEtaleFiberPoint_left
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (artinSchreierEtaleFiberPoint p f g).left = artinSchreierSchemePoint p f g := rfl

/-- The geometric site point and the distinguished-root evaluation agree. -/
@[simp] theorem artinSchreierEtaleFiberPoint_root
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (Spec.preimage (artinSchreierEtaleFiberPoint p f g).left).hom
        (artinSchreierRoot p f) = g (artinSchreierRoot p f) :=
  artinSchreierSchemePoint_root p f g

set_option backward.isDefEq.respectTransparency.types false in
/-- A geometric point of the site object recovers a homomorphism from the
actual quotient algebra.  The algebra compatibility comes from the
commuting triangle in the over category. -/
def artinSchreierEtaleFiberHom
    (t : (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.obj
        (artinSchreierEtaleObject p f)) :
    ArtinSchreierCover p R f →ₐ[R] Ω := by
  refine ⟨(Spec.preimage t.left).hom, ?_⟩
  have hw : CommRingCat.ofHom (algebraMap R (ArtinSchreierCover p R f)) ≫
      Spec.preimage t.left = CommRingCat.ofHom (algebraMap R Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact t.w
  intro r
  exact congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of Ω => h r) hw

set_option backward.isDefEq.respectTransparency.types false in
/-- The geometric fiber of the site object is exactly the quotient's
algebra-homomorphism fiber, not merely a map from the polynomial roots. -/
def artinSchreierHomEquivEtaleFiber :
    (ArtinSchreierCover p R f →ₐ[R] Ω) ≃
      (Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.obj
          (artinSchreierEtaleObject p f) where
  toFun := artinSchreierEtaleFiberPoint p f
  invFun := artinSchreierEtaleFiberHom p f
  left_inv g := by
    apply AlgHom.coe_ringHom_injective
    change (Spec.preimage (artinSchreierSchemePoint p f g)).hom = g.toRingHom
    rw [artinSchreierSchemePoint_preimage]
    rfl
  right_inv t := by
    apply Over.OverMorphism.ext
    change Spec.map (Spec.preimage t.left) = t.left
    exact Spec.map_preimage t.left

/-- The inverse equivalence reads the distinguished root from the actual
scheme point's coordinate-ring map. -/
@[simp] theorem artinSchreierHomEquivEtaleFiber_symm_root
    (t : (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.obj
        (artinSchreierEtaleObject p f)) :
    (artinSchreierHomEquivEtaleFiber p f).symm t (artinSchreierRoot p f) =
      (Spec.preimage t.left).hom (artinSchreierRoot p f) := rfl

end GeometricSitePoint

#print axioms artinSchreierScheme
#print axioms artinSchreierSchemeMap
#print axioms artinSchreierSchemeMap_finite
#print axioms artinSchreierSchemeMap_etale
#print axioms artinSchreierCover_faithfullyFlat
#print axioms artinSchreierSchemeMap_surjective
#print axioms artinSchreierEtaleCover
#print axioms artinSchreierEtaleObject
#print axioms artinSchreierEtaleObject_left
#print axioms artinSchreierEtaleObject_hom
#print axioms artinSchreierEtaleToBase
#print axioms artinSchreierEtaleToBase_covering
#print axioms artinSchreierSchemePoint
#print axioms artinSchreierSchemePoint_over
#print axioms artinSchreierSchemePoint_preimage
#print axioms artinSchreierSchemePoint_root
#print axioms artinSchreierEtaleFiberPoint
#print axioms artinSchreierEtaleFiberPoint_left
#print axioms artinSchreierEtaleFiberPoint_root
#print axioms artinSchreierEtaleFiberHom
#print axioms artinSchreierHomEquivEtaleFiber
#print axioms artinSchreierHomEquivEtaleFiber_symm_root

end PrimeGap182.TypeIII
