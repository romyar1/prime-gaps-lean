import TypeIIIArtinSchreierPointFiber
import TypeIIIArtinSchreierSiteFrobenius

/-!
# Frobenius at a finite-field point of an arbitrary affine base

For a compatible point R → K → Ω with K finite, the q-power automorphism
of Ω fixes R. Its spectrum therefore acts on the actual geometric point
of Spec R. The original Artin--Schreier cover fiber sees precisely the
q-power permutation of the roots with parameter f(K).

Geometric Frobenius is the inverse field automorphism. On the free module
of the actual site fiber it becomes precomposition by arithmetic Frobenius
on root functions. No replacement of the original base scheme is made.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry
open scoped Classical

section ActualPoint

variable (p : ℕ) [Fact p.Prime] (R Ω : Type u) [CommRing R] [CharP R p]
  [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (f : R)

/-- A field automorphism fixing R acts on points of the original cover
by composition of their actual algebra homomorphisms. -/
theorem smallEtaleFieldFiberIso_artinSchreierPointOver (σ : Ω ≃ₐ[R] Ω)
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (smallEtaleFieldFiberIso R Ω σ).hom.app (artinSchreierEtaleObject p f)
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

/-- The original quotient-homomorphism coordinate intertwines the
actual site automorphism and the coefficient-field automorphism. -/
theorem smallEtaleFieldFiberIso_artinSchreierHomOver (σ : Ω ≃ₐ[R] Ω)
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    (artinSchreierHomEquivEtaleFiber p f).symm
        ((smallEtaleFieldFiberIso R Ω σ).hom.app (artinSchreierEtaleObject p f) t) =
      σ.toAlgHom.comp ((artinSchreierHomEquivEtaleFiber p f).symm t) := by
  obtain ⟨g, rfl⟩ := (artinSchreierHomEquivEtaleFiber p f).surjective t
  change (artinSchreierHomEquivEtaleFiber p f).symm
      ((smallEtaleFieldFiberIso R Ω σ).hom.app (artinSchreierEtaleObject p f)
        (artinSchreierEtaleFiberPoint p f g)) = _
  rw [smallEtaleFieldFiberIso_artinSchreierPointOver]
  change (artinSchreierHomEquivEtaleFiber p f).symm
      ((artinSchreierHomEquivEtaleFiber p f) (σ.toAlgHom.comp g)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable (K : Type u) [Field K] [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω]

/-- Reading the specialized root after the site action gives the
actual field automorphism applied to the original root coordinate. -/
theorem artinSchreierPointSiteEquivRoots_fieldAutomorphism_val (σ : Ω ≃ₐ[R] Ω)
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    (artinSchreierPointSiteEquivRoots p R Ω f K
        ((smallEtaleFieldFiberIso R Ω σ).hom.app (artinSchreierEtaleObject p f) t) : Ω) =
      σ (artinSchreierPointSiteEquivRoots p R Ω f K t : Ω) := by
  change (artinSchreierPointHomEquivFiber p R K Ω f
      ((artinSchreierHomEquivEtaleFiber p f).symm
        ((smallEtaleFieldFiberIso R Ω σ).hom.app (artinSchreierEtaleObject p f) t)) : Ω) = _
  rw [smallEtaleFieldFiberIso_artinSchreierHomOver]
  rfl

end ActualPoint

section FinitePoint

variable (R K Ω : Type u) [CommRing R] [Field K] [Fintype K] [Field Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra.IsAlgebraic K Ω]

/-- Arithmetic Frobenius of the finite point field, viewed as an
automorphism fixing the original affine coordinate ring. -/
def smallEtalePointArithmeticFrobenius : Ω ≃ₐ[R] Ω :=
  (smallEtaleArithmeticFrobenius K Ω).restrictScalars R

/-- The restricted automorphism is still the literal q-power map. -/
@[simp] theorem smallEtalePointArithmeticFrobenius_apply (x : Ω) :
    smallEtalePointArithmeticFrobenius R K Ω x = x ^ Fintype.card K := rfl

variable [IsSepClosed Ω]

/-- Arithmetic Frobenius acts on the actual fiber functor over Spec R. -/
def smallEtalePointArithmeticFrobeniusFiberIso :
    (smallEtaleGeometricPoint R Ω).fiber ≅ (smallEtaleGeometricPoint R Ω).fiber :=
  smallEtaleFieldFiberIso R Ω (smallEtalePointArithmeticFrobenius R K Ω)

/-- Geometric Frobenius uses the inverse field map over the same base. -/
def smallEtalePointGeometricFrobeniusFiberIso :
    (smallEtaleGeometricPoint R Ω).fiber ≅ (smallEtaleGeometricPoint R Ω).fiber :=
  smallEtaleFieldFiberIso R Ω (smallEtalePointArithmeticFrobenius R K Ω).symm

variable (E : Type u) [CommRing E]

/-- The inverse point automorphism acts on the actual stalk functor
for sheaves over Spec R. -/
def smallEtalePointGeometricFrobeniusModuleStalkIso :
    (smallEtaleGeometricPoint R Ω).sheafFiber (A := ModuleCat.{u} E) ≅
      (smallEtaleGeometricPoint R Ω).sheafFiber (A := ModuleCat.{u} E) :=
  smallEtaleFieldSheafFiberIso R Ω (ModuleCat.{u} E)
    (smallEtalePointArithmeticFrobenius R K Ω).symm

variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP Ω p]
  [Algebra (ZMod p) K] [Algebra (ZMod p) Ω] [IsScalarTower (ZMod p) K Ω] (f : R)

/-- The actual arithmetic action on the original cover fiber is the
root Frobenius with parameter equal to the value of f at the point. -/
theorem artinSchreierPointSiteEquivRoots_arithmeticFrobenius
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    artinSchreierPointSiteEquivRoots p R Ω f K
        ((smallEtalePointArithmeticFrobeniusFiberIso R K Ω).hom.app
          (artinSchreierEtaleObject p f) t) =
      artinSchreierArithmeticFrobenius p K Ω (algebraMap R K f)
        (artinSchreierPointSiteEquivRoots p R Ω f K t) := by
  apply Subtype.ext
  change (artinSchreierPointSiteEquivRoots p R Ω f K
      ((smallEtaleFieldFiberIso R Ω (smallEtalePointArithmeticFrobenius R K Ω)).hom.app
        (artinSchreierEtaleObject p f) t) : Ω) = _
  rw [artinSchreierPointSiteEquivRoots_fieldAutomorphism_val,
    smallEtalePointArithmeticFrobenius_apply, artinSchreierArithmeticFrobenius_val]

end FinitePoint

section FreeFunctions

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Fintype K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra.IsAlgebraic K Ω] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] (f : R) (E : Type u) [CommRing E]

/-- Pushing free generators by the actual geometric point permutation
is precomposition by arithmetic Frobenius on the specialized root fiber. -/
theorem artinSchreierPointFreeEquivFunctions_geometricFrobenius
    (v : (ModuleCat.free E).obj (ArtinSchreierPointSiteFiber p R Ω f)) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        ((ModuleCat.free E).map
          ((smallEtalePointGeometricFrobeniusFiberIso R K Ω).hom.app
            (artinSchreierEtaleObject p f)) v) =
      fun z => artinSchreierPointFreeEquivFunctions p R K Ω f E v
        (artinSchreierArithmeticFrobenius p K Ω (algebraMap R K f) z) := by
  funext z
  rw [artinSchreierPointFreeEquivFunctions_apply,
    artinSchreierPointFreeEquivFunctions_apply]
  let d := ((smallEtalePointGeometricFrobeniusFiberIso R K Ω).app
    (artinSchreierEtaleObject p f)).toEquiv
  have ha :
      (smallEtalePointArithmeticFrobeniusFiberIso R K Ω).hom.app
          (artinSchreierEtaleObject p f)
          ((artinSchreierPointSiteEquivRoots p R Ω f K).symm z) =
        (artinSchreierPointSiteEquivRoots p R Ω f K).symm
          (artinSchreierArithmeticFrobenius p K Ω (algebraMap R K f) z) := by
    apply (artinSchreierPointSiteEquivRoots p R Ω f K).injective
    rw [artinSchreierPointSiteEquivRoots_arithmeticFrobenius,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hi :
      d ((artinSchreierPointSiteEquivRoots p R Ω f K).symm
          (artinSchreierArithmeticFrobenius p K Ω (algebraMap R K f) z)) =
        (artinSchreierPointSiteEquivRoots p R Ω f K).symm z := by
    rw [← ha]
    exact ((smallEtalePointArithmeticFrobeniusFiberIso R K Ω).app
      (artinSchreierEtaleObject p f)).toEquiv.left_inv _
  have h := Finsupp.mapDomain_apply d.injective v
    ((artinSchreierPointSiteEquivRoots p R Ω f K).symm
      (artinSchreierArithmeticFrobenius p K Ω (algebraMap R K f) z))
  rw [hi] at h
  exact h

end FreeFunctions

#print axioms smallEtaleFieldFiberIso_artinSchreierPointOver
#print axioms smallEtaleFieldFiberIso_artinSchreierHomOver
#print axioms artinSchreierPointSiteEquivRoots_fieldAutomorphism_val
#print axioms smallEtalePointArithmeticFrobenius
#print axioms smallEtalePointArithmeticFrobenius_apply
#print axioms smallEtalePointArithmeticFrobeniusFiberIso
#print axioms smallEtalePointGeometricFrobeniusFiberIso
#print axioms smallEtalePointGeometricFrobeniusModuleStalkIso
#print axioms artinSchreierPointSiteEquivRoots_arithmeticFrobenius
#print axioms artinSchreierPointFreeEquivFunctions_geometricFrobenius

end PrimeGap182.TypeIII
