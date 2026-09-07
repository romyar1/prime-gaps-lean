import TypeIIIArtinSchreierRingStalk
import TypeIIIArtinSchreierPointTrace

/-!
# The actual Artin--Schreier sheaf trace with ring coefficients

Let R be an affine coordinate ring of characteristic p and R → K a
finite-field point.  Over a commutative coefficient ring E in which p
is invertible, geometric Frobenius on the actual character-image sheaf
stalk has trace ψ(Tr(f(K))).  Its endomorphism is defined by evaluating
the actual geometric site-point automorphism at that sheaf.

The comparison with root functions follows from naturality of the
actual image inclusion.  Freeness and finite generation are supplied
by the proved stalk equivalence before applying the linear trace
formula.  No scalar-action, stalk-comparison, rank, or root-existence
premise is assumed, and no default-zero trace case is used.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Fintype K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra.IsAlgebraic K Ω] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] (f : R)
  (E : Type u) [CommRing E] [Invertible (p : E)] (ψ : AddChar (ZMod p) E)

/-- Geometric Frobenius on the actual original-base ring image stalk.
The definition uses the site-stalk automorphism, not a scalar model. -/
def artinSchreierRingPointSheafGeometricFrobenius :
    ArtinSchreierRingPointCharacterStalk p R Ω f E ψ →ₗ[E]
      ArtinSchreierRingPointCharacterStalk p R Ω f E ψ :=
  ((smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.app
    (artinSchreierRingCharacterImageSheaf p f E ψ)).hom

omit [CharP Ω p] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] in
/-- Naturality of the genuine point automorphism makes the actual
image-sheaf inclusion equivariant. -/
theorem artinSchreierRingPointSheafGeometricFrobenius_inclusion
    (v : ArtinSchreierRingPointCharacterStalk p R Ω f E ψ) :
    artinSchreierRingPointCharacterStalkInclusion p R Ω f E ψ
        (artinSchreierRingPointSheafGeometricFrobenius p R K Ω f E ψ v) =
      ((smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.app
        (artinSchreierFreeSheaf p f E))
          (artinSchreierRingPointCharacterStalkInclusion p R Ω f E ψ v) := by
  have h := (smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.naturality
    (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ))
  exact (congrArg (fun g => g v) h).symm

/-- The actual ring image-stalk equivalence intertwines geometric
Frobenius with arithmetic Frobenius precomposition on root functions. -/
theorem artinSchreierRingPointCharacterStalkEquiv_geometricFrobenius
    (v : ArtinSchreierRingPointCharacterStalk p R Ω f E ψ) :
    artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ
        (artinSchreierRingPointSheafGeometricFrobenius p R K Ω f E ψ v) =
      artinSchreierCharacterFrobenius p K Ω (algebraMap R K f) E ψ
        (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ v) := by
  apply Subtype.ext
  funext z
  rw [artinSchreierCharacterFrobenius_apply, artinSchreierRingPointCharacterStalkEquiv_val,
    artinSchreierRingPointSheafGeometricFrobenius_inclusion,
    artinSchreierRingPointCharacterStalkEquiv_val]
  exact congrFun (artinSchreierPointAmbientStalkEquivFunctions_geometricFrobenius
    p R K Ω f E (artinSchreierRingPointCharacterStalkInclusion p R Ω f E ψ v)) z

/-- On the actual original-base stalk, geometric Frobenius is scalar
multiplication by the positive character of the evaluated field trace. -/
theorem artinSchreierRingPointSheafGeometricFrobenius_eq_smul :
    artinSchreierRingPointSheafGeometricFrobenius p R K Ω f E ψ =
      ψ (Algebra.trace (ZMod p) K (algebraMap R K f)) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply (artinSchreierRingPointCharacterStalkEquiv p R K Ω f E ψ).injective
  rw [artinSchreierRingPointCharacterStalkEquiv_geometricFrobenius,
    artinSchreierCharacterFrobenius_eq_smul]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- The actual geometric Frobenius trace at R → K over p-unit ring
coefficients.  The stalk is proved finite free before taking its trace. -/
theorem artinSchreierRingPointSheafGeometricFrobenius_trace :
    LinearMap.trace E (ArtinSchreierRingPointCharacterStalk p R Ω f E ψ)
        (artinSchreierRingPointSheafGeometricFrobenius p R K Ω f E ψ) =
      ψ (Algebra.trace (ZMod p) K (algebraMap R K f)) := by
  let := artinSchreierRingPointCharacterStalk_free p R K Ω f E ψ
  let := artinSchreierRingPointCharacterStalk_finite p R K Ω f E ψ
  rw [artinSchreierRingPointSheafGeometricFrobenius_eq_smul p R K Ω f E ψ,
    map_smul, LinearMap.trace_id,
    artinSchreierRingPointCharacterStalk_finrank p R K Ω f E ψ]
  simp

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierRingPointSheafGeometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointSheafGeometricFrobenius_inclusion
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointCharacterStalkEquiv_geometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointSheafGeometricFrobenius_eq_smul
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointSheafGeometricFrobenius_trace
