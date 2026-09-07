import TypeIIIArtinSchreierPointStalk
import TypeIIIArtinSchreierPointFrobenius
import TypeIIIFiniteFieldCovariance

/-!
# The character-sheaf trace at a finite-field point

The sheaf is constructed over Spec R. At a compatible point R → K → Ω,
where K is finite and (p:E)≠0, geometric Frobenius on its actual image-sheaf
stalk has trace ψ(Tr(f(K))). The operator comes from the point automorphism
over R; it is not defined by transporting a scalar action from Spec K.

This supplies the additive-character trace function on an arbitrary
affine base. It does not construct compact cohomology or a Kloosterman
sheaf.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

section GeneralCharacter

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Fintype K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra.IsAlgebraic K Ω] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] (f : R)

section RingAmbient

variable (E : Type u) [CommRing E]

/-- The actual point-induced action on the original ambient stalk is
arithmetic Frobenius precomposition on the specialized root functions. -/
theorem artinSchreierPointAmbientStalkEquivFunctions_geometricFrobenius
    (v : ArtinSchreierPointAmbientStalk p R Ω f E) :
    artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E
        (((smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.app
          (artinSchreierFreeSheaf p f E)) v) =
      fun z => artinSchreierPointAmbientStalkEquivFunctions p R K Ω f E v
        (artinSchreierArithmeticFrobenius p K Ω (algebraMap R K f) z) := by
  let Φ := smallEtaleGeometricPoint R Ω
  have h := congrArg (fun g => g v)
    (artinSchreierFreeSheaf_stalk_fieldAutomorphism p f E
      (smallEtalePointArithmeticFrobenius R K Ω).symm)
  change artinSchreierPointFreeEquivFunctions p R K Ω f E
      ((artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        (((smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.app
          (artinSchreierFreeSheaf p f E)) v)) = _
  change (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
      (((smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.app
        (artinSchreierFreeSheaf p f E)) v) = _ at h
  rw [h]
  exact artinSchreierPointFreeEquivFunctions_geometricFrobenius p R K Ω f E _

end RingAmbient

variable (E : Type u) [Field E] (ψ : AddChar (ZMod p) E)

/-- Geometric Frobenius on the original character-image stalk is the
actual site-stalk automorphism evaluated at that sheaf. -/
def artinSchreierPointSheafGeometricFrobenius :
    ArtinSchreierPointCharacterStalk p R Ω f E ψ →ₗ[E]
      ArtinSchreierPointCharacterStalk p R Ω f E ψ :=
  ((smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.app
    (artinSchreierCharacterImageSheaf p f E ψ)).hom

omit [CharP Ω p] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] in
/-- The actual image inclusion is equivariant by naturality of the
point-induced stalk automorphism. -/
theorem artinSchreierPointSheafGeometricFrobenius_inclusion
    (v : ArtinSchreierPointCharacterStalk p R Ω f E ψ) :
    artinSchreierPointCharacterStalkInclusion p R Ω f E ψ
        (artinSchreierPointSheafGeometricFrobenius p R K Ω f E ψ v) =
      ((smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.app
        (artinSchreierFreeSheaf p f E))
          (artinSchreierPointCharacterStalkInclusion p R Ω f E ψ v) := by
  have h := (smallEtalePointGeometricFrobeniusModuleStalkIso R K Ω E).hom.naturality
    (Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ))
  exact (congrArg (fun g => g v) h).symm

/-- The independently defined geometric action agrees with the root
character action under the actual stalk comparison over Spec R. -/
theorem artinSchreierPointCharacterStalkEquiv_geometricFrobenius
    (hpE : (p : E) ≠ 0) (v : ArtinSchreierPointCharacterStalk p R Ω f E ψ) :
    artinSchreierPointCharacterStalkEquiv p R K Ω f E ψ hpE
        (artinSchreierPointSheafGeometricFrobenius p R K Ω f E ψ v) =
      artinSchreierCharacterFrobenius p K Ω (algebraMap R K f) E ψ
        (artinSchreierPointCharacterStalkEquiv p R K Ω f E ψ hpE v) := by
  apply Subtype.ext
  funext z
  rw [artinSchreierCharacterFrobenius_apply, artinSchreierPointCharacterStalkEquiv_val,
    artinSchreierPointSheafGeometricFrobenius_inclusion,
    artinSchreierPointCharacterStalkEquiv_val]
  exact congrFun (artinSchreierPointAmbientStalkEquivFunctions_geometricFrobenius
    p R K Ω f E (artinSchreierPointCharacterStalkInclusion p R Ω f E ψ v)) z

/-- Geometric Frobenius on the actual original-base stalk acts by the
positive character of the field trace of the evaluated parameter. -/
theorem artinSchreierPointSheafGeometricFrobenius_eq_smul (hpE : (p : E) ≠ 0) :
    artinSchreierPointSheafGeometricFrobenius p R K Ω f E ψ =
      ψ (Algebra.trace (ZMod p) K (algebraMap R K f)) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply (artinSchreierPointCharacterStalkEquiv p R K Ω f E ψ hpE).injective
  rw [artinSchreierPointCharacterStalkEquiv_geometricFrobenius,
    artinSchreierCharacterFrobenius_eq_smul]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- The trace on the actual sheaf stalk at R → K is ψ(Tr(f(K))).
There are no supplied stalk, root, rank, or action-comparison premises. -/
theorem artinSchreierPointSheafGeometricFrobenius_trace (hpE : (p : E) ≠ 0) :
    LinearMap.trace E (ArtinSchreierPointCharacterStalk p R Ω f E ψ)
        (artinSchreierPointSheafGeometricFrobenius p R K Ω f E ψ) =
      ψ (Algebra.trace (ZMod p) K (algebraMap R K f)) := by
  let := artinSchreierPointCharacterStalk_finiteDimensional p R K Ω f E ψ hpE
  rw [artinSchreierPointSheafGeometricFrobenius_eq_smul p R K Ω f E ψ hpE,
    map_smul, LinearMap.trace_id,
    artinSchreierPointCharacterStalk_finrank p R K Ω f E ψ hpE]
  simp

end GeneralCharacter

section StandardCharacter

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type) [CommRing R] [CharP R p]
  [Field K] [Fintype K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra.IsAlgebraic K Ω] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] (f : R)

/-- The standard complex-character trace is the additive trace character
of the actual value of f at the finite-field point. -/
theorem artinSchreierPointSheafGeometricFrobenius_standard_trace :
    LinearMap.trace ℂ (ArtinSchreierPointCharacterStalk p R Ω f ℂ ZMod.stdAddChar)
        (artinSchreierPointSheafGeometricFrobenius p R K Ω f ℂ ZMod.stdAddChar) =
      FiniteFieldSums.traceAddChar p K (algebraMap R K f) := by
  have hpℂ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  exact artinSchreierPointSheafGeometricFrobenius_trace p R K Ω f ℂ ZMod.stdAddChar hpℂ

end StandardCharacter

/-- At a prime-field-valued point, the trace of the sheaf on the original
affine base is the original standard additive phase at f(point). -/
theorem artinSchreierPointSheafGeometricFrobenius_prime_trace
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    [Algebra R (ZMod p)] (f : R) :
    LinearMap.trace ℂ
        (ArtinSchreierPointCharacterStalk p R (AlgebraicClosure (ZMod p)) f ℂ ZMod.stdAddChar)
        (artinSchreierPointSheafGeometricFrobenius p R (ZMod p)
          (AlgebraicClosure (ZMod p)) f ℂ ZMod.stdAddChar) =
      ZMod.stdAddChar (algebraMap R (ZMod p) f) := by
  simpa only [FiniteFieldSums.traceAddChar_prime] using
    artinSchreierPointSheafGeometricFrobenius_standard_trace p R (ZMod p)
      (AlgebraicClosure (ZMod p)) f

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierPointAmbientStalkEquivFunctions_geometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius_inclusion
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalkEquiv_geometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius_eq_smul
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius_trace
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius_standard_trace
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius_prime_trace
