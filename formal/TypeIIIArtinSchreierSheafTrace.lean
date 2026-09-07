import TypeIIIArtinSchreierCharacterStalk
import TypeIIIArtinSchreierSiteFrobenius

/-!
# Frobenius trace on the actual Artin--Schreier image sheaf

The operator is the actual geometric site-point automorphism evaluated
on the character image sheaf.  It is not defined by a scalar or by a
transport of the root-character representation.  Naturality of the
actual image inclusion and the proved ambient function comparison
identify this operator with the positive Artin--Schreier character
action.  When p is nonzero in E, its trace is ψ(Tr(f)).
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

section GeneralCharacter

variable (p : ℕ) [Fact p.Prime] (K Ω : Type u) [Field K] [Fintype K] [CharP K p]
  [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  [Algebra (ZMod p) K] [Algebra (ZMod p) Ω] [IsScalarTower (ZMod p) K Ω]
  (f : K) (E : Type u) [Field E] (ψ : AddChar (ZMod p) E)

/-- The actual geometric site-fiber permutation, pushed forward on free
generators, acts on functions by arithmetic Frobenius precomposition. -/
theorem artinSchreierSiteFreeEquivFunctions_geometricFrobenius
    (v : (ModuleCat.free E).obj (ArtinSchreierSiteFiber p K Ω f)) :
    artinSchreierSiteFreeEquivFunctions p K Ω f E
        ((ModuleCat.free E).map
          ((smallEtaleGeometricFrobeniusFiberIso K Ω).hom.app
            (artinSchreierEtaleObject p f)) v) =
      fun z => artinSchreierSiteFreeEquivFunctions p K Ω f E v
        (artinSchreierArithmeticFrobenius p K Ω f z) := by
  funext z
  rw [artinSchreierSiteFreeEquivFunctions_apply,
    artinSchreierSiteFreeEquivFunctions_apply]
  let d := ((smallEtaleGeometricFrobeniusFiberIso K Ω).app
    (artinSchreierEtaleObject p f)).toEquiv
  have ha :
      (smallEtaleArithmeticFrobeniusFiberIso K Ω).hom.app
          (artinSchreierEtaleObject p f)
          ((artinSchreierSiteFiberEquivRoots p K Ω f).symm z) =
        (artinSchreierSiteFiberEquivRoots p K Ω f).symm
          (artinSchreierArithmeticFrobenius p K Ω f z) := by
    apply (artinSchreierSiteFiberEquivRoots p K Ω f).injective
    rw [artinSchreierSiteFiberEquivRoots_arithmeticFrobenius,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hi :
      d ((artinSchreierSiteFiberEquivRoots p K Ω f).symm
          (artinSchreierArithmeticFrobenius p K Ω f z)) =
        (artinSchreierSiteFiberEquivRoots p K Ω f).symm z := by
    rw [← ha]
    exact ((smallEtaleArithmeticFrobeniusFiberIso K Ω).app
      (artinSchreierEtaleObject p f)).toEquiv.left_inv _
  have h := Finsupp.mapDomain_apply d.injective v
    ((artinSchreierSiteFiberEquivRoots p K Ω f).symm
      (artinSchreierArithmeticFrobenius p K Ω f z))
  rw [hi] at h
  exact h

/-- The actual point-induced geometric Frobenius on the ambient sheaf
stalk is arithmetic Frobenius precomposition on actual root functions. -/
theorem artinSchreierAmbientStalkEquivFunctions_geometricFrobenius
    (v : ArtinSchreierAmbientStalk p K Ω f E) :
    artinSchreierAmbientStalkEquivFunctions p K Ω f E
        (((smallEtaleGeometricFrobeniusModuleStalkIso K Ω E).hom.app
          (artinSchreierFreeSheaf p f E)) v) =
      fun z => artinSchreierAmbientStalkEquivFunctions p K Ω f E v
        (artinSchreierArithmeticFrobenius p K Ω f z) := by
  let Φ := smallEtaleGeometricPoint K Ω
  have h := congrArg (fun g => g v)
    (artinSchreierFreeSheaf_stalk_fieldAutomorphism p f E
      (smallEtaleArithmeticFrobenius K Ω).symm)
  change artinSchreierSiteFreeEquivFunctions p K Ω f E
      ((artinSchreierFreeSheaf_stalkIso p f E Φ).hom
        (((smallEtaleGeometricFrobeniusModuleStalkIso K Ω E).hom.app
          (artinSchreierFreeSheaf p f E)) v)) = _
  change (artinSchreierFreeSheaf_stalkIso p f E Φ).hom
      (((smallEtaleGeometricFrobeniusModuleStalkIso K Ω E).hom.app
        (artinSchreierFreeSheaf p f E)) v) = _ at h
  rw [h]
  exact artinSchreierSiteFreeEquivFunctions_geometricFrobenius p K Ω f E _

/-- Geometric Frobenius on the actual character-image stalk, defined
by the genuine site-stalk natural automorphism at that sheaf. -/
def artinSchreierSheafGeometricFrobenius :
    ArtinSchreierCharacterStalk p K Ω f E ψ →ₗ[E]
      ArtinSchreierCharacterStalk p K Ω f E ψ :=
  ((smallEtaleGeometricFrobeniusModuleStalkIso K Ω E).hom.app
    (artinSchreierCharacterImageSheaf p f E ψ)).hom

omit [CharP Ω p] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] in
/-- Naturality of the actual site-stalk automorphism makes the
image-sheaf inclusion Frobenius-equivariant. -/
theorem artinSchreierSheafGeometricFrobenius_inclusion
    (v : ArtinSchreierCharacterStalk p K Ω f E ψ) :
    artinSchreierCharacterStalkInclusion p K Ω f E ψ
        (artinSchreierSheafGeometricFrobenius p K Ω f E ψ v) =
      ((smallEtaleGeometricFrobeniusModuleStalkIso K Ω E).hom.app
        (artinSchreierFreeSheaf p f E))
          (artinSchreierCharacterStalkInclusion p K Ω f E ψ v) := by
  have h := (smallEtaleGeometricFrobeniusModuleStalkIso K Ω E).hom.naturality
    (Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ))
  exact (congrArg (fun g => g v) h).symm

/-- The actual image-stalk Frobenius agrees with the root-character
action under the proved stalk equivalence. -/
theorem artinSchreierCharacterStalkEquiv_geometricFrobenius
    (hpE : (p : E) ≠ 0) (v : ArtinSchreierCharacterStalk p K Ω f E ψ) :
    artinSchreierCharacterStalkEquiv p K Ω f E ψ hpE
        (artinSchreierSheafGeometricFrobenius p K Ω f E ψ v) =
      artinSchreierCharacterFrobenius p K Ω f E ψ
        (artinSchreierCharacterStalkEquiv p K Ω f E ψ hpE v) := by
  apply Subtype.ext
  funext z
  rw [artinSchreierCharacterFrobenius_apply, artinSchreierCharacterStalkEquiv_val,
    artinSchreierSheafGeometricFrobenius_inclusion,
    artinSchreierCharacterStalkEquiv_val]
  exact congrFun (artinSchreierAmbientStalkEquivFunctions_geometricFrobenius
    p K Ω f E (artinSchreierCharacterStalkInclusion p K Ω f E ψ v)) z

/-- The independently defined geometric stalk operator acts by the
positive character of the field trace. -/
theorem artinSchreierSheafGeometricFrobenius_eq_smul (hpE : (p : E) ≠ 0) :
    artinSchreierSheafGeometricFrobenius p K Ω f E ψ =
      ψ (Algebra.trace (ZMod p) K f) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply (artinSchreierCharacterStalkEquiv p K Ω f E ψ hpE).injective
  rw [artinSchreierCharacterStalkEquiv_geometricFrobenius,
    artinSchreierCharacterFrobenius_eq_smul]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- The actual geometric Frobenius trace on the image-sheaf stalk is
ψ(Tr(f)).  All stalk, point-action, and root-existence comparisons have
been proved; invertibility of p is the coefficient hypothesis. -/
theorem artinSchreierSheafGeometricFrobenius_trace (hpE : (p : E) ≠ 0) :
    LinearMap.trace E (ArtinSchreierCharacterStalk p K Ω f E ψ)
        (artinSchreierSheafGeometricFrobenius p K Ω f E ψ) =
      ψ (Algebra.trace (ZMod p) K f) := by
  let := artinSchreierCharacterStalk_finiteDimensional p K Ω f E ψ hpE
  rw [artinSchreierSheafGeometricFrobenius_eq_smul p K Ω f E ψ hpE,
    map_smul, LinearMap.trace_id, artinSchreierCharacterStalk_finrank p K Ω f E ψ hpE]
  simp

end GeneralCharacter

section StandardCharacter

variable (p : ℕ) [Fact p.Prime] (K Ω : Type) [Field K] [Fintype K] [CharP K p]
  [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  [Algebra (ZMod p) K] [Algebra (ZMod p) Ω] [IsScalarTower (ZMod p) K Ω] (f : K)

/-- For the standard complex character, the actual sheaf-stalk trace
is precisely the trace character used in the finite Type III sums. -/
theorem artinSchreierSheafGeometricFrobenius_standard_trace :
    LinearMap.trace ℂ (ArtinSchreierCharacterStalk p K Ω f ℂ ZMod.stdAddChar)
        (artinSchreierSheafGeometricFrobenius p K Ω f ℂ ZMod.stdAddChar) =
      FiniteFieldSums.traceAddChar p K f := by
  have hpℂ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  exact artinSchreierSheafGeometricFrobenius_trace p K Ω f ℂ ZMod.stdAddChar hpℂ

end StandardCharacter

/-- Over the prime field the actual sheaf-stalk trace is exactly the
standard additive phase appearing in the original Type III sums. -/
theorem artinSchreierSheafGeometricFrobenius_prime_trace
    (p : ℕ) [Fact p.Prime] (f : ZMod p) :
    LinearMap.trace ℂ
        (ArtinSchreierCharacterStalk p (ZMod p) (AlgebraicClosure (ZMod p)) f ℂ ZMod.stdAddChar)
        (artinSchreierSheafGeometricFrobenius p (ZMod p) (AlgebraicClosure (ZMod p)) f ℂ
          ZMod.stdAddChar) = ZMod.stdAddChar f := by
  simpa only [FiniteFieldSums.traceAddChar_prime] using
    artinSchreierSheafGeometricFrobenius_standard_trace p (ZMod p)
      (AlgebraicClosure (ZMod p)) f

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius_inclusion
#print axioms PrimeGap182.TypeIII.artinSchreierSiteFreeEquivFunctions_geometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierAmbientStalkEquivFunctions_geometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalkEquiv_geometricFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius_eq_smul
#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius_trace
#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius_standard_trace
#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius_prime_trace
