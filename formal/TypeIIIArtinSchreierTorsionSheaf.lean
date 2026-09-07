import TypeIIIArtinSchreierRingLocalTriviality
import TypeIIIArtinSchreierRingTrace
import TypeIIITorsionCoefficients

/-!
# Actual Artin--Schreier sheaves at finite torsion coefficient levels

At level n use the actual finite cyclotomic quotient Λ_n over
Z/(ℓ^(n+1)), with its constructed primitive p-th root character.
The proved unit p in Λ_n defines the existing character image sheaf.
It is locally free of rank one on the actual Artin--Schreier cover,
and its actual point-induced Frobenius trace is the additive phase.

The point traces are compatible with the proved coefficient reductions.
This module makes no cohomology, purity, or uniform-cancellation claim.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The actual character image sheaf with the constructed finite
torsion coefficients and their primitive additive character. -/
def torsionArtinSchreierSheaf (n : ℕ) {R : Type} [CommRing R] [CharP R p] (f : R) :
    Sheaf (Spec (.of R)).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientRing p ell n)) :=
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  artinSchreierRingCharacterImageSheaf p f (TorsionCoefficientRing p ell n)
    (torsionCoefficientChar p ell n)

/-- Every finite coefficient level becomes the actual constant
rank-one module sheaf on the same Artin--Schreier covering object. -/
def torsionArtinSchreierLocalTrivialization
    (n : ℕ) {R : Type} [CommRing R] [CharP R p] (f : R) :
    (torsionArtinSchreierSheaf p ell hne n f).over (artinSchreierEtaleObject p f) ≅
      (constantSheaf ((Spec (.of R)).smallEtaleTopology.over
        (artinSchreierEtaleObject p f))
        (ModuleCat.{0} (TorsionCoefficientRing p ell n))).obj
          (ModuleCat.of (TorsionCoefficientRing p ell n) (TorsionCoefficientRing p ell n)) := by
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  exact artinSchreierRingCharacterLocalTrivialization p f
    (TorsionCoefficientRing p ell n) (torsionCoefficientChar p ell n)

/-- The local constancy witness is the actual sheaf isomorphism
on the proved covering object, at every finite torsion level. -/
theorem torsionArtinSchreierSheaf_over_isConstant
    (n : ℕ) {R : Type} [CommRing R] [CharP R p] (f : R) :
    Sheaf.IsConstant
      ((Spec (.of R)).smallEtaleTopology.over (artinSchreierEtaleObject p f))
      ((torsionArtinSchreierSheaf p ell hne n f).over (artinSchreierEtaleObject p f)) :=
  Sheaf.isConstant_of_iso _ (torsionArtinSchreierLocalTrivialization p ell hne n f)

section FinitePoint

variable (R K Ω : Type) [CommRing R] [CharP R p]
  [Field K] [Fintype K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [Algebra.IsAlgebraic K Ω] [Algebra (ZMod p) K] [Algebra (ZMod p) Ω]
  [IsScalarTower (ZMod p) K Ω] (f : R)

/-- The trace of the actual geometric Frobenius on the stalk of
the finite-coefficient sheaf at the original affine-base point. -/
def torsionArtinSchreierTrace (n : ℕ) : TorsionCoefficientRing p ell n :=
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  LinearMap.trace (TorsionCoefficientRing p ell n)
    (ArtinSchreierRingPointCharacterStalk p R Ω f (TorsionCoefficientRing p ell n)
      (torsionCoefficientChar p ell n))
    (artinSchreierRingPointSheafGeometricFrobenius p R K Ω f
      (TorsionCoefficientRing p ell n) (torsionCoefficientChar p ell n))

/-- The actual stalk trace is the constructed primitive character
of the field trace of the phase evaluated at the point. -/
theorem torsionArtinSchreierTrace_eq (n : ℕ) :
    torsionArtinSchreierTrace p ell hne R K Ω f n =
      torsionCoefficientChar p ell n (Algebra.trace (ZMod p) K (algebraMap R K f)) := by
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  exact artinSchreierRingPointSheafGeometricFrobenius_trace p R K Ω f
    (TorsionCoefficientRing p ell n) (torsionCoefficientChar p ell n)

/-- Reducing the actual point trace agrees with the actual point
trace of the sheaf at the lower coefficient level. -/
theorem torsionArtinSchreierTrace_reduce {m n : ℕ} (hmn : m ≤ n) :
    torsionCoefficientReduce p ell hmn (torsionArtinSchreierTrace p ell hne R K Ω f n) =
      torsionArtinSchreierTrace p ell hne R K Ω f m := by
  rw [torsionArtinSchreierTrace_eq, torsionArtinSchreierTrace_eq]
  exact torsionCoefficientReduce_char p ell hmn _

end FinitePoint

#print axioms torsionArtinSchreierSheaf
#print axioms torsionArtinSchreierLocalTrivialization
#print axioms torsionArtinSchreierSheaf_over_isConstant
#print axioms torsionArtinSchreierTrace
#print axioms torsionArtinSchreierTrace_eq
#print axioms torsionArtinSchreierTrace_reduce

end PrimeGap182.TypeIII
