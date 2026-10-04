import TypeIIILinearRadialPhaseFromPoleTransport

/-!
# Canonical coefficient maps on the actual full affine presentations

The prime-field QST plane and the algebraically closed coefficient plane
are different schemes. Their comparison map is fixed by the coefficient
algebraMap, and it commutes with the actual full-affine linear form.
These coordinate statements provide maps for a shared ordinary system;
they do not identify its adic/perverse realizations or supply base change.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PrimeGap182.TypeIII.CanonicalAffineCoefficientChange

variable (K0 k : Type) [Field K0] [Field k] [Algebra K0 k]

abbrev affine (n : ℕ) : Scheme := Spec (.of (MvPolynomial (Fin n) k))

def coefficientHom (n : ℕ) : MvPolynomial (Fin n) K0 →+* MvPolynomial (Fin n) k :=
  MvPolynomial.map (algebraMap K0 k)

def coefficientMorphism (n : ℕ) : affine k n ⟶ affine K0 n :=
  Spec.map (CommRingCat.ofHom (coefficientHom K0 k n))

theorem lineMorphism : coefficientMorphism K0 k 1 =
    LinearRadialPhaseFromPoleTransport.baseLineMorphism K0 k := rfl

theorem linearHom_square (a b : K0) :
    (coefficientHom K0 k 2).comp
        (LinearRadialPhaseFromPoleTransport.linearHom a b).toRingHom =
      (LinearRadialPhaseFromPoleTransport.linearHom
        (algebraMap K0 k a) (algebraMap K0 k b)).toRingHom.comp
          (coefficientHom K0 k 1) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [coefficientHom, LinearRadialPhaseFromPoleTransport.linearHom]
  · intro i
    simp [coefficientHom, LinearRadialPhaseFromPoleTransport.linearHom]

theorem linearMorphism_square (a b : K0) :
    coefficientMorphism K0 k 2 ≫
        LinearRadialPhaseFromPoleTransport.linearMorphism a b =
      LinearRadialPhaseFromPoleTransport.linearMorphism
        (algebraMap K0 k a) (algebraMap K0 k b) ≫ coefficientMorphism K0 k 1 := by
  dsimp only [coefficientMorphism, LinearRadialPhaseFromPoleTransport.linearMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (linearHom_square K0 k a b)

def planeMorphism : FullFourierKernelCoordinates.planeScheme k ⟶
    FullFourierKernelCoordinates.planeScheme K0 := coefficientMorphism K0 k 2

end PrimeGap182.TypeIII.CanonicalAffineCoefficientChange

#print axioms PrimeGap182.TypeIII.CanonicalAffineCoefficientChange.linearMorphism_square
