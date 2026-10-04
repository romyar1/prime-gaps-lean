import TypeIIITorusOpenFromLaurentLocalization
import TypeIIIFourierOriginFromASKernel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
Both actual coordinate projections of the full Fourier affine plane are
smooth. The source projection is a polynomial affine-line projection
transported through the existing exact polynomial coordinate equivalences;
the target projection is obtained by the actual coordinate swap. No sheaf,
Fourier-comparison, chosen smoothness certificate, or MODEL premise occurs.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace PrimeGap182.TypeIII.FullFourierSourceProjectionSmoothFromPolynomialCoordinates
open TorusOpenFromLaurentLocalization

variable (E : Type) [Field E]

/-- Exact source ring map as a polynomial projection between coordinate isomorphisms. -/
theorem sourceHom_factor :
    (MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 2)) :
      MvPolynomial (Fin 1) E →ₐ[E] MvPolynomial (Fin 2) E).toRingHom =
    (doublePolynomialEquiv E).symm.toRingHom.comp
      ((Polynomial.C : Polynomial E →+* Polynomial (Polynomial E)).comp
        (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    apply (doublePolynomialEquiv E).injective
    simp
    exact (doublePolynomialEquiv E).commutes c
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    apply (doublePolynomialEquiv E).injective
    simp [doublePolynomialEquiv_X_zero, MvPolynomial.uniqueAlgEquiv_apply]

/-- The actual first full-plane projection is smooth over every field. -/
instance sourceMorphism_smooth : Smooth (FourierOriginFromASKernel.sourceMorphism E) := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 2)) :
      MvPolynomial (Fin 1) E →ₐ[E] MvPolynomial (Fin 2) E).toRingHom))
  rw [sourceHom_factor, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp]
  have : Smooth (Spec.map (CommRingCat.ofHom
      (Polynomial.C : Polynomial E →+* Polynomial (Polynomial E)))) := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    change (algebraMap (Polynomial E) (Polynomial (Polynomial E))).Smooth
    exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingHom) :=
    inferInstanceAs (IsIso
      (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingEquiv.toCommRingCatIso.hom)
  have : IsIso (CommRingCat.ofHom (doublePolynomialEquiv E).symm.toRingHom) :=
    inferInstanceAs (IsIso
      (doublePolynomialEquiv E).symm.toRingEquiv.toCommRingCatIso.hom)
  infer_instance

/-- The exact target coordinate is the source coordinate after swapping the plane. -/
theorem targetMorphism_factor :
    FullFourierKernelCoordinates.targetMorphism E =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.renameEquiv E (Equiv.swap (0 : Fin 2) 1)).toRingHom) ≫
        FourierOriginFromASKernel.sourceMorphism E := by
  dsimp only [FullFourierKernelCoordinates.targetMorphism,
    FourierOriginFromASKernel.sourceMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [FullFourierKernelCoordinates.targetHom]
  · intro i
    simp [FullFourierKernelCoordinates.targetHom, MvPolynomial.renameEquiv_apply]

/-- The actual second full-plane projection is smooth as well. -/
instance targetMorphism_smooth : Smooth (FullFourierKernelCoordinates.targetMorphism E) := by
  rw [targetMorphism_factor]
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.renameEquiv E (Equiv.swap (0 : Fin 2) 1)).toRingHom) :=
    inferInstanceAs (IsIso
      (MvPolynomial.renameEquiv E (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.toCommRingCatIso.hom)
  infer_instance

end PrimeGap182.TypeIII.FullFourierSourceProjectionSmoothFromPolynomialCoordinates

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.FullFourierSourceProjectionSmoothFromPolynomialCoordinates.sourceHom_factor
#print axioms PrimeGap182.TypeIII.FullFourierSourceProjectionSmoothFromPolynomialCoordinates.sourceMorphism_smooth
#print axioms PrimeGap182.TypeIII.FullFourierSourceProjectionSmoothFromPolynomialCoordinates.targetMorphism_factor
#print axioms PrimeGap182.TypeIII.FullFourierSourceProjectionSmoothFromPolynomialCoordinates.targetMorphism_smooth
