import TypeIIIRelativeAffineFourierKernelFromActualCoordinates
import TypeIIIMiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology

/-!
The actual source Gm open pulls back to the SAME relative Laurent open.
Both opens are literal Away-X localizations; their coordinate ring is the
original parameter ring, with no field replacement or deleted source origin.
This proves a Cartesian square, without any smooth base-change, tensor,
cohomology, model interpretation, or completed Fourier comparison premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization
open GenericRelativeAffineLineCoordinates GenericSourceSpecialization
open GenericCurvePullback RelativeAffineFourierKernelFromActualCoordinates
open PublishedPhaseApplication FourierSourceMaps

variable (R : Type) [CommRing R]

/-- The actual one-variable polynomial-to-Laurent homomorphism. -/
def affineLaurentHom : MvPolynomial (Fin 1) R →+* LaurentPolynomial R :=
  Polynomial.toLaurent.comp (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom

/-- The polynomial coordinate isomorphism followed by actual Laurent localization. -/
instance affineLaurentHom_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineLaurentHom R))) := by
  dsimp only [affineLaurentHom]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R))) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial R) (LaurentPolynomial R))))
    exact IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial R)
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom) :=
    inferInstanceAs (IsIso
      (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingEquiv.toCommRingCatIso.hom)
  infer_instance

/-- Transporting the polynomial Away-X localization changes no coordinates. -/
theorem affineLaurentHom_opensRange :
    (Spec.map (CommRingCat.ofHom (affineLaurentHom R))).opensRange =
      PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) := by
  let : Algebra (MvPolynomial (Fin 1) R) (LaurentPolynomial R) :=
    (affineLaurentHom R).toAlgebra
  let : IsLocalization.Away (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R)
      (LaurentPolynomial R) := by
    apply IsLocalization.of_ringEquiv_left
      (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingEquiv
      (M₁ := Submonoid.powers (Polynomial.X : Polynomial R))
      (M₂ := Submonoid.powers (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R))
    · simp [Submonoid.map_powers, MvPolynomial.uniqueAlgEquiv]
    · intro a
      rfl
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R)
    (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R)

variable (E : Type) [Field E]

/-- The SAME arithmetic local input has exactly the nonzero-source image. -/
theorem localInput_opensRange :
    (ArithmeticSourceMaps.localInputMorphism E E).opensRange =
      PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) E) := by
  have h : (ArithmeticSourceMaps.localInputHom E E).toRingHom = affineLaurentHom E := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ArithmeticSourceMaps.localInputHom, affineLaurentHom]
    · intro i
      simp [ArithmeticSourceMaps.localInputHom, affineLaurentHom,
        MvPolynomial.uniqueAlgEquiv, Polynomial.toLaurent_X]
      rfl
  apply TopologicalSpace.Opens.ext
  change Set.range (PrimeSpectrum.comap
    (ArithmeticSourceMaps.localInputHom E E).toRingHom) = _
  rw [h]
  exact SetLike.ext'_iff.mp (affineLaurentHom_opensRange E)

variable (K : Type) [Field K]

/-- The relative open retains the original parameter ring and exact source X. -/
theorem relativeOpen_opensRange :
    (relativeOpenMorphism K).opensRange =
      PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1) : RelativeAffineRing K) :=
  affineLaurentHom_opensRange (ParameterRing K)

/-- Pulling back the source open gives the actual relative Laurent open. -/
theorem source_preimage_localOpen :
    sourceMorphism K ⁻¹ᵁ (ArithmeticSourceMaps.localInputMorphism
      (PhaseField K) (PhaseField K)).opensRange = (relativeOpenMorphism K).opensRange := by
  rw [localInput_opensRange, relativeOpen_opensRange]
  change (Spec.map (CommRingCat.ofHom (sourceHom K))) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) = _
  rw [SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (sourceHom K (MvPolynomial.X (0 : Fin 1))) = _
  simp only [sourceHom, MvPolynomial.eval₂Hom_X']

/-- A genuine Cartesian square, beyond the previously checked commuting equation. -/
theorem sourceOpen_isPullback :
    IsPullback (projectionMorphism K) (relativeOpenMorphism K)
      (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K))
      (sourceMorphism K) :=
  IsOpenImmersion.isPullback _ _ _ _
    (open_comp_sourceMorphism K) (source_preimage_localOpen K)

end PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization.affineLaurentHom
#print axioms PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization.affineLaurentHom_isOpenImmersion
#print axioms PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization.affineLaurentHom_opensRange
#print axioms PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization.localInput_opensRange
#print axioms PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization.relativeOpen_opensRange
#print axioms PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization.source_preimage_localOpen
#print axioms PrimeGap182.TypeIII.FourierSourceOpenCartesianFromLaurentLocalization.sourceOpen_isPullback
