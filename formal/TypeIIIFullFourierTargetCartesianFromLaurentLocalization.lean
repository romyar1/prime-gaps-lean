import TypeIIIFullFourierTargetChartFromRelativeAffineCoordinates
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
The SAME native target chart is the actual Cartesian Laurent-open base
change of the full native target projection. The source x stays polynomial,
including zero. Explicit polynomial equivalences identify the actual ring
map with localization of the target coefficient variable; no Cartesian,
compact base-change, cycle, field-model or whole Data premise is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization
open PublishedPhaseApplication GenericCurvePullback GenericRelativeAffineLineCoordinates
open FullFourierTargetChartFromRelativeAffineCoordinates

variable (K : Type) [Field K]

/-- x is the outer polynomial variable; y is the inner coefficient variable. -/
def planePolynomialEquiv : FullFourierKernelCoordinates.PlaneRing (PhaseField K) ≃ₐ[PhaseField K]
    Polynomial (Polynomial (PhaseField K)) :=
  (MvPolynomial.finSuccEquiv (PhaseField K) 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv (PhaseField K) (Fin 1)))

theorem planePolynomialEquiv_X_source :
    planePolynomialEquiv K (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [planePolynomialEquiv, MvPolynomial.finSuccEquiv_X_zero]

theorem planePolynomialEquiv_X_target :
    planePolynomialEquiv K (MvPolynomial.X (1 : Fin 2)) = Polynomial.C Polynomial.X := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv (PhaseField K) (Fin 1)).toRingHom
    ((MvPolynomial.finSuccEquiv (PhaseField K) 1) (MvPolynomial.X (0 : Fin 1).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

/-- Localization of y in the coefficient ring, without localizing x. -/
def targetLocalizationHom : Polynomial (Polynomial (PhaseField K)) →+*
    Polynomial (ParameterRing K) :=
  Polynomial.mapRingHom Polynomial.toLaurent

theorem targetChartHom_localization :
    (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).toRingHom.comp
        (targetChartHom K) =
      (targetLocalizationHom K).comp (planePolynomialEquiv K).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [targetLocalizationHom, targetChartHom, planePolynomialEquiv,
      MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.finSuccEquiv_apply]
  · intro i
    fin_cases i
    · simp [RingHom.comp_apply, targetChartHom_X_source,
        MvPolynomial.uniqueAlgEquiv_apply, planePolynomialEquiv_X_source,
        targetLocalizationHom]
    · simp [RingHom.comp_apply, targetChartHom_X_target,
        MvPolynomial.uniqueAlgEquiv_apply, planePolynomialEquiv_X_target,
        targetLocalizationHom]

theorem targetHom_polynomial :
    (planePolynomialEquiv K).toRingHom.comp
        (FullFourierKernelCoordinates.targetHom (PhaseField K)).toRingHom =
      (Polynomial.C : Polynomial (PhaseField K) →+* Polynomial (Polynomial (PhaseField K))).comp
        (MvPolynomial.uniqueAlgEquiv (PhaseField K) (Fin 1)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [FullFourierKernelCoordinates.targetHom, planePolynomialEquiv,
      MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.finSuccEquiv_apply]
  · intro i
    simp [FullFourierKernelCoordinates.targetHom, planePolynomialEquiv_X_target,
      MvPolynomial.uniqueAlgEquiv_apply]

theorem targetOpenHom_polynomial :
    (ArithmeticSourceMaps.localInputHom (PhaseField K) (PhaseField K)).toRingHom =
      Polynomial.toLaurent.comp
        (MvPolynomial.uniqueAlgEquiv (PhaseField K) (Fin 1)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [ArithmeticSourceMaps.localInputHom, MvPolynomial.uniqueAlgEquiv_apply]
  · intro i
    simp [ArithmeticSourceMaps.localInputHom, MvPolynomial.uniqueAlgEquiv_apply]
    rfl

/-- The actual polynomial localization pushout, before coordinate transport. -/
theorem polynomialLocalization_isPushout :
    IsPushout
      (CommRingCat.ofHom (Polynomial.C : Polynomial (PhaseField K) →+*
        Polynomial (Polynomial (PhaseField K))))
      (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial (PhaseField K) →+* ParameterRing K))
      (CommRingCat.ofHom (targetLocalizationHom K))
      (CommRingCat.ofHom (Polynomial.C : ParameterRing K →+* Polynomial (ParameterRing K))) := by
  let : Algebra (Polynomial (PhaseField K)) (ParameterRing K) := inferInstance
  let : Algebra (Polynomial (Polynomial (PhaseField K))) (Polynomial (ParameterRing K)) :=
    Polynomial.algebra (Polynomial (PhaseField K)) (ParameterRing K)
  let : IsLocalization ((Submonoid.powers (Polynomial.X : Polynomial (PhaseField K))).map
      (Polynomial.C : Polynomial (PhaseField K) →+* Polynomial (Polynomial (PhaseField K))))
      (Polynomial (ParameterRing K)) :=
    Polynomial.isLocalization (Submonoid.powers (Polynomial.X : Polynomial (PhaseField K)))
      (ParameterRing K)
  exact CommRingCat.isPushout_of_isLocalization
    (Polynomial.C : Polynomial (PhaseField K) →+* Polynomial (Polynomial (PhaseField K)))
    (Polynomial.C : ParameterRing K →+* Polynomial (ParameterRing K))
    (by
      apply RingHom.ext
      intro c
      change Polynomial.C (Polynomial.toLaurent c) =
        Polynomial.map Polynomial.toLaurent (Polynomial.C c)
      exact (Polynomial.map_C Polynomial.toLaurent (a := c)).symm)
    (Submonoid.powers (Polynomial.X : Polynomial (PhaseField K)))

/-- No assumed square: all four literal native ring maps form a pushout. -/
theorem targetChart_isPushout :
    IsPushout
      (CommRingCat.ofHom (FullFourierKernelCoordinates.targetHom (PhaseField K)).toRingHom)
      (CommRingCat.ofHom (ArithmeticSourceMaps.localInputHom (PhaseField K) (PhaseField K)).toRingHom)
      (CommRingCat.ofHom (targetChartHom K))
      (CommRingCat.ofHom (MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K)) := by
  apply (polynomialLocalization_isPushout K).of_iso'
    (MvPolynomial.uniqueAlgEquiv (PhaseField K) (Fin 1)).toRingEquiv.toCommRingCatIso
    (planePolynomialEquiv K).toRingEquiv.toCommRingCatIso
    (Iso.refl _)
    (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).toRingEquiv.toCommRingCatIso
  · change CommRingCat.ofHom _ = CommRingCat.ofHom _
    exact congrArg CommRingCat.ofHom (targetHom_polynomial K).symm
  · change CommRingCat.ofHom _ = CommRingCat.ofHom _
    exact congrArg CommRingCat.ofHom (targetOpenHom_polynomial K).symm
  · change CommRingCat.ofHom _ = CommRingCat.ofHom _
    exact congrArg CommRingCat.ofHom (targetChartHom_localization K).symm
  · change CommRingCat.ofHom (Polynomial.C : ParameterRing K →+* Polynomial (ParameterRing K)) =
      CommRingCat.ofHom ((MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).toRingHom.comp
        (MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K))
    exact congrArg CommRingCat.ofHom (show
      (Polynomial.C : ParameterRing K →+* Polynomial (ParameterRing K)) =
        (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).toRingHom.comp
          (MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K) from by
      apply RingHom.ext
      intro c
      exact ((MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).commutes c).symm)

/-- Exact original target-chart square, proved by the actual localization. -/
theorem targetChart_isPullback :
    IsPullback (targetChartMorphism K) (relativeProjection K)
      (FullFourierKernelCoordinates.targetMorphism (PhaseField K))
      (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (targetChart_isPushout K)

/-- The literal chart ring hom factors through coefficient localization and two isos. -/
theorem targetChartHom_factorization :
    targetChartHom K =
      (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).symm.toRingHom.comp
        ((targetLocalizationHom K).comp (planePolynomialEquiv K).toRingHom) := by
  apply RingHom.ext
  intro a
  apply (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).injective
  change (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)) ((targetChartHom K) a) =
    (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1))
      ((MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).symm
        ((targetLocalizationHom K) ((planePolynomialEquiv K) a)))
  rw [AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (targetChartHom_localization K) a

theorem targetLocalization_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (targetLocalizationHom K))) := by
  let : Algebra (Polynomial (Polynomial (PhaseField K))) (Polynomial (ParameterRing K)) :=
    Polynomial.algebra (Polynomial (PhaseField K)) (ParameterRing K)
  let : IsLocalization.Away (Polynomial.C (Polynomial.X : Polynomial (PhaseField K)))
      (Polynomial (ParameterRing K)) := by
    rw [IsLocalization.Away, ← Submonoid.map_powers]
    exact Polynomial.isLocalization (Submonoid.powers (Polynomial.X : Polynomial (PhaseField K)))
      (ParameterRing K)
  exact IsOpenImmersion.of_isLocalization (Polynomial.C (Polynomial.X : Polynomial (PhaseField K)))

/-- The existing actual targetChartMorphism is open; x=0 is retained. -/
instance targetChart_isOpenImmersion : IsOpenImmersion (targetChartMorphism K) := by
  dsimp only [targetChartMorphism]
  rw [targetChartHom_factorization K, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).symm.toRingHom) :=
    inferInstanceAs (IsIso
      (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).symm.toRingEquiv.toCommRingCatIso.hom)
  have : IsIso (CommRingCat.ofHom (planePolynomialEquiv K).toRingHom) :=
    inferInstanceAs (IsIso (planePolynomialEquiv K).toRingEquiv.toCommRingCatIso.hom)
  have := targetLocalization_isOpenImmersion K
  infer_instance

theorem source_zero_retained :
    relativeZeroHom K (targetChartHom K (MvPolynomial.X (0 : Fin 2))) = 0 := by
  rw [targetChartHom_X_source]
  simp [relativeZeroHom]

end PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.planePolynomialEquiv
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.planePolynomialEquiv_X_source
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.planePolynomialEquiv_X_target
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetLocalizationHom
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetChartHom_localization
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetHom_polynomial
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetOpenHom_polynomial
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.polynomialLocalization_isPushout
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetChart_isPushout
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetChart_isPullback
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetChartHom_factorization
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetLocalization_isOpenImmersion
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.targetChart_isOpenImmersion
#print axioms PrimeGap182.TypeIII.FullFourierTargetCartesianFromLaurentLocalization.source_zero_retained
