import TypeIIIGenericCurvePullback

/-!
# The normalized Fourier source maps

The same generic curve maps to the local x-line over PhaseField(K).
Its first Kl3 map is projection followed by the inclusion into A1_K;
its second is the same map after scalar multiplication by the exact
angular unit. The third is the literal additive kernel (T^2/s)*x.
These are identities of ring maps and schemes, before using sheaves.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.FourierSourceMaps

open StartingSourceMaps PublishedPhaseApplication GenericSourceSpecialization

universe u
variable (K : Type u) [Field K]

abbrev LocalRing := LaurentPolynomial (PhaseField K)
abbrev localScheme : Scheme := Spec (.of (LocalRing K))

def localInputHom : MvPolynomial (Fin 1) K →ₐ[K] LocalRing K :=
  aeval (fun _ => (PhysicalTorusLaurent.variableUnit (PhaseField K) : LocalRing K))

def projectionHom : LocalRing K →ₐ[K] GenericRing K where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K)
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _
      (LaurentPolynomial.C (algebraMap K (PhaseField K) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact IsScalarTower.algebraMap_apply K (PhaseField K) (GenericRing K) c

def scalarHom (lambda : (PhaseField K)ˣ) : LocalRing K →ₐ[K] LocalRing K where
  toRingHom := LaurentPolynomial.eval₂ LaurentPolynomial.C
    (Units.map (LaurentPolynomial.C : PhaseField K →+* LocalRing K).toMonoidHom lambda *
      PhysicalTorusLaurent.variableUnit (PhaseField K))
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _
      (LaurentPolynomial.C (algebraMap K (PhaseField K) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    rfl

theorem scalarHom_one : scalarHom K 1 = AlgHom.id K (LocalRing K) := by
  apply AlgHom.coe_ringHom_injective
  apply SourceCurveBaseChange.laurent_ringHom_ext
  · apply RingHom.ext
    intro c
    exact LaurentPolynomial.eval₂_C _ _ c
  · apply Units.ext
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]
    simp only [map_one, one_mul]
    rfl

def additiveHom (s : (PhaseField K)ˣ) : MvPolynomial (Fin 1) K →ₐ[K] GenericRing K :=
  aeval (fun _ => ((parameterUnit K ^ 2 / constantUnit K s : (GenericRing K)ˣ) : GenericRing K) *
    (curveUnit K : GenericRing K))

variable (alpha m n : Kˣ)

theorem first_inputHom :
    (projectionHom K).comp (localInputHom K) = genericInputHom K alpha m n 0 := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  simp only [AlgHom.comp_apply, localInputHom, genericInputHom, aeval_X, Matrix.cons_val_zero]
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

theorem second_inputHom :
    ((projectionHom K).comp (scalarHom K (lambdaUnit K m n))).comp (localInputHom K) =
      genericInputHom K alpha m n 1 := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  simp only [AlgHom.comp_apply, localInputHom, genericInputHom, aeval_X, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [radialCoefficients_lambda K alpha m n]
  change LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K)
    (LaurentPolynomial.eval₂ LaurentPolynomial.C _ (LaurentPolynomial.T 1)) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  change LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K)
    (LaurentPolynomial.C (lambdaUnit K m n : PhaseField K) * LaurentPolynomial.T 1) = _
  rw [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_one]
  rfl

theorem additive_inputHom :
    additiveHom K (scaleUnit K alpha m) = genericInputHom K alpha m n 2 := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  simp only [additiveHom, genericInputHom, aeval_X, Matrix.cons_val_two]
  rw [radialCoefficients_xi K alpha m n]
  rfl

theorem lambdaUnit_eq_angularUnit :
    lambdaUnit K m n = CanonicalLocalCorrelation.angularUnit (m : K) (n : K) m.ne_zero n.ne_zero := by
  apply Units.ext
  exact lambdaUnit_value K m n

theorem scaleUnit_eq_radialScale :
    scaleUnit K alpha m = Units.mk0 (radialScale (alpha : K) (m : K))
      (radialScale_ne_zero (alpha : K) (m : K) alpha.ne_zero m.ne_zero) := by
  apply Units.ext
  exact scaleUnit_value K alpha m

def localInputMorphism : localScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (localInputHom K).toRingHom)

def projectionMorphism : genericScheme K ⟶ localScheme K :=
  Spec.map (CommRingCat.ofHom (projectionHom K).toRingHom)

def scalarMorphism (lambda : (PhaseField K)ˣ) : localScheme K ⟶ localScheme K :=
  Spec.map (CommRingCat.ofHom (scalarHom K lambda).toRingHom)

def additiveMorphism (s : (PhaseField K)ˣ) : genericScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (additiveHom K s).toRingHom)

theorem scalarMorphism_one : scalarMorphism K 1 = 𝟙 (localScheme K) := by
  rw [scalarMorphism, scalarHom_one]
  exact Spec.map_id _

theorem first_inputMorphism :
    projectionMorphism K ≫ localInputMorphism K = genericInputMorphism K alpha m n 0 := by
  dsimp only [projectionMorphism, localInputMorphism, genericInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (first_inputHom K alpha m n))

theorem second_inputMorphism :
    (projectionMorphism K ≫ scalarMorphism K (lambdaUnit K m n)) ≫ localInputMorphism K =
      genericInputMorphism K alpha m n 1 := by
  dsimp only [projectionMorphism, scalarMorphism, localInputMorphism, genericInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (second_inputHom K alpha m n))

theorem additive_inputMorphism :
    additiveMorphism K (scaleUnit K alpha m) = genericInputMorphism K alpha m n 2 :=
  congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (additive_inputHom K alpha m n))

end PrimeGap182.TypeIII.FourierSourceMaps

#print axioms PrimeGap182.TypeIII.FourierSourceMaps.scalarHom_one
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.first_inputHom
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.second_inputHom
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.additive_inputHom
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.lambdaUnit_eq_angularUnit
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.scaleUnit_eq_radialScale
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.scalarMorphism_one
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.first_inputMorphism
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.second_inputMorphism
#print axioms PrimeGap182.TypeIII.FourierSourceMaps.additive_inputMorphism
