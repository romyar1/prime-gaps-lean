import TypeIIIProjectivePlaneModel
import TypeIIIHomogeneousEvaluation
import Mathlib.Algebra.Polynomial.Laurent

/-!
# The actual projective torus chart

The degree-zero localization of B[X,Y,Z] at XYZ is identified with
B[u,u⁻¹,v,v⁻¹]. The maps are explicit: X/Z and Y/Z are the two Laurent
coordinates. The homogeneous-fraction inverse identity is proved in the
ordinary localization using homogeneous evaluation, over any commutative
coefficient ring.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open MvPolynomial HomogeneousLocalization
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable (B : Type u) [CommRing B]

/-- The coordinate ring with the inner Laurent variable u and outer variable v. -/
abbrev ProjectiveTorusLaurentRing := LaurentPolynomial (LaurentPolynomial B)

/-- The first homogeneous coordinate ratio X/Z. -/
def projectiveTorusChartU : ProjectivePlaneTorusChart B :=
  Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1
    (X (0 : Fin 3) ^ 2 * X 1)
    (by
      simpa using (((isHomogeneous_X B (0 : Fin 3)).pow 2).mul
        (isHomogeneous_X B (1 : Fin 3))))

/-- The reciprocal ratio Z/X, with the same homogeneous denominator XYZ. -/
def projectiveTorusChartUInv : ProjectivePlaneTorusChart B :=
  Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1
    (X (1 : Fin 3) * X 2 ^ 2)
    (by
      simpa using ((isHomogeneous_X B (1 : Fin 3)).mul
        ((isHomogeneous_X B (2 : Fin 3)).pow 2)))

/-- The second homogeneous coordinate ratio Y/Z. -/
def projectiveTorusChartV : ProjectivePlaneTorusChart B :=
  Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1
    (X (0 : Fin 3) * X 1 ^ 2)
    (by
      simpa using ((isHomogeneous_X B (0 : Fin 3)).mul
        ((isHomogeneous_X B (1 : Fin 3)).pow 2)))

/-- The reciprocal ratio Z/Y, with the same homogeneous denominator XYZ. -/
def projectiveTorusChartVInv : ProjectivePlaneTorusChart B :=
  Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1
    (X (0 : Fin 3) * X 2 ^ 2)
    (by
      simpa using ((isHomogeneous_X B (0 : Fin 3)).mul
        ((isHomogeneous_X B (2 : Fin 3)).pow 2)))

private theorem chart_fraction_mul_one (a b : ProjectivePlanePolynomialRing B)
    (ha : a ∈ projectivePlaneGrading B (1 • 3))
    (hb : b ∈ projectivePlaneGrading B (1 • 3))
    (hab : a * b = projectivePlaneXYZ B ^ 2) :
    Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1 a ha *
      Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1 b hb = 1 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (projectivePlaneXYZ B))
  simp only [val_mul, Away.val_mk, val_one, Localization.mk_mul, pow_one]
  rw [hab]
  simp [pow_two]

/-- The specified inverse of X/Z is an actual inverse in the chart ring. -/
theorem projectiveTorusChartU_mul_UInv :
    projectiveTorusChartU B * projectiveTorusChartUInv B = 1 := by
  apply chart_fraction_mul_one
  dsimp [projectivePlaneXYZ]
  ring

/-- The specified inverse of Y/Z is an actual inverse in the chart ring. -/
theorem projectiveTorusChartV_mul_VInv :
    projectiveTorusChartV B * projectiveTorusChartVInv B = 1 := by
  apply chart_fraction_mul_one
  dsimp [projectivePlaneXYZ]
  ring

/-- The first coordinate as a unit, with its displayed inverse. -/
def projectiveTorusChartUUnit : (ProjectivePlaneTorusChart B)ˣ where
  val := projectiveTorusChartU B
  inv := projectiveTorusChartUInv B
  val_inv := projectiveTorusChartU_mul_UInv B
  inv_val := by rw [mul_comm, projectiveTorusChartU_mul_UInv]

/-- The second coordinate as a unit, with its displayed inverse. -/
def projectiveTorusChartVUnit : (ProjectivePlaneTorusChart B)ˣ where
  val := projectiveTorusChartV B
  inv := projectiveTorusChartVInv B
  val_inv := projectiveTorusChartV_mul_VInv B
  inv_val := by rw [mul_comm, projectiveTorusChartV_mul_VInv]

/-- Polynomial evaluation X↦u, Y↦v, Z↦1 before localization. -/
def projectiveTorusChartPolynomialEvaluation :
    ProjectivePlanePolynomialRing B →+* ProjectiveTorusLaurentRing B :=
  eval₂Hom (LaurentPolynomial.C.comp LaurentPolynomial.C)
    ![LaurentPolynomial.C (LaurentPolynomial.T 1), LaurentPolynomial.T 1, 1]

private def laurentDenominatorInverse : ProjectiveTorusLaurentRing B :=
  LaurentPolynomial.C (LaurentPolynomial.T (-1)) * LaurentPolynomial.T (-1)

private theorem inner_laurent_inverse :
    (LaurentPolynomial.C (LaurentPolynomial.T 1) : ProjectiveTorusLaurentRing B) *
      LaurentPolynomial.C (LaurentPolynomial.T (-1)) = 1 := by
  rw [← map_mul, ← LaurentPolynomial.T_add]
  norm_num

private theorem outer_laurent_inverse :
    (LaurentPolynomial.T 1 : ProjectiveTorusLaurentRing B) *
      LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]
  norm_num

private theorem polynomialEvaluation_denominator_inverse :
    projectiveTorusChartPolynomialEvaluation B (projectivePlaneXYZ B) *
      laurentDenominatorInverse B = 1 := by
  simp only [projectiveTorusChartPolynomialEvaluation, projectivePlaneXYZ, map_mul,
    eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    mul_one, laurentDenominatorInverse]
  calc
    _ = (LaurentPolynomial.C (LaurentPolynomial.T 1) *
        LaurentPolynomial.C (LaurentPolynomial.T (-1))) *
        ((LaurentPolynomial.T 1 : ProjectiveTorusLaurentRing B) *
          LaurentPolynomial.T (-1)) := by ring
    _ = 1 := by rw [inner_laurent_inverse, outer_laurent_inverse, one_mul]

/-- Dehomogenization, restricted from the actual ordinary localization. -/
def projectiveTorusChartToLaurent :
    ProjectivePlaneTorusChart B →+* ProjectiveTorusLaurentRing B :=
  (Localization.awayLift (projectiveTorusChartPolynomialEvaluation B)
    (projectivePlaneXYZ B)
    (isUnit_iff_exists_inv.mpr
      ⟨laurentDenominatorInverse B, polynomialEvaluation_denominator_inverse B⟩)).comp
    (algebraMap (ProjectivePlaneTorusChart B)
      (Localization.Away (projectivePlaneXYZ B)))

/-- The dehomogenization formula on every equal-degree fraction. -/
theorem projectiveTorusChartToLaurent_mk (n : ℕ)
    (a : ProjectivePlanePolynomialRing B)
    (ha : a ∈ projectivePlaneGrading B (n • 3)) :
    projectiveTorusChartToLaurent B
      (Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) n a ha) =
    projectiveTorusChartPolynomialEvaluation B a *
      (LaurentPolynomial.C (LaurentPolynomial.T (-1)) * LaurentPolynomial.T (-1)) ^ n := by
  exact Localization.awayLift_mk _ _ _ _
    (polynomialEvaluation_denominator_inverse B) n

/-- Dehomogenization fixes the original coefficient ring. -/
theorem projectiveTorusChartToLaurent_coefficient (b : B) :
    projectiveTorusChartToLaurent B (projectivePlaneChartCoefficient B b) =
      LaurentPolynomial.C (LaurentPolynomial.C b) := by
  unfold projectiveTorusChartToLaurent
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    projectivePlaneChartCoefficient_val]
  rw [IsLocalization.Away.lift_eq]
  simp [projectiveTorusChartPolynomialEvaluation]

/-- The inverse map evaluates Laurent polynomials at the two actual chart units. -/
def projectiveTorusLaurentToChart :
    ProjectiveTorusLaurentRing B →+* ProjectivePlaneTorusChart B :=
  LaurentPolynomial.eval₂
    (LaurentPolynomial.eval₂ (projectivePlaneChartCoefficient B)
      (projectiveTorusChartUUnit B)) (projectiveTorusChartVUnit B)

theorem projectiveTorusLaurentToChart_coefficient (b : B) :
    projectiveTorusLaurentToChart B (LaurentPolynomial.C (LaurentPolynomial.C b)) =
      projectivePlaneChartCoefficient B b := by
  simp [projectiveTorusLaurentToChart]

theorem projectiveTorusLaurentToChart_u :
    projectiveTorusLaurentToChart B (LaurentPolynomial.C (LaurentPolynomial.T 1)) =
      projectiveTorusChartU B := by
  simp [projectiveTorusLaurentToChart, projectiveTorusChartUUnit]

theorem projectiveTorusLaurentToChart_uInv :
    projectiveTorusLaurentToChart B (LaurentPolynomial.C (LaurentPolynomial.T (-1))) =
      projectiveTorusChartUInv B := by
  simp [projectiveTorusLaurentToChart, projectiveTorusChartUUnit]

theorem projectiveTorusLaurentToChart_v :
    projectiveTorusLaurentToChart B (LaurentPolynomial.T 1) =
      projectiveTorusChartV B := by
  simp [projectiveTorusLaurentToChart, projectiveTorusChartVUnit]

theorem projectiveTorusLaurentToChart_vInv :
    projectiveTorusLaurentToChart B (LaurentPolynomial.T (-1)) =
      projectiveTorusChartVInv B := by
  simp [projectiveTorusLaurentToChart, projectiveTorusChartVUnit]

/-- The first homogeneous ratio maps to the inner Laurent variable. -/
theorem projectiveTorusChartToLaurent_U :
    projectiveTorusChartToLaurent B (projectiveTorusChartU B) =
      LaurentPolynomial.C (LaurentPolynomial.T 1) := by
  rw [projectiveTorusChartU, projectiveTorusChartToLaurent_mk]
  simp only [projectiveTorusChartPolynomialEvaluation, map_mul, map_pow, eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, pow_one]
  calc
    _ = LaurentPolynomial.C (LaurentPolynomial.T 1) *
        (LaurentPolynomial.C (LaurentPolynomial.T 1) *
          LaurentPolynomial.C (LaurentPolynomial.T (-1))) *
        ((LaurentPolynomial.T 1 : ProjectiveTorusLaurentRing B) *
          LaurentPolynomial.T (-1)) := by ring
    _ = _ := by rw [inner_laurent_inverse, outer_laurent_inverse, mul_one, mul_one]

/-- The second homogeneous ratio maps to the outer Laurent variable. -/
theorem projectiveTorusChartToLaurent_V :
    projectiveTorusChartToLaurent B (projectiveTorusChartV B) =
      LaurentPolynomial.T 1 := by
  rw [projectiveTorusChartV, projectiveTorusChartToLaurent_mk]
  simp only [projectiveTorusChartPolynomialEvaluation, map_mul, map_pow, eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, pow_one]
  calc
    _ = (LaurentPolynomial.T 1 : ProjectiveTorusLaurentRing B) *
        (LaurentPolynomial.C (LaurentPolynomial.T 1) *
          LaurentPolynomial.C (LaurentPolynomial.T (-1))) *
        (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by ring
    _ = _ := by rw [inner_laurent_inverse, outer_laurent_inverse, mul_one, mul_one]

private theorem laurent_hom_ext {R S : Type*} [CommRing R] [CommRing S]
    {f g : LaurentPolynomial R →+* S}
    (hC : ∀ r, f (LaurentPolynomial.C r) = g (LaurentPolynomial.C r))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  ext r
  · simpa using hC r
  · simpa using hT

/-- The explicit homogeneous-coordinate substitution is a right inverse. -/
theorem projectiveTorusChartToLaurent_comp_toChart :
    (projectiveTorusChartToLaurent B).comp (projectiveTorusLaurentToChart B) =
      RingHom.id (ProjectiveTorusLaurentRing B) := by
  apply laurent_hom_ext
  · intro a
    have hc :
        ((projectiveTorusChartToLaurent B).comp (projectiveTorusLaurentToChart B)).comp
            LaurentPolynomial.C = LaurentPolynomial.C := by
      apply laurent_hom_ext
      · intro b
        change projectiveTorusChartToLaurent B
          (projectiveTorusLaurentToChart B (LaurentPolynomial.C (LaurentPolynomial.C b))) = _
        rw [projectiveTorusLaurentToChart_coefficient, projectiveTorusChartToLaurent_coefficient]
      · change projectiveTorusChartToLaurent B
          (projectiveTorusLaurentToChart B (LaurentPolynomial.C (LaurentPolynomial.T 1))) = _
        rw [projectiveTorusLaurentToChart_u, projectiveTorusChartToLaurent_U]
    exact RingHom.congr_fun hc a
  · change projectiveTorusChartToLaurent B
      (projectiveTorusLaurentToChart B (LaurentPolynomial.T 1)) = _
    rw [projectiveTorusLaurentToChart_v, projectiveTorusChartToLaurent_V]
    rfl

local notation "𝓛" => Localization.Away (projectivePlaneXYZ B)
local notation "ι" => algebraMap (ProjectivePlanePolynomialRing B) 𝓛

private theorem chart_fraction_mul_variable
    (a b c : ProjectivePlanePolynomialRing B)
    (ha : a ∈ projectivePlaneGrading B (1 • 3))
    (hab : a * b = c * projectivePlaneXYZ B) :
    (Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1 a ha).val *
      ι b = ι c := by
  simp only [Away.val_mk, pow_one, Localization.mk_eq_mk']
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  change ι (b * a) = ι c * ι (projectivePlaneXYZ B)
  rw [mul_comm b a, hab, map_mul]

private theorem chart_U_mul_Z :
    (projectiveTorusChartU B).val * ι (X (2 : Fin 3)) = ι (X (0 : Fin 3)) := by
  apply chart_fraction_mul_variable
  dsimp [projectivePlaneXYZ]
  ring

private theorem chart_V_mul_Z :
    (projectiveTorusChartV B).val * ι (X (2 : Fin 3)) = ι (X (1 : Fin 3)) := by
  apply chart_fraction_mul_variable
  dsimp [projectivePlaneXYZ]
  ring

private theorem chart_UInv_mul_X :
    (projectiveTorusChartUInv B).val * ι (X (0 : Fin 3)) = ι (X (2 : Fin 3)) := by
  have hi : (projectiveTorusChartUInv B).val * (projectiveTorusChartU B).val = 1 := by
    rw [← val_mul, mul_comm (projectiveTorusChartUInv B),
      projectiveTorusChartU_mul_UInv, val_one]
  calc
    _ = (projectiveTorusChartUInv B).val *
        ((projectiveTorusChartU B).val * ι (X (2 : Fin 3))) := by rw [chart_U_mul_Z]
    _ = ((projectiveTorusChartUInv B).val * (projectiveTorusChartU B).val) *
        ι (X (2 : Fin 3)) := by ring
    _ = _ := by rw [hi, one_mul]

private theorem chart_VInv_mul_Y :
    (projectiveTorusChartVInv B).val * ι (X (1 : Fin 3)) = ι (X (2 : Fin 3)) := by
  have hi : (projectiveTorusChartVInv B).val * (projectiveTorusChartV B).val = 1 := by
    rw [← val_mul, mul_comm (projectiveTorusChartVInv B),
      projectiveTorusChartV_mul_VInv, val_one]
  calc
    _ = (projectiveTorusChartVInv B).val *
        ((projectiveTorusChartV B).val * ι (X (2 : Fin 3))) := by rw [chart_V_mul_Z]
    _ = ((projectiveTorusChartVInv B).val * (projectiveTorusChartV B).val) *
        ι (X (2 : Fin 3)) := by ring
    _ = _ := by rw [hi, one_mul]

private def laurentToOrdinaryLocalization : ProjectiveTorusLaurentRing B →+* 𝓛 :=
  (algebraMap (ProjectivePlaneTorusChart B) 𝓛).comp (projectiveTorusLaurentToChart B)

private theorem laurentToOrdinaryLocalization_coefficient :
    (laurentToOrdinaryLocalization B).comp
      (LaurentPolynomial.C.comp LaurentPolynomial.C) = (ι).comp MvPolynomial.C := by
  ext b
  change (projectiveTorusLaurentToChart B
    (LaurentPolynomial.C (LaurentPolynomial.C b))).val = ι (MvPolynomial.C b)
  rw [projectiveTorusLaurentToChart_coefficient, projectivePlaneChartCoefficient_val]

private theorem laurentToOrdinaryLocalization_variables :
    (fun i : Fin 3 => laurentToOrdinaryLocalization B
      (![LaurentPolynomial.C (LaurentPolynomial.T 1), LaurentPolynomial.T 1, 1] i)) =
      ![(projectiveTorusChartU B).val, (projectiveTorusChartV B).val, 1] := by
  funext i
  fin_cases i <;>
    simp [laurentToOrdinaryLocalization, projectiveTorusLaurentToChart_u,
      projectiveTorusLaurentToChart_v]

private theorem laurentToOrdinaryLocalization_polynomial (a : ProjectivePlanePolynomialRing B) :
    laurentToOrdinaryLocalization B (projectiveTorusChartPolynomialEvaluation B a) =
      eval₂Hom ((ι).comp MvPolynomial.C)
        ![(projectiveTorusChartU B).val, (projectiveTorusChartV B).val, 1] a := by
  rw [projectiveTorusChartPolynomialEvaluation, MvPolynomial.map_eval₂Hom,
    laurentToOrdinaryLocalization_coefficient, laurentToOrdinaryLocalization_variables]

private theorem scaled_chart_variables :
    (fun i : Fin 3 => ι (X (2 : Fin 3)) *
      (![(projectiveTorusChartU B).val, (projectiveTorusChartV B).val, 1] i)) =
      (fun i => ι (X i)) := by
  funext i
  fin_cases i
  · simpa [mul_comm] using chart_U_mul_Z B
  · simpa [mul_comm] using chart_V_mul_Z B
  · simp

private theorem homogeneous_chart_evaluation (n : ℕ)
    (a : ProjectivePlanePolynomialRing B)
    (ha : a ∈ projectivePlaneGrading B (n • 3)) :
    laurentToOrdinaryLocalization B (projectiveTorusChartPolynomialEvaluation B a) *
      ι (X (2 : Fin 3)) ^ (n • 3) = ι a := by
  have h := homogeneous_eval₂_scale ha ((ι).comp MvPolynomial.C) (ι (X (2 : Fin 3)))
    ![(projectiveTorusChartU B).val, (projectiveTorusChartV B).val, 1]
  rw [scaled_chart_variables] at h
  have he : eval₂Hom ((ι).comp MvPolynomial.C) (fun i : Fin 3 => ι (X i)) = ι := by
    ext i <;> simp
  rw [he] at h
  rw [laurentToOrdinaryLocalization_polynomial, mul_comm]
  exact h.symm

private theorem laurent_inverse_times_denominator :
    laurentToOrdinaryLocalization B (laurentDenominatorInverse B) *
      ι (projectivePlaneXYZ B) = ι (X (2 : Fin 3)) ^ 3 := by
  change (projectiveTorusLaurentToChart B (laurentDenominatorInverse B)).val *
    ι (projectivePlaneXYZ B) = _
  rw [laurentDenominatorInverse, map_mul, projectiveTorusLaurentToChart_uInv,
    projectiveTorusLaurentToChart_vInv, val_mul]
  have hF : ι (projectivePlaneXYZ B) =
      ι (X (0 : Fin 3)) * ι (X (1 : Fin 3)) * ι (X (2 : Fin 3)) := by
    change ι (X (0 : Fin 3) * X 1 * X 2) = _
    rw [map_mul, map_mul]
  rw [hF]
  calc
    _ = ((projectiveTorusChartUInv B).val * ι (X (0 : Fin 3))) *
        ((projectiveTorusChartVInv B).val * ι (X (1 : Fin 3))) *
        ι (X (2 : Fin 3)) := by ring
    _ = _ := by rw [chart_UInv_mul_X, chart_VInv_mul_Y]; ring

/-- The explicit substitutions are inverse on every homogeneous fraction. -/
theorem projectiveTorusLaurentToChart_toLaurent (x : ProjectivePlaneTorusChart B) :
    projectiveTorusLaurentToChart B (projectiveTorusChartToLaurent B x) = x := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective
    (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) x
  apply HomogeneousLocalization.val_injective (Submonoid.powers (projectivePlaneXYZ B))
  change laurentToOrdinaryLocalization B
    (projectiveTorusChartToLaurent B
      (Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) n a ha)) = _
  rw [projectiveTorusChartToLaurent_mk, map_mul, map_pow, Away.val_mk,
    Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change (laurentToOrdinaryLocalization B (projectiveTorusChartPolynomialEvaluation B a) *
    laurentToOrdinaryLocalization B (laurentDenominatorInverse B) ^ n) *
      ι (projectivePlaneXYZ B ^ n) = ι a
  rw [map_pow]
  calc
    _ = laurentToOrdinaryLocalization B (projectiveTorusChartPolynomialEvaluation B a) *
        (laurentToOrdinaryLocalization B (laurentDenominatorInverse B) *
          ι (projectivePlaneXYZ B)) ^ n := by rw [mul_pow]; ring
    _ = laurentToOrdinaryLocalization B (projectiveTorusChartPolynomialEvaluation B a) *
        ι (X (2 : Fin 3)) ^ (n • 3) := by
      rw [laurent_inverse_times_denominator, ← pow_mul]
      simp only [smul_eq_mul, Nat.mul_comm]
    _ = ι a := homogeneous_chart_evaluation B n a ha

/-- The actual coordinate-ring isomorphism of the projective torus chart. -/
def projectiveTorusChartEquiv :
    ProjectivePlaneTorusChart B ≃+* ProjectiveTorusLaurentRing B :=
  RingEquiv.ofRingHom (projectiveTorusChartToLaurent B) (projectiveTorusLaurentToChart B)
    (projectiveTorusChartToLaurent_comp_toChart B)
    (RingHom.ext (projectiveTorusLaurentToChart_toLaurent B))

/-- The isomorphism respects the actual coefficient map into the chart. -/
theorem projectiveTorusChartEquiv_coefficient :
    (projectiveTorusChartEquiv B).toRingHom.comp (projectivePlaneChartCoefficient B) =
      LaurentPolynomial.C.comp LaurentPolynomial.C := by
  apply RingHom.ext
  intro b
  exact projectiveTorusChartToLaurent_coefficient B b

/-- The homogeneous numerator of u+v+t/(uv), over the original coefficient ring. -/
def projectiveTorusPhaseNumerator (t : B) : ProjectivePlanePolynomialRing B :=
  X (0 : Fin 3) ^ 2 * X 1 + X 0 * X 1 ^ 2 + MvPolynomial.C t * X 2 ^ 3

/-- The numerator has precisely the same homogeneous degree as XYZ. -/
theorem projectiveTorusPhaseNumerator_homogeneous (t : B) :
    projectiveTorusPhaseNumerator B t ∈ projectivePlaneGrading B 3 :=
  ((((isHomogeneous_X B (0 : Fin 3)).pow 2).mul (isHomogeneous_X B 1)).add
    ((isHomogeneous_X B (0 : Fin 3)).mul ((isHomogeneous_X B 1).pow 2))).add
    (((isHomogeneous_X B (2 : Fin 3)).pow 3).C_mul t)

/-- The actual phase as a regular function on the homogeneous torus chart. -/
def projectiveTorusChartPhase (t : B) : ProjectivePlaneTorusChart B :=
  Away.mk (projectivePlaneGrading B) (projectivePlaneXYZ_homogeneous B) 1
    (projectiveTorusPhaseNumerator B t)
    (by simpa using projectiveTorusPhaseNumerator_homogeneous B t)

/-- The chart isomorphism sends the homogeneous phase to the unchanged Laurent phase. -/
theorem projectiveTorusChartEquiv_phase (t : B) :
    projectiveTorusChartEquiv B (projectiveTorusChartPhase B t) =
      LaurentPolynomial.C (LaurentPolynomial.T 1) + LaurentPolynomial.T 1 +
      LaurentPolynomial.C (LaurentPolynomial.C t) *
        LaurentPolynomial.C (LaurentPolynomial.T (-1)) * LaurentPolynomial.T (-1) := by
  have hu := projectiveTorusChartToLaurent_U B
  have hv := projectiveTorusChartToLaurent_V B
  rw [projectiveTorusChartU, projectiveTorusChartToLaurent_mk] at hu
  rw [projectiveTorusChartV, projectiveTorusChartToLaurent_mk] at hv
  simp only [projectiveTorusChartPolynomialEvaluation, map_mul, map_pow, eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, pow_one] at hu hv
  change projectiveTorusChartToLaurent B (projectiveTorusChartPhase B t) = _
  rw [projectiveTorusChartPhase, projectiveTorusChartToLaurent_mk]
  simp only [projectiveTorusPhaseNumerator, projectiveTorusChartPolynomialEvaluation,
    map_add, map_mul, map_pow, eval₂Hom_X', eval₂Hom_C, RingHom.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_pow, mul_one, pow_one]
  rw [add_mul, add_mul, hu, hv]
  ring

#print axioms ProjectiveTorusLaurentRing
#print axioms projectiveTorusChartU
#print axioms projectiveTorusChartUInv
#print axioms projectiveTorusChartV
#print axioms projectiveTorusChartVInv
#print axioms projectiveTorusChartU_mul_UInv
#print axioms projectiveTorusChartV_mul_VInv
#print axioms projectiveTorusChartUUnit
#print axioms projectiveTorusChartVUnit
#print axioms projectiveTorusChartPolynomialEvaluation
#print axioms projectiveTorusChartToLaurent
#print axioms projectiveTorusChartToLaurent_mk
#print axioms projectiveTorusChartToLaurent_coefficient
#print axioms projectiveTorusLaurentToChart
#print axioms projectiveTorusLaurentToChart_coefficient
#print axioms projectiveTorusLaurentToChart_u
#print axioms projectiveTorusLaurentToChart_uInv
#print axioms projectiveTorusLaurentToChart_v
#print axioms projectiveTorusLaurentToChart_vInv
#print axioms projectiveTorusChartToLaurent_U
#print axioms projectiveTorusChartToLaurent_V
#print axioms projectiveTorusChartToLaurent_comp_toChart
#print axioms projectiveTorusLaurentToChart_toLaurent
#print axioms projectiveTorusChartEquiv
#print axioms projectiveTorusChartEquiv_coefficient
#print axioms projectiveTorusPhaseNumerator
#print axioms projectiveTorusPhaseNumerator_homogeneous
#print axioms projectiveTorusChartPhase
#print axioms projectiveTorusChartEquiv_phase

end PrimeGap182.TypeIII
