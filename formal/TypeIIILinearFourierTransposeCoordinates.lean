import TypeIIIRankTwoFourierKernelCoordinates
import TypeIIILinearRadialPhaseFromPoleTransport
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual coefficient-line transpose and Fourier reflection coordinates

The transpose A1 → A2 is t ↦ (a*t,b*t) on the full affine schemes.
Both reflection squares, coordinate-ring surjectivity, closed immersion
and rational-point image are proved using actual polynomial/Spec maps.
No sheaf, Fourier or support-classification law is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.LinearFourierTransposeCoordinates

variable (k : Type) [Field k]

abbrev planeScheme : Scheme := FullFourierKernelCoordinates.planeScheme k
abbrev lineScheme : Scheme := LocalFourierKernelCoordinates.affineLine k

/-- The ACTUAL transpose coefficient line, including its origin. -/
def transposeHom (a b : k) : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 1) k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (if i = 0 then a else b) * MvPolynomial.X 0)

def transposeMorphism (a b : k) : lineScheme k ⟶ planeScheme k :=
  Spec.map (CommRingCat.ofHom (transposeHom k a b).toRingHom)

/-- Negation on the SAME full affine line. -/
def reflectionHom : MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 1) k :=
  MvPolynomial.aeval (fun i => -MvPolynomial.X i)

def reflectionMorphism : lineScheme k ⟶ lineScheme k :=
  Spec.map (CommRingCat.ofHom (reflectionHom k).toRingHom)

@[simp] theorem transposeHom_X (a b : k) (i : Fin 2) :
    transposeHom k a b (MvPolynomial.X i) =
      MvPolynomial.C (if i = 0 then a else b) * MvPolynomial.X 0 := MvPolynomial.aeval_X _ _

@[simp] theorem reflectionHom_X (i : Fin 1) :
    reflectionHom k (MvPolynomial.X i) = -MvPolynomial.X i := MvPolynomial.aeval_X _ _

theorem reflectionHom_square : (reflectionHom k).comp (reflectionHom k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

theorem reflectionRingHom_square :
    (reflectionHom k).toRingHom.comp (reflectionHom k).toRingHom = RingHom.id _ :=
  congrArg AlgHom.toRingHom (reflectionHom_square k)

theorem reflectionMorphism_square : reflectionMorphism k ≫ reflectionMorphism k = 𝟙 _ := by
  dsimp only [reflectionMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, reflectionRingHom_square]
  exact Spec.map_id _

def reflectionIso : lineScheme k ≅ lineScheme k where
  hom := reflectionMorphism k
  inv := reflectionMorphism k
  hom_inv_id := reflectionMorphism_square k
  inv_hom_id := reflectionMorphism_square k

/-- Reflection commutes with the actual dot-product map on every coefficient pair. -/
theorem linear_reflectionHom (a b : k) :
    (LinearRadialPhaseFromPoleTransport.linearHom a b).comp (reflectionHom k) =
      (RankTwoFourierKernelCoordinates.reflectionHom k).comp
        (LinearRadialPhaseFromPoleTransport.linearHom a b) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [LinearRadialPhaseFromPoleTransport.linearHom]
  ring

theorem linear_reflectionMorphism (a b : k) :
    LinearRadialPhaseFromPoleTransport.linearMorphism a b ≫ reflectionMorphism k =
      RankTwoFourierKernelCoordinates.reflectionMorphism k ≫
        LinearRadialPhaseFromPoleTransport.linearMorphism a b := by
  dsimp only [LinearRadialPhaseFromPoleTransport.linearMorphism, reflectionMorphism,
    RankTwoFourierKernelCoordinates.reflectionMorphism]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (linear_reflectionHom k a b)

/-- Reflection commutes with the ACTUAL transpose inclusion. -/
theorem transpose_reflectionHom (a b : k) :
    (transposeHom k a b).comp (RankTwoFourierKernelCoordinates.reflectionHom k) =
      (reflectionHom k).comp (transposeHom k a b) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

theorem transpose_reflectionMorphism (a b : k) :
    transposeMorphism k a b ≫ RankTwoFourierKernelCoordinates.reflectionMorphism k =
      reflectionMorphism k ≫ transposeMorphism k a b := by
  dsimp only [transposeMorphism, reflectionMorphism,
    RankTwoFourierKernelCoordinates.reflectionMorphism]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (transpose_reflectionHom k a b)

/-- A nonzero coefficient makes the ACTUAL coordinate map surjective. -/
theorem transposeHom_surjective (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Surjective (transposeHom k a b) := by
  rcases hab with ha | hb
  · let s : MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 2) k :=
      MvPolynomial.aeval (fun _ => MvPolynomial.C a⁻¹ * MvPolynomial.X 0)
    have hs : (transposeHom k a b).comp s = AlgHom.id k _ := by
      apply MvPolynomial.algHom_ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [hi, s, transposeHom, ← mul_assoc, ← MvPolynomial.C_mul, ha]
    intro P
    exact ⟨s P, congrArg (fun f => f P) hs⟩
  · let s : MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 2) k :=
      MvPolynomial.aeval (fun _ => MvPolynomial.C b⁻¹ * MvPolynomial.X 1)
    have hs : (transposeHom k a b).comp s = AlgHom.id k _ := by
      apply MvPolynomial.algHom_ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [hi, s, transposeHom, ← mul_assoc, ← MvPolynomial.C_mul, hb]
    intro P
    exact ⟨s P, congrArg (fun f => f P) hs⟩

/-- Closed immersion follows from the proved ACTUAL coordinate-ring surjectivity. -/
theorem transpose_isClosedImmersion (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    IsClosedImmersion (transposeMorphism k a b) :=
  IsClosedImmersion.spec_of_surjective _ (transposeHom_surjective k a b hab)

/-- Exact coordinate evaluation of the transpose at EVERY rational point. -/
theorem transpose_evaluation (a b t : k) :
    (MvPolynomial.eval (fun _ : Fin 1 => t)).comp (transposeHom k a b).toRingHom =
      MvPolynomial.eval (fun i : Fin 2 => (if i = 0 then a else b) * t) := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [transposeHom]
  · intro i; simp

theorem point_transposeMorphism (a b t : k) :
    RankTwoFourierKernelCoordinates.linePoint k t ≫ transposeMorphism k a b =
      RankTwoFourierKernelCoordinates.planePoint k ![a * t, b * t] := by
  dsimp only [RankTwoFourierKernelCoordinates.linePoint, transposeMorphism,
    RankTwoFourierKernelCoordinates.planePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, transpose_evaluation]
  congr 3
  funext i
  fin_cases i <;> simp

/-- Coordinate image of the ACTUAL rational-point map is precisely its homogeneous line. -/
theorem transpose_coordinate_range (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    Set.range (fun t : k => (a * t, b * t)) = ScalingLines.originLine (-b) a := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    change (-b) * (a * t) + a * (b * t) = 0
    ring
  · intro h
    change (-b) * z.1 + a * z.2 = 0 at h
    rcases hab with ha | hb
    · refine ⟨z.1 / a, ?_⟩
      apply Prod.ext
      · exact mul_div_cancel₀ z.1 ha
      · change b * (z.1 / a) = z.2
        rw [← mul_div_assoc, div_eq_iff ha]
        linear_combination -h
    · refine ⟨z.2 / b, ?_⟩
      apply Prod.ext
      · change a * (z.2 / b) = z.1
        rw [← mul_div_assoc, div_eq_iff hb]
        linear_combination h
      · exact mul_div_cancel₀ z.2 hb

/-- The convention used in inverse_line_pullback has EXACT old originLine(a,b). -/
theorem normal_transpose_coordinate_range (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    Set.range (fun t : k => (b * t, (-a) * t)) = ScalingLines.originLine a b := by
  have h : b ≠ 0 ∨ -a ≠ 0 := hab.elim (fun h => Or.inr (neg_ne_zero.mpr h)) Or.inl
  simpa only [neg_neg] using transpose_coordinate_range k b (-a) h

/-- Distinct coordinate vectors give distinct ACTUAL rational affine points. -/
theorem planePoint_injective : Function.Injective (RankTwoFourierKernelCoordinates.planePoint k) := by
  intro v w h
  dsimp only [RankTwoFourierKernelCoordinates.planePoint] at h
  have hr := Spec.map_injective h
  funext i
  have hi := congrArg (fun f : CommRingCat.of (MvPolynomial (Fin 2) k) ⟶ CommRingCat.of k =>
    f.hom (MvPolynomial.X i)) hr
  simpa only [CommRingCat.hom_ofHom, MvPolynomial.eval_X] using hi

/-- Factorization of each ACTUAL rational point is exactly its coordinate equality. -/
theorem point_transpose_eq_iff (a b t : k) (z : k × k) :
    RankTwoFourierKernelCoordinates.linePoint k t ≫ transposeMorphism k a b =
      RankTwoFourierKernelCoordinates.planePoint k ![z.1, z.2] ↔ (a * t, b * t) = z := by
  rw [point_transposeMorphism]
  constructor
  · intro h
    have hv := planePoint_injective k h
    apply Prod.ext
    · exact congrFun hv 0
    · exact congrFun hv 1
  · intro h
    subst z
    rfl

/-- The image on ACTUAL k-rational points is precisely the coefficient line. -/
theorem point_factors_iff (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) (z : k × k) :
    (∃ t, RankTwoFourierKernelCoordinates.linePoint k t ≫ transposeMorphism k a b =
      RankTwoFourierKernelCoordinates.planePoint k ![z.1, z.2]) ↔
      z ∈ ScalingLines.originLine (-b) a := by
  simp only [point_transpose_eq_iff]
  exact Set.ext_iff.mp (transpose_coordinate_range k a b hab) z

/-- EXACT inverse_line_pullback line convention, with rational-point factorization. -/
theorem normal_point_factors_iff (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) (z : k × k) :
    (∃ t, RankTwoFourierKernelCoordinates.linePoint k t ≫ transposeMorphism k b (-a) =
      RankTwoFourierKernelCoordinates.planePoint k ![z.1, z.2]) ↔ z ∈ ScalingLines.originLine a b := by
  have h : b ≠ 0 ∨ -a ≠ 0 := hab.elim (fun h => Or.inr (neg_ne_zero.mpr h)) Or.inl
  simpa only [neg_neg] using point_factors_iff k b (-a) h z

end PrimeGap182.TypeIII.LinearFourierTransposeCoordinates

#print axioms PrimeGap182.TypeIII.LinearFourierTransposeCoordinates.transpose_isClosedImmersion
#print axioms PrimeGap182.TypeIII.LinearFourierTransposeCoordinates.linear_reflectionMorphism
#print axioms PrimeGap182.TypeIII.LinearFourierTransposeCoordinates.transpose_reflectionMorphism
#print axioms PrimeGap182.TypeIII.LinearFourierTransposeCoordinates.point_transposeMorphism
#print axioms PrimeGap182.TypeIII.LinearFourierTransposeCoordinates.normal_transpose_coordinate_range
#print axioms PrimeGap182.TypeIII.LinearFourierTransposeCoordinates.normal_point_factors_iff
