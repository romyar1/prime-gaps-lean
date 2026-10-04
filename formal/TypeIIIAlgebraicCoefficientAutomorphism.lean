import TypeIIICoefficientAutomorphism
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Continuous extension to algebraic coefficient fields

Uniqueness of the norm over a complete nonarchimedean field proves that
an extension of a norm-preserving coefficient automorphism is an isometry.
Thus extending to an algebraically closed algebraic overfield does not
require a new continuity assumption.
-/

noncomputable section

namespace PrimeGap182.TypeIII.AlgebraicCoefficientAutomorphism

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
  [Algebra.IsAlgebraic K L]

/-- Pulling the absolute value back along an extension preserves the
base norm; uniqueness of the extended norm determines it everywhere. -/
theorem norm_eq (e : K ≃+* K) (he : ∀ x : K, ‖e x‖ = ‖x‖)
    (σ : L ≃+* L)
    (hσ : ∀ x : K, σ (algebraMap K L x) = algebraMap K L (e x)) (x : L) :
    ‖σ x‖ = ‖x‖ := by
  let f : AbsoluteValue L ℝ :=
    { toFun := fun y => ‖σ y‖
      map_mul' := fun a b => by simp only [map_mul, norm_mul]
      nonneg' := fun a => norm_nonneg _
      eq_zero' := fun a => by
        rw [norm_eq_zero]
        exact σ.map_eq_zero_iff
      add_le' := fun a b => by simpa only [map_add] using norm_add_le (σ a) (σ b) }
  have hf (a : K) : f (algebraMap K L a) = ‖a‖ := by
    change ‖σ (algebraMap K L a)‖ = ‖a‖
    rw [hσ, norm_algebraMap, he, norm_one, mul_one]
  exact (spectralNorm_unique_field_norm_ext hf x).trans
    (NormedAlgebra.norm_eq_spectralNorm K x).symm

theorem isometry (e : K ≃+* K) (he : ∀ x : K, ‖e x‖ = ‖x‖)
    (σ : L ≃+* L)
    (hσ : ∀ x : K, σ (algebraMap K L x) = algebraMap K L (e x)) :
    Isometry σ := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, ← map_sub, norm_eq e he σ hσ, dist_eq_norm]

variable [IsAlgClosed L]

/-- The same algebraic extension used by the coefficient trace bridge
is continuous, with continuous inverse, in the extended valued topology. -/
theorem extension_isometry (e : K ≃+* K) (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    Isometry (CoefficientAutomorphism.extension K L e) :=
  isometry e he _ (CoefficientAutomorphism.extension_spec K L e)

theorem extension_continuous (e : K ≃+* K) (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    Continuous (CoefficientAutomorphism.extension K L e) :=
  (extension_isometry e he).continuous

theorem extension_symm_continuous (e : K ≃+* K) (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    Continuous (CoefficientAutomorphism.extension K L e).symm := by
  have hi := extension_isometry (L := L) e he
  have hs : Isometry (CoefficientAutomorphism.extension K L e).symm := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    simpa only [RingEquiv.apply_symm_apply] using
      (hi.dist_eq ((CoefficientAutomorphism.extension K L e).symm x)
        ((CoefficientAutomorphism.extension K L e).symm y)).symm
  exact hs.continuous

end PrimeGap182.TypeIII.AlgebraicCoefficientAutomorphism

#print axioms PrimeGap182.TypeIII.AlgebraicCoefficientAutomorphism.norm_eq
#print axioms PrimeGap182.TypeIII.AlgebraicCoefficientAutomorphism.isometry
#print axioms PrimeGap182.TypeIII.AlgebraicCoefficientAutomorphism.extension_isometry
#print axioms PrimeGap182.TypeIII.AlgebraicCoefficientAutomorphism.extension_continuous
#print axioms PrimeGap182.TypeIII.AlgebraicCoefficientAutomorphism.extension_symm_continuous
