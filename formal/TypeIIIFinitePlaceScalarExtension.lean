import TypeIIIClosedCyclotomicCoefficient
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Scalar extension between finite-place completions

Construct the continuous map from the completion of the base number field
to the existing completed coefficient field. A dense tensor-product image
then proves finite dimensionality, retaining the original number-field map.
-/

noncomputable section
open scoped Topology TensorProduct Valued

namespace PrimeGap182.TypeIII.FinitePlaceScalarExtension

open NumberField IsDedekindDomain LocalCyclotomicCoefficient

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Complete the original scalar embedding at the chosen places. -/
def completionMap : v.adicCompletion K →+* LocalField L w :=
  (UniformSpace.Completion.mapRingHom
    (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom

theorem completionMap_continuous : Continuous (completionMap K L v w) :=
  UniformSpace.Completion.continuous_map.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)

theorem completionMap_on_base (x : K) :
    completionMap K L v w (algebraMap K (v.adicCompletion K) x) =
      embedding L w (algebraMap K L x) := by
  exact UniformSpace.Completion.mapRingHom_coe
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous
      ((WithVal.equiv (v.valuation K)).symm x)

scoped instance completionAlgebra : Algebra (v.adicCompletion K) (LocalField L w) :=
  (completionMap K L v w).toAlgebra

scoped instance completionContinuousSMul :
    ContinuousSMul (v.adicCompletion K) (LocalField L w) where
  continuous_smul := (completionMap_continuous K L v w).comp continuous_fst |>.mul continuous_snd

scoped instance completionScalarTower : IsScalarTower K (v.adicCompletion K) (LocalField L w) :=
  .of_algebraMap_eq fun x => by
    exact (completionMap_on_base K L v w x).symm

/-- The completed extension is finite over the completed base: the image
of the finite-dimensional scalar-extension tensor product is closed and
contains the dense image of the original number field. -/
theorem finiteDimensional : FiniteDimensional (v.adicCompletion K) (LocalField L w) := by
  let Φ : (v.adicCompletion K) ⊗[K] L →ₗ[v.adicCompletion K] LocalField L w :=
    (Algebra.TensorProduct.lift (Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
      (LocalField L w)) (Algebra.algHom K L (LocalField L w))
        (fun _ _ => mul_comm ..)).toLinearMap
  have hd : DenseRange (embedding L w) := by
    exact UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (w.valuation L)).symm.surjective.denseRange
        (UniformSpace.Completion.continuous_coe _)
  have hΦ : DenseRange Φ := by
    apply hd.mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom, embedding]; rfl⟩
  apply Module.Finite.of_surjective Φ
  have hc : IsClosed (Set.range Φ) := by
    rw [← Φ.coe_range]
    exact Φ.range.closed_of_finiteDimensional
  rw [← Set.range_eq_univ, ← hc.closure_eq]
  exact hΦ.closure_range

end PrimeGap182.TypeIII.FinitePlaceScalarExtension

#print axioms PrimeGap182.TypeIII.FinitePlaceScalarExtension.completionMap
#print axioms PrimeGap182.TypeIII.FinitePlaceScalarExtension.completionMap_continuous
#print axioms PrimeGap182.TypeIII.FinitePlaceScalarExtension.completionMap_on_base
#print axioms PrimeGap182.TypeIII.FinitePlaceScalarExtension.completionAlgebra
#print axioms PrimeGap182.TypeIII.FinitePlaceScalarExtension.completionContinuousSMul
#print axioms PrimeGap182.TypeIII.FinitePlaceScalarExtension.completionScalarTower
#print axioms PrimeGap182.TypeIII.FinitePlaceScalarExtension.finiteDimensional
