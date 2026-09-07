import SharpPrimeMeasure182
import SharpResidualTuples182

/-! Literal closed limiting region and all boundary strips for the sharp
five-prime residual. The first 19 faces impose roughness, the first order
type, and all ten pair caps. Ten further hyperplanes exclude collisions.+-/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
open Filter MeasureTheory Set PrimeGap186

namespace PrimeGap182Analytic.SharpMean

def sharpCoreCoefficients : Fin 19 → Fin 5 → ℝ :=
  ![![1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1],
    ![0, 0, 1, -1, 0],
    ![0, 1, -1, 0, 0],
    ![1, -1, 0, 0, 0],
    ![0, 0, 0, -1, 1],
    ![-1, -1, 0, 0, 0],
    ![-1, 0, -1, 0, 0],
    ![-1, 0, 0, -1, 0],
    ![-1, 0, 0, 0, -1],
    ![0, -1, -1, 0, 0],
    ![0, -1, 0, -1, 0],
    ![0, -1, 0, 0, -1],
    ![0, 0, -1, -1, 0],
    ![0, 0, -1, 0, -1],
    ![0, 0, 0, -1, -1]]

def sharpCoreThreshold : Fin 19 → ℝ :=
  ![8639 / 50000, 8639 / 50000, 8639 / 50000, 8639 / 50000, 8639 / 50000, 0, 0, 0, 0, -(41361 / 100000), -(41361 / 100000), -(41361 / 100000), -(41361 / 100000), -(41361 / 100000), -(41361 / 100000), -(41361 / 100000), -(41361 / 100000), -(41361 / 100000), -(41361 / 100000)]

def sharpCollisionCoefficients : Fin 10 → Fin 5 → ℝ :=
  ![![1, -1, 0, 0, 0],
    ![1, 0, -1, 0, 0],
    ![1, 0, 0, -1, 0],
    ![1, 0, 0, 0, -1],
    ![0, 1, -1, 0, 0],
    ![0, 1, 0, -1, 0],
    ![0, 1, 0, 0, -1],
    ![0, 0, 1, -1, 0],
    ![0, 0, 1, 0, -1],
    ![0, 0, 0, 1, -1]]

def sharpCoreNormal (j : Fin 19) (i : Fin 4) : ℝ :=
  sharpCoreCoefficients j i.castSucc - sharpCoreCoefficients j 4

def sharpCoreOffset (j : Fin 19) : ℝ :=
  sharpCoreThreshold j - sharpCoreCoefficients j 4

def sharpCoreStrict (α : Fin 5 → ℝ) : Prop :=
  ∀ j, sharpCoreThreshold j < ∑ i, sharpCoreCoefficients j i * α i

def sharpCoreClosed (α : Fin 5 → ℝ) : Prop :=
  ∀ j, sharpCoreThreshold j ≤ ∑ i, sharpCoreCoefficients j i * α i

def sharpResidualRegion : Set (Fin 4 → ℝ) :=
  {t | sharpCoreClosed (Fin.snoc t (1 - ∑ i, t i))}

theorem sharpCoreStrict_iff (α : Fin 5 → ℝ) :
    sharpCoreStrict α ↔ (∀ i, (8639 : ℝ) / 50000 < α i) ∧
      sharpResidualOrder 0 α ∧ (∀ i j : Fin 5, i < j → α i + α j < 41361 / 100000) := by
  simp [sharpCoreStrict, sharpCoreCoefficients, sharpCoreThreshold, sharpResidualOrder,
    Fin.forall_fin_succ, Fin.sum_univ_succ]
  constructor <;> intro h <;> rcases h with h <;> grind only [= sub_eq_add_neg]

theorem sharpCoreClosed_iff (α : Fin 5 → ℝ) :
    sharpCoreClosed α ↔ (∀ i, (8639 : ℝ) / 50000 ≤ α i) ∧
      (α 3 ≤ α 2 ∧ α 2 ≤ α 1 ∧ α 1 ≤ α 0 ∧ α 3 ≤ α 4) ∧
      (∀ i j : Fin 5, i < j → α i + α j ≤ 41361 / 100000) := by
  simp [sharpCoreClosed, sharpCoreCoefficients, sharpCoreThreshold,
    Fin.forall_fin_succ, Fin.sum_univ_succ]
  constructor <;> intro h <;> rcases h with h <;> grind only [= sub_eq_add_neg]

theorem sharpCoreNormal_ne_zero (j : Fin 19) : sharpCoreNormal j ≠ 0 := by
  fin_cases j <;>
    norm_num [sharpCoreNormal, sharpCoreCoefficients, Function.ne_iff,
      Fin.exists_fin_succ, Matrix.cons_val_four]

theorem sharpCore_last_bound (j : Fin 19) : |sharpCoreCoefficients j 4| ≤ 1 := by
  fin_cases j <;> norm_num [sharpCoreCoefficients, Matrix.cons_val_four]

theorem sharpCoreClosed_snoc (t : Fin 4 → ℝ) :
    sharpCoreClosed (Fin.snoc t (1 - ∑ i, t i)) ↔
      ∀ j, sharpCoreOffset j ≤ ∑ i, sharpCoreNormal j i * t i := by
  unfold sharpCoreClosed
  apply forall_congr'
  intro j
  have h := snoc_affine_limit_eq (sharpCoreCoefficients j) (sharpCoreThreshold j) t
  rw [show Fin.last 4 = (4 : Fin 5) from rfl] at h
  dsimp only [sharpCoreOffset, sharpCoreNormal]
  constructor <;> intro hj <;> linarith only [h, hj]

theorem measurableSet_sharpResidualRegion : MeasurableSet sharpResidualRegion := by
  have heq : sharpResidualRegion = ⋂ j : Fin 19,
      {t : Fin 4 → ℝ | sharpCoreOffset j ≤ ∑ i, sharpCoreNormal j i * t i} := by
    ext t
    simp only [sharpResidualRegion, Set.mem_ofPred_eq, Set.mem_iInter, sharpCoreClosed_snoc]
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  exact (isClosed_le continuous_const (by fun_prop)).measurableSet

theorem sharpResidualRegion_frontier_null : volume (frontier sharpResidualRegion) = 0 := by
  classical
  let s := List.ofFn fun j : Fin 19 => (sharpCoreNormal j, sharpCoreOffset j)
  have hs : ∀ v ∈ s, ∃ i, v.1 i ≠ 0 := by
    intro v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact Function.ne_iff.mp (sharpCoreNormal_ne_zero j)
  have heq : sharpResidualRegion =
      ⋂ v ∈ s.toFinset, {t : Fin 4 → ℝ | v.2 ≤ ∑ i, v.1 i * t i} := by
    ext t
    simp only [sharpResidualRegion, Set.mem_ofPred_eq, sharpCoreClosed_snoc,
      Set.mem_iInter, List.mem_toFinset, s, List.mem_ofFn]
    constructor
    · intro ht v hv
      obtain ⟨j, rfl⟩ := hv
      exact ht j
    · intro ht j
      exact ht _ ⟨j, rfl⟩
  rw [heq]
  exact volume_frontier_finite_halfspace_intersection s hs

def sharpFirstMass : ℝ :=
  (finiteMeasureWithContinuousDensity reciprocalExponentMeasure
    reciprocalResidualExponent : Measure (Fin 4 → ℝ)).real sharpResidualRegion

theorem sharpFirstMass_nonneg : 0 ≤ sharpFirstMass := measureReal_nonneg

open Classical in
theorem sharpFirstMass_reciprocal_tendsto : Tendsto
    (fun x : ℝ => ∑ p ∈ exceptionalPrimeQuadruples x,
      if primeQuadrupleExponents x p ∈ sharpResidualRegion then
        ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹ else 0)
    atTop (nhds sharpFirstMass) := by
  have hm := tendsto_finiteMeasureWithContinuousDensity reciprocalResidualExponent
    (fun t => (reciprocalResidualExponent_pos t).le) tendsto_primeQuadrupleExponentMeasure
  have hn : (finiteMeasureWithContinuousDensity reciprocalExponentMeasure
      reciprocalResidualExponent : Measure (Fin 4 → ℝ)) (frontier sharpResidualRegion) = 0 :=
    ((finiteMeasureWithContinuousDensity_absolutelyContinuous _ _).trans
      reciprocalExponentMeasure_absolutelyContinuous_volume) sharpResidualRegion_frontier_null
  have hl := NNReal.tendsto_coe.mpr (tendsto_finiteMeasure_apply_of_null_frontier hm hn)
  apply hl.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  exact weighted_primeQuadrupleExponentMeasure_real x hx sharpResidualRegion
    measurableSet_sharpResidualRegion

#print axioms sharpCoreStrict_iff
#print axioms sharpResidualRegion_frontier_null
#print axioms sharpFirstMass_reciprocal_tendsto

end PrimeGap182Analytic.SharpMean
