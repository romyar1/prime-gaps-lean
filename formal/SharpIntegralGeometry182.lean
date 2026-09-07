import SharpMinorantMean182

/-! Exact Lebesgue integral and normalized polytope for the actual sharp
minorant mean. The three-simplex geometry is the parameter-independent
geometry proved in PrimeGaps186. The affine scale is rechecked here at
1361/100000; no numerical integral bound is assumed in this file. -/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction Pointwise
open Filter MeasureTheory Set PrimeGap186

namespace PrimeGap182Analytic.SharpMean

local notation "box" =>
  (Set.Icc (fun _ : Fin 4 => exceptionalExponentLower)
    (fun _ : Fin 4 => exceptionalExponentUpper))

theorem five_pair_closed_geometry (a : ℝ) (v : Fin 5 → ℝ)
    (hsum : 1 ≤ ∑ i, v i)
    (hpair : ∀ i j : Fin 5, i < j → v i + v j ≤ a) :
    ∀ i, 1 - 2 * a ≤ v i ∧ v i ≤ (4 * a - 1) / 3 := by
  have h01 := hpair 0 1 (by decide)
  have h02 := hpair 0 2 (by decide)
  have h03 := hpair 0 3 (by decide)
  have h04 := hpair 0 4 (by decide)
  have h12 := hpair 1 2 (by decide)
  have h13 := hpair 1 3 (by decide)
  have h14 := hpair 1 4 (by decide)
  have h23 := hpair 2 3 (by decide)
  have h24 := hpair 2 4 (by decide)
  have h34 := hpair 3 4 (by decide)
  simp [Fin.sum_univ_succ] at hsum
  intro i
  fin_cases i <;> constructor <;> dsimp <;>
    linarith only [hsum, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]

theorem sharpResidualRegion_subset_box : sharpResidualRegion ⊆ box := by
  intro t ht
  obtain ⟨hlo, _, hp⟩ := (sharpCoreClosed_iff _).mp ht
  have hg := five_pair_closed_geometry ((41361 : ℝ) / 100000)
    (Fin.snoc t (1 - ∑ i, t i)) (coefficient_sum_one t).ge hp
  constructor
  · intro i
    simpa only [Fin.snoc_castSucc, exceptionalExponentLower] using hlo i.castSucc
  · intro i
    have hi := (hg i.castSucc).2
    simp only [Fin.snoc_castSucc] at hi
    dsimp only [exceptionalExponentUpper]
    linarith only [hi]

def sharpDensity (t : Fin 4 → ℝ) : ℝ :=
  (∏ i : Fin 5, (Fin.snoc t (1 - ∑ j, t j) : Fin 5 → ℝ) i)⁻¹

theorem sharpDensity_eq (t : Fin 4 → ℝ) :
    sharpDensity t = (1 - ∑ i, t i)⁻¹ * (∏ i, t i)⁻¹ := by
  simp only [sharpDensity, Fin.prod_snoc, mul_inv_rev]

theorem sharpDensity_integrableOn : IntegrableOn sharpDensity sharpResidualRegion := by
  have hc : ContinuousOn sharpDensity box := by
    rw [show sharpDensity = (fun t => (1 - ∑ i, t i)⁻¹ * (∏ i, t i)⁻¹)
      from funext sharpDensity_eq]
    exact continuousOn_inv_one_sub_sum_exceptional_exponent_box.mul
      continuousOn_reciprocal_exponent_density
  exact (hc.integrableOn_compact isCompact_Icc).mono_set sharpResidualRegion_subset_box

theorem sharpFirstMass_eq_integral :
    sharpFirstMass = ∫ t in sharpResidualRegion, sharpDensity t := by
  unfold sharpFirstMass
  rw [finiteMeasureWithContinuousDensity_real reciprocalExponentMeasure
    reciprocalResidualExponent (fun t => (reciprocalResidualExponent_pos t).le)
    sharpResidualRegion measurableSet_sharpResidualRegion,
    setIntegral_reciprocalExponentMeasure reciprocalResidualExponent sharpResidualRegion
      measurableSet_sharpResidualRegion,
    Set.inter_eq_left.mpr sharpResidualRegion_subset_box]
  apply setIntegral_congr_fun measurableSet_sharpResidualRegion
  intro t ht
  dsimp only
  rw [reciprocalResidualExponent_eq_inv_one_sub_sum_of_mem_box
    (sharpResidualRegion_subset_box ht), sharpDensity_eq]

theorem sharpMass_eq_integral :
    sharpMass = 6 * ∫ t in sharpResidualRegion, sharpDensity t := by
  rw [sharpMass, sharpFirstMass_eq_integral]

theorem ordered_pair_caps_iff (a : ℝ) (α : Fin 5 → ℝ)
    (hsum : ∑ i, α i = 1)
    (hord : α 3 ≤ α 2 ∧ α 2 ≤ α 1 ∧ α 1 ≤ α 0 ∧ α 3 ≤ α 4) :
    (∀ i j : Fin 5, i < j → α i + α j ≤ a) ↔
      α 0 + α 1 ≤ a ∧ 1 - a ≤ α 1 + α 2 + α 3 := by
  simp [Fin.sum_univ_succ] at hsum
  obtain ⟨h32, h21, h10, h34⟩ := hord
  constructor
  · intro hp
    have h04 := hp 0 4 (by decide)
    exact ⟨hp 0 1 (by decide), by linarith only [hsum, h04]⟩
  · rintro ⟨h01, h123⟩ i j hij
    have h04 : α 0 + α 4 ≤ a := by linarith only [hsum, h123]
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals dsimp; linarith only [h01, h04, h32, h21, h10, h34]

def sharpNormalizedRegion : Set (Fin 4 → ℝ) :=
  {z | (∀ i, (-2 : ℝ) ≤ z i) ∧ -2 ≤ -(∑ i, z i) ∧
    z 1 ≤ z 0 ∧ z 2 ≤ z 1 ∧ z 3 ≤ z 2 ∧
    z 3 ≤ -(∑ i, z i) ∧ z 0 + z 1 ≤ 1 ∧ -1 ≤ z 1 + z 2 + z 3}

def sharpAffine (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => (1 : ℝ) / 5 + (1361 : ℝ) / 100000 * z i

theorem sharpAffine_snoc (z : Fin 4 → ℝ) :
    (Fin.snoc (sharpAffine z) (1 - ∑ i, sharpAffine z i) : Fin 5 → ℝ) =
      fun i => (1 : ℝ) / 5 + (1361 : ℝ) / 100000 *
        (Fin.snoc z (-(∑ j, z j)) : Fin 5 → ℝ) i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, sharpAffine, Fin.sum_univ_four]
    ring
  · simp only [Fin.snoc_castSucc, sharpAffine]

theorem sharpAffine_mem_iff (z : Fin 4 → ℝ) :
    sharpAffine z ∈ sharpResidualRegion ↔ z ∈ sharpNormalizedRegion := by
  change sharpCoreClosed (Fin.snoc (sharpAffine z) (1 - ∑ i, sharpAffine z i)) ↔ _
  rw [sharpCoreClosed_iff]
  have heq (α : Fin 5 → ℝ) (hs : (∑ i, α i) = 1) :
      ((∀ i, (8639 : ℝ) / 50000 ≤ α i) ∧
        (α 3 ≤ α 2 ∧ α 2 ≤ α 1 ∧ α 1 ≤ α 0 ∧ α 3 ≤ α 4) ∧
        (∀ i j : Fin 5, i < j → α i + α j ≤ 41361 / 100000)) ↔
      ((∀ i, (8639 : ℝ) / 50000 ≤ α i) ∧
        α 3 ≤ α 2 ∧ α 2 ≤ α 1 ∧ α 1 ≤ α 0 ∧ α 3 ≤ α 4 ∧
        α 0 + α 1 ≤ 41361 / 100000 ∧ 58639 / 100000 ≤ α 1 + α 2 + α 3) := by
    constructor
    · rintro ⟨hl, ho, hpair⟩
      have h := (ordered_pair_caps_iff _ α hs ho).mp hpair
      norm_num at h
      exact ⟨hl, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2, h⟩
    · rintro ⟨hl, h32, h21, h10, h34, h01, h123⟩
      refine ⟨hl, ⟨h32, h21, h10, h34⟩, ?_⟩
      apply (ordered_pair_caps_iff _ α hs ⟨h32, h21, h10, h34⟩).mpr
      exact ⟨h01, by norm_num; exact h123⟩
  rw [heq _ (coefficient_sum_one (sharpAffine z)), sharpAffine_snoc]
  have hlo (r : ℝ) : (8639 : ℝ) / 50000 ≤ 1 / 5 + 1361 / 100000 * r ↔ -2 ≤ r := by
    constructor <;> intro h <;> linarith only [h]
  have hord (r s : ℝ) :
      (1 : ℝ) / 5 + 1361 / 100000 * r ≤ 1 / 5 + 1361 / 100000 * s ↔ r ≤ s := by
    constructor <;> intro h <;> linarith only [h]
  have hpair (r s : ℝ) :
      ((1 : ℝ) / 5 + 1361 / 100000 * r) + (1 / 5 + 1361 / 100000 * s) ≤
        41361 / 100000 ↔ r + s ≤ 1 := by
    constructor <;> intro h <;> linarith only [h]
  have htriple (r s t : ℝ) :
      (58639 : ℝ) / 100000 ≤ ((1 : ℝ) / 5 + 1361 / 100000 * r) +
        (1 / 5 + 1361 / 100000 * s) + (1 / 5 + 1361 / 100000 * t) ↔ -1 ≤ r + s + t := by
    constructor <;> intro h <;> linarith only [h]
  simp only [hlo, hord, hpair, htriple, sharpNormalizedRegion, Set.mem_ofPred_eq,
    Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]
  tauto

theorem sharpResidualRegion_eq_affine_image :
    sharpResidualRegion = sharpAffine '' sharpNormalizedRegion := by
  ext t
  constructor
  · intro ht
    let z : Fin 4 → ℝ := fun i => (t i - (1 : ℝ) / 5) / ((1361 : ℝ) / 100000)
    have hz : sharpAffine z = t := by
      funext i
      dsimp only [sharpAffine, z]
      ring
    refine ⟨z, (sharpAffine_mem_iff z).mp ?_, hz⟩
    rw [hz]
    exact ht
  · rintro ⟨z, hz, rfl⟩
    exact (sharpAffine_mem_iff z).mpr hz

theorem sharpNormalizedRegion_eq_simplices : sharpNormalizedRegion =
    ⋃ j : Fin 3, convexHull ℝ (Set.range fun k : Fin 5 =>
      minorantVertices1 (minorantSimplexIndices1 j k)) :=
  minorant_halfspaces1_eq_iUnion

theorem sharpNormalizedRegion_volume :
    volume sharpNormalizedRegion = (125 : ℝ≥0∞) / 864 :=
  minorant_halfspaces1_volume

theorem sharpResidualRegion_volume : volume sharpResidualRegion =
    ENNReal.ofReal (((1361 : ℝ) / 100000) ^ 4) * (125 / 864) := by
  rw [sharpResidualRegion_eq_affine_image]
  change volume ((fun z : Fin 4 → ℝ =>
    (fun _ => (1 / 5 : ℝ)) + (1361 / 100000 : ℝ) • z) '' sharpNormalizedRegion) = _
  rw [volume_affine_rescale_four _ _ (by norm_num), sharpNormalizedRegion_volume]

theorem setIntegral_sharpAffine (f : (Fin 4 → ℝ) → ℝ) (S : Set (Fin 4 → ℝ)) :
    (∫ t in sharpAffine '' S, f t) = ((1361 : ℝ) / 100000) ^ 4 *
      ∫ z in S, f (sharpAffine z) := by
  let b : Fin 4 → ℝ := fun _ => 1 / 5
  let c : ℝ := 1361 / 100000
  have hc : 0 < c := by norm_num [c]
  have himage : sharpAffine '' S = (fun y => b + y) '' (c • S) := by
    rw [← Set.image_smul, Set.image_image]
    rfl
  have ht := (measurePreserving_add_left (volume : Measure (Fin 4 → ℝ)) b).setIntegral_image_emb
    (MeasurableEquiv.addLeft b).measurableEmbedding f (c • S)
  have hm : (∫ z in S, f (sharpAffine z)) = (c ^ 4)⁻¹ *
      ∫ y in c • S, f (b + y) := by
    change (∫ z in S, f (b + c • z)) = (c ^ 4)⁻¹ * ∫ y in c • S, f (b + y)
    simpa only [Module.finrank_fin_fun, smul_eq_mul] using Measure.setIntegral_comp_smul_of_pos
      (volume : Measure (Fin 4 → ℝ)) (fun y => f (b + y)) S hc
  rw [himage, ht, hm]
  change _ = c ^ 4 * ((c ^ 4)⁻¹ * _)
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc.ne'), one_mul]

theorem sharpMass_eq_normalized_integral : sharpMass =
    6 * ((1361 : ℝ) / 100000) ^ 4 *
      ∫ z in sharpNormalizedRegion,
        (∏ i : Fin 5, ((1 : ℝ) / 5 + (1361 : ℝ) / 100000 *
          (Fin.snoc z (-(∑ j, z j)) : Fin 5 → ℝ) i))⁻¹ := by
  rw [sharpMass_eq_integral, sharpResidualRegion_eq_affine_image, setIntegral_sharpAffine]
  simp only [sharpDensity, sharpAffine_snoc, mul_assoc]

#print axioms sharpFirstMass_eq_integral
#print axioms sharpAffine_mem_iff
#print axioms sharpNormalizedRegion_eq_simplices
#print axioms sharpResidualRegion_volume
#print axioms sharpMass_eq_normalized_integral

end PrimeGap182Analytic.SharpMean
