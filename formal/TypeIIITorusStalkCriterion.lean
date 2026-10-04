import TypeIIIPublishedStalkCertificate

/-!
# Exact restoration on the physical unit torus

The original kernel is extended by zero on both coordinate axes. Hence
restricting its four-cycle to any set containing the unit torus changes
nothing. The raw boundary estimate, and therefore BaselineLocalInputs,
are unnecessary for certificates using this physical open set. The
intermediate-extension stalk boundary still uses the existing weight
argument; it is not asserted to vanish.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.TorusStalkCriterion

open PublishedStalkCertificate

theorem fourCycle_restriction_eq (p : ℕ) [Fact p.Prime]
    (U : Finset (ZMod p × ZMod p)) (hU : torusOpen p ⊆ U)
    (α m m' n n' : ZMod p) :
    physicalRestriction p U (fourCycle p α m m' n n') = fourCycle p α m m' n n' := by
  funext x y
  by_cases hxy : (x, y) ∈ U
  · simp only [physicalRestriction, ite_eq_left hxy]
  · have hnot : ¬ (x ≠ 0 ∧ y ≠ 0) := fun h =>
      hxy (hU ((mem_torusOpen p (x, y)).mpr h))
    by_cases hx : x = 0
    · simp [physicalRestriction, hx]
    · have hy : y = 0 := by tauto
      simp [physicalRestriction, hy]

/-- No raw boundary error is required. The older, larger constant is
retained so this result supplies the unchanged quantitative endpoint. -/
theorem fourCycle_fourier_norm_le_of_core_envelope
    (p : ℕ) [Fact p.Prime] (C : ℝ) (hC : 0 ≤ C) (Dphys : ℕ)
    (U : Finset (ZMod p × ZMod p)) (hU : torusOpen p ⊆ U)
    (α m m' n n' h k : ZMod p) (E : ℝ) (hE : 1 ≤ E)
    (hcore : ∀ S ∈ nonemptyCoreSubsets,
      ‖fourier₂ p (actualRestrictedCoreSubproduct p U α m m' n n' S) h k‖ ≤
        C * (p : ℝ) ^ 3 * E) :
    ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
      (81 + 175 * C + 13122 * Dphys) * (p : ℝ) ^ 3 * E := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (NeZero.one_le : 1 ≤ p)
  have hp₂ : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hp₁)]
  have hpE : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 * E :=
    hp₂.trans (le_mul_of_one_le_right (by positivity) hE)
  have hr := actual_fourCycle_fourier_le_of_core_bounds p U α m m' n n' h k
    (C * (p : ℝ) ^ 3 * E) (mul_nonneg (by positivity) (le_trans zero_le_one hE)) hcore
  change ‖fourier₂ p (physicalRestriction p U (fourCycle p α m m' n n')) h k‖ ≤ _ at hr
  rw [fourCycle_restriction_eq p U hU] at hr
  apply hr.trans
  have hboundary : 0 ≤ 13122 * (Dphys : ℝ) * (p : ℝ) ^ 3 * E :=
    mul_nonneg (by positivity) (le_trans zero_le_one hE)
  nlinarith [mul_le_mul_of_nonneg_left hpE (by norm_num : (0 : ℝ) ≤ 81)]

variable {p B Dphys Rphys Dcore : ℕ} [Fact p.Prime]
  {α m m' n n' : ZMod p}
  {c : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n'}

/-- The original finite exceptional inequality from the same stalk
certificate and support, when its physical open contains the unit torus. -/
theorem finiteFourierBound (support : TypeIIIFiniteStalkSupport c Dcore)
    (htorus : torusOpen p ⊆ c.physicalOpen) :
    FiniteExceptionalFourierBound p (uniformStalkConstant B Dphys Rphys)
      (15 * Dcore) α m m' n n' := by
  let Zall := assembledCoreExceptionalSet p support.exceptional
  refine ⟨Zall, assembledCoreExceptionalSet_card_le p support.exceptional Dcore
    support.exceptional_card, ?_⟩
  intro h k
  let E : ℝ := 1 + Real.sqrt p * if (h, k) ∈ Zall then 1 else 0
  have hE : 1 ≤ E := le_add_of_nonneg_right (by positivity)
  unfold uniformStalkConstant
  apply fourCycle_fourier_norm_le_of_core_envelope p
    (surfaceAssemblyCoreConstant B Dphys Rphys)
    (surfaceAssemblyCoreConstant_nonneg B Dphys Rphys) Dphys c.physicalOpen htorus
    α m m' n n' h k E hE
  intro S hS
  have hcore := restricted_fourier_norm_le_finite_of_surface_stalks p B Dphys Rphys
    c.physicalOpen (c.physicalExceptional S) (support.exceptional S)
    c.complement_card (c.physicalExceptional_card S hS)
    (fun x y => ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y)
    (c.physical S) (c.transformed S) (c.trace_on S hS) (c.fourier_trace S hS)
    (c.physical_dimensions S hS) (c.physical_eigenvaluesLe S hS)
    (c.physical_minusOne S hS) (c.physical_zero S hS)
    (c.transformed_dimensions S hS) (c.transformed_eigenvaluesLe S hS)
    (support.minusOne S hS) (support.zero S hS) h k
  apply hcore.trans
  apply mul_le_mul_of_nonneg_left _ (by
    exact mul_nonneg (surfaceAssemblyCoreConstant_nonneg B Dphys Rphys) (by positivity))
  by_cases hpair : (h, k) ∈ support.exceptional S
  · have hall : (h, k) ∈ Zall :=
      core_exceptional_subset_assembled p support.exceptional S hS hpair
    simp only [E, ite_eq_left hpair, ite_eq_left hall, le_refl]
  · simp only [ite_eq_right hpair, mul_zero, add_zero]
    exact hE

/-- The repeated-index alternative retains the same actual polynomial
and origin term. Only the raw coordinate-axis boundary is eliminated. -/
theorem curveFourierBound (support : TypeIIICurveStalkSupport c Dcore)
    (htorus : torusOpen p ⊆ c.physicalOpen) :
    CurveExceptionalFourierBound p (uniformStalkConstant B Dphys Rphys)
      (15 * Dcore) α m m' n n' := by
  refine ⟨assembledCoreCurve p support.equation,
    assembledCoreCurve_ne_zero p support.equation support.equation_ne_zero,
    assembledCoreCurve_totalDegree_le p support.equation Dcore support.equation_degree, ?_⟩
  intro h k
  let E : ℝ := 1 + Real.sqrt p *
    (if planeEval p (assembledCoreCurve p support.equation) h k = 0 then 1 else 0) +
      (p : ℝ) * if h = 0 ∧ k = 0 then 1 else 0
  have hE : 1 ≤ E := by
    dsimp only [E]
    have hs : 0 ≤ Real.sqrt p *
        (if planeEval p (assembledCoreCurve p support.equation) h k = 0 then (1 : ℝ) else 0) := by
      positivity
    have ho : 0 ≤ (p : ℝ) * (if h = 0 ∧ k = 0 then (1 : ℝ) else 0) := by positivity
    linarith
  unfold uniformStalkConstant
  apply fourCycle_fourier_norm_le_of_core_envelope p
    (surfaceAssemblyCoreConstant B Dphys Rphys)
    (surfaceAssemblyCoreConstant_nonneg B Dphys Rphys) Dphys c.physicalOpen htorus
    α m m' n n' h k E hE
  intro S hS
  have hcore := restricted_fourier_norm_le_curve_of_surface_stalks p B Dphys Rphys
    c.physicalOpen (c.physicalExceptional S) (support.equation S)
    c.complement_card (c.physicalExceptional_card S hS)
    (fun x y => ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y)
    (c.physical S) (c.transformed S) (c.trace_on S hS) (c.fourier_trace S hS)
    (c.physical_dimensions S hS) (c.physical_eigenvaluesLe S hS)
    (c.physical_minusOne S hS) (c.physical_zero S hS)
    (c.transformed_dimensions S hS) (c.transformed_eigenvaluesLe S hS)
    (support.minusOne S hS) (support.zero S hS) h k
  apply hcore.trans
  apply mul_le_mul_of_nonneg_left _ (by
    exact mul_nonneg (surfaceAssemblyCoreConstant_nonneg B Dphys Rphys) (by positivity))
  dsimp only [E]
  by_cases hAS : planeEval p (support.equation S) h k = 0
  · have hall := planeEval_assembledCoreCurve_eq_zero p support.equation S hS h k hAS
    simp only [ite_eq_left hAS, ite_eq_left hall, le_refl]
  · simp only [ite_eq_right hAS, mul_zero, add_zero]
    have hnonneg : 0 ≤ Real.sqrt p *
        (if planeEval p (assembledCoreCurve p support.equation) h k = 0 then (1 : ℝ) else 0) := by
      positivity
    linarith

end PrimeGap182.TypeIII.TorusStalkCriterion

#print axioms PrimeGap182.TypeIII.TorusStalkCriterion.fourCycle_restriction_eq
#print axioms PrimeGap182.TypeIII.TorusStalkCriterion.fourCycle_fourier_norm_le_of_core_envelope
#print axioms PrimeGap182.TypeIII.TorusStalkCriterion.finiteFourierBound
#print axioms PrimeGap182.TypeIII.TorusStalkCriterion.curveFourierBound
