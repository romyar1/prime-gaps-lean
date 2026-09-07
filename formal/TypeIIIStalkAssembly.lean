import TypeIIIFrobeniusTraceBounds
import TypeIIIFiniteAssembly

/-!
# Arithmetic assembly from explicit surface-stalk data

The physical and transformed stalks in this file are supplied data. Their
trace identity, eigenvalue bounds, dimensions, and support restrictions are
separate hypotheses. No assertion that they are realized by a particular
etale or perverse sheaf is made here. In particular, no Fourier norm estimate
is a hypothesis of the final stalk-based assembly theorems.

The physical boundary is estimated with its finite exceptional stalk set.
The final statements retain the original corrected subproducts, raw kernel,
positive Fourier convention, and finite/curve exceptional-bound definitions.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

/-- The dimension and aggregate physical-boundary constant. -/
def surfaceAssemblyCoreConstant (B Dphys Rphys : ℕ) : ℝ :=
  B * (1 + 2 * Dphys + Rphys)

theorem surfaceAssemblyCoreConstant_nonneg (B Dphys Rphys : ℕ) :
    0 ≤ surfaceAssemblyCoreConstant B Dphys Rphys := by
  unfold surfaceAssemblyCoreConstant
  positivity

theorem surfaceAssemblyCoreConstant_envelope (p B Dphys Rphys : ℕ)
    (E : ℝ) (hE : 1 ≤ E) :
    B * (p : ℝ) ^ 3 * E + B * (2 * (Dphys : ℝ) + Rphys) * (p : ℝ) ^ 3 ≤
      surfaceAssemblyCoreConstant B Dphys Rphys * (p : ℝ) ^ 3 * E := by
  calc
    _ ≤ B * (p : ℝ) ^ 3 * E +
        (B * (2 * (Dphys : ℝ) + Rphys) * (p : ℝ) ^ 3) * E := by
      exact add_le_add le_rfl (le_mul_of_one_le_right (by positivity) hE)
    _ = _ := by unfold surfaceAssemblyCoreConstant; ring

/-- Removing the physical intermediate-extension boundary from an exact
trace identity costs only the stated aggregate `p^3` error. -/
theorem restricted_fourier_norm_le_surface_trace
    (p : ℕ) [Fact p.Prime] (B Dphys Rphys : ℕ)
    (U Zphys : Finset (ZMod p × ZMod p))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p) (hZ : Zphys.card ≤ Rphys)
    (F : ZMod p → ZMod p → ℂ)
    (P Q : ZMod p → ZMod p → SurfaceStalk)
    (htrace : ∀ x y, (x, y) ∈ U → (P x y).trace = F x y)
    (hfourier : ∀ h k, (Q h k).trace = fourier₂ p (fun x y => (P x y).trace) h k)
    (hPB : ∀ x y, (P x y).dimensionsLe B)
    (hPeig : ∀ x y, (P x y).eigenvaluesLe ((p : ℝ) ^ 2)
      ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3))
    (hPminus : ∀ x y, (x, y) ∉ Zphys → (P x y).minusOne.dimension = 0)
    (hPzero : ∀ x y, (P x y).zero.dimension = 0) (h k : ZMod p) :
    ‖fourier₂ p (physicalRestriction p U F) h k‖ ≤
      ‖(Q h k).trace‖ + B * (2 * (Dphys : ℝ) + Rphys) * (p : ℝ) ^ 3 := by
  have hrestrict : physicalRestriction p U (fun x y => (P x y).trace) =
      physicalRestriction p U F := by
    funext x y
    by_cases hxy : (x, y) ∈ U
    · simp only [physicalRestriction, ite_eq_left hxy, htrace x y hxy]
    · simp only [physicalRestriction, ite_eq_right hxy]
  have hsplit : fourier₂ p (physicalRestriction p U F) h k =
      (Q h k).trace - physicalBoundaryFourier p (Finset.univ \ U)
        (fun x y => (P x y).trace) h k := by
    rw [hfourier h k,
      fourier₂_eq_restriction_add_boundary p U (fun x y => (P x y).trace), hrestrict,
      add_sub_cancel_right]
  have hboundary := physicalBoundaryFourier_norm_le_surface_weights p Dphys Rphys
    (Finset.univ \ U) Zphys hU hZ (fun x y => (P x y).trace) (B : ℝ)
    (by positivity) (fun z _ =>
      (P z.1 z.2).physical_trace_norm_le p B (z ∈ Zphys) (hPB _ _) (hPeig _ _)
        (hPminus _ _) (hPzero _ _)) h k
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hboundary)

/-- A finite transformed degree-minus-one support and vanishing degree zero
give the actual restricted Fourier estimate; no norm estimate is assumed. -/
theorem restricted_fourier_norm_le_finite_of_surface_stalks
    (p : ℕ) [Fact p.Prime] (B Dphys Rphys : ℕ)
    (U Zphys Zfourier : Finset (ZMod p × ZMod p))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p) (hZ : Zphys.card ≤ Rphys)
    (F : ZMod p → ZMod p → ℂ)
    (P Q : ZMod p → ZMod p → SurfaceStalk)
    (htrace : ∀ x y, (x, y) ∈ U → (P x y).trace = F x y)
    (hfourier : ∀ h k, (Q h k).trace = fourier₂ p (fun x y => (P x y).trace) h k)
    (hPB : ∀ x y, (P x y).dimensionsLe B)
    (hPeig : ∀ x y, (P x y).eigenvaluesLe ((p : ℝ) ^ 2)
      ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3))
    (hPminus : ∀ x y, (x, y) ∉ Zphys → (P x y).minusOne.dimension = 0)
    (hPzero : ∀ x y, (P x y).zero.dimension = 0)
    (hQB : ∀ h k, (Q h k).dimensionsLe B)
    (hQeig : ∀ h k, (Q h k).eigenvaluesLe ((p : ℝ) ^ 3)
      ((p : ℝ) ^ 3 * Real.sqrt p) ((p : ℝ) ^ 4))
    (hQminus : ∀ h k, (h, k) ∉ Zfourier → (Q h k).minusOne.dimension = 0)
    (hQzero : ∀ h k, (Q h k).zero.dimension = 0) (h k : ZMod p) :
    ‖fourier₂ p (physicalRestriction p U F) h k‖ ≤
      surfaceAssemblyCoreConstant B Dphys Rphys * (p : ℝ) ^ 3 *
        (1 + Real.sqrt p * if (h, k) ∈ Zfourier then 1 else 0) := by
  apply (restricted_fourier_norm_le_surface_trace p B Dphys Rphys U Zphys
    hU hZ F P Q htrace hfourier hPB hPeig hPminus hPzero h k).trans
  apply (add_le_add ((Q h k).fourier_trace_norm_le_finite p B
    ((h, k) ∈ Zfourier) (hQB _ _) (hQeig _ _) (hQminus _ _) (hQzero _ _)) le_rfl).trans
  exact surfaceAssemblyCoreConstant_envelope p B Dphys Rphys _
    (le_add_of_nonneg_right (by positivity))

/-- The curve alternative keeps the actual degree-zero origin contribution. -/
theorem restricted_fourier_norm_le_curve_of_surface_stalks
    (p : ℕ) [Fact p.Prime] (B Dphys Rphys : ℕ)
    (U Zphys : Finset (ZMod p × ZMod p))
    (A : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p) (hZ : Zphys.card ≤ Rphys)
    (F : ZMod p → ZMod p → ℂ)
    (P Q : ZMod p → ZMod p → SurfaceStalk)
    (htrace : ∀ x y, (x, y) ∈ U → (P x y).trace = F x y)
    (hfourier : ∀ h k, (Q h k).trace = fourier₂ p (fun x y => (P x y).trace) h k)
    (hPB : ∀ x y, (P x y).dimensionsLe B)
    (hPeig : ∀ x y, (P x y).eigenvaluesLe ((p : ℝ) ^ 2)
      ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3))
    (hPminus : ∀ x y, (x, y) ∉ Zphys → (P x y).minusOne.dimension = 0)
    (hPzero : ∀ x y, (P x y).zero.dimension = 0)
    (hQB : ∀ h k, (Q h k).dimensionsLe B)
    (hQeig : ∀ h k, (Q h k).eigenvaluesLe ((p : ℝ) ^ 3)
      ((p : ℝ) ^ 3 * Real.sqrt p) ((p : ℝ) ^ 4))
    (hQminus : ∀ h k, planeEval p A h k ≠ 0 → (Q h k).minusOne.dimension = 0)
    (hQzero : ∀ h k, ¬ (h = 0 ∧ k = 0) → (Q h k).zero.dimension = 0)
    (h k : ZMod p) :
    ‖fourier₂ p (physicalRestriction p U F) h k‖ ≤
      surfaceAssemblyCoreConstant B Dphys Rphys * (p : ℝ) ^ 3 *
        (1 + Real.sqrt p * (if planeEval p A h k = 0 then 1 else 0) +
          (p : ℝ) * if h = 0 ∧ k = 0 then 1 else 0) := by
  apply (restricted_fourier_norm_le_surface_trace p B Dphys Rphys U Zphys
    hU hZ F P Q htrace hfourier hPB hPeig hPminus hPzero h k).trans
  apply (add_le_add ((Q h k).fourier_trace_norm_le p B
    (planeEval p A h k = 0) (h = 0 ∧ k = 0) (hQB _ _) (hQeig _ _)
    (hQminus _ _) (hQzero _ _)) le_rfl).trans
  exact surfaceAssemblyCoreConstant_envelope p B Dphys Rphys _ (by
    have hs : 0 ≤ Real.sqrt p * (if planeEval p A h k = 0 then (1 : ℝ) else 0) :=
      by positivity
    have ho : 0 ≤ (p : ℝ) * (if h = 0 ∧ k = 0 then (1 : ℝ) else 0) := by positivity
    linarith)

/-- The product of the fifteen nonzero geometric equations retains their
actual zero loci, without choosing a replacement exceptional set. -/
def assembledCoreCurve (p : ℕ) [Fact p.Prime]
    (A : Finset (Fin 4) → MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) :
    MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)) :=
  ∏ S ∈ nonemptyCoreSubsets, A S

theorem assembledCoreCurve_ne_zero (p : ℕ) [Fact p.Prime]
    (A : Finset (Fin 4) → MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hA : ∀ S ∈ nonemptyCoreSubsets, A S ≠ 0) : assembledCoreCurve p A ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr hA

theorem assembledCoreCurve_totalDegree_le (p : ℕ) [Fact p.Prime]
    (A : Finset (Fin 4) → MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (D : ℕ) (hA : ∀ S ∈ nonemptyCoreSubsets, (A S).totalDegree ≤ D) :
    (assembledCoreCurve p A).totalDegree ≤ 15 * D := by
  calc
    _ ≤ ∑ S ∈ nonemptyCoreSubsets, (A S).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _S ∈ nonemptyCoreSubsets, D := Finset.sum_le_sum hA
    _ = _ := by simp only [Finset.sum_const, card_nonemptyCoreSubsets, smul_eq_mul]

theorem planeEval_assembledCoreCurve_eq_zero (p : ℕ) [Fact p.Prime]
    (A : Finset (Fin 4) → MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) (h k : ZMod p)
    (hA : planeEval p (A S) h k = 0) :
    planeEval p (assembledCoreCurve p A) h k = 0 := by
  simp only [assembledCoreCurve, planeEval, MvPolynomial.eval_prod]
  exact Finset.prod_eq_zero hS hA

/-- The raw four-cycle assembly for any nonnegative envelope at least one. -/
theorem fourCycle_fourier_norm_le_of_core_envelope
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime]
    (C : ℝ) (hC : 0 ≤ C) (Dphys : ℕ)
    (U : Finset (ZMod p × ZMod p))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (h k : ZMod p)
    (E : ℝ) (hE : 1 ≤ E)
    (hcore : ∀ S ∈ nonemptyCoreSubsets,
      ‖fourier₂ p (actualRestrictedCoreSubproduct p U α m m' n n' S) h k‖ ≤
        C * (p : ℝ) ^ 3 * E) :
    ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
      (81 + 175 * C + 13122 * Dphys) * (p : ℝ) ^ 3 * E := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (NeZero.one_le : 1 ≤ p)
  have hp₂ : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hp₁)]
  have hrestricted := actual_fourCycle_fourier_le_of_core_bounds p U α m m' n n' h k
    (C * (p : ℝ) ^ 3 * E) (mul_nonneg (by positivity) (le_trans zero_le_one hE)) hcore
  have hboundary := raw_fourCycle_physicalBoundary_norm_le hbase p Dphys
    (Finset.univ \ U) hU α m m' n n' hα hm hm' hn hn' h k
  rw [fourier₂_eq_restriction_add_boundary p U]
  apply (norm_add_le _ _).trans
  have hrestricted' :
      ‖fourier₂ p (physicalRestriction p U (fourCycle p α m m' n n')) h k‖ ≤
        81 * (p : ℝ) ^ 2 + 175 * (C * (p : ℝ) ^ 3 * E) := hrestricted
  apply (add_le_add hrestricted' hboundary).trans
  have hpE : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 * E :=
    hp₂.trans (le_mul_of_one_le_right (by positivity) hE)
  have hbE : 13122 * (Dphys : ℝ) * (p : ℝ) ^ 3 ≤
      13122 * (Dphys : ℝ) * (p : ℝ) ^ 3 * E :=
    le_mul_of_one_le_right (by positivity) hE
  nlinarith [mul_le_mul_of_nonneg_left hpE (by norm_num : (0 : ℝ) ≤ 81)]

/-- Curve counterpart of the existing finite-core assembly. The later
stalk theorem discharges the displayed arithmetic `hcore` premise. -/
theorem curveExceptionalFourierBound_of_actual_core_bounds
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime]
    (C : ℝ) (hC : 0 ≤ C) (Dphys Dcore : ℕ)
    (U : Finset (ZMod p × ZMod p))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0)
    (A : Finset (Fin 4) → MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hA : ∀ S ∈ nonemptyCoreSubsets, A S ≠ 0)
    (hD : ∀ S ∈ nonemptyCoreSubsets, (A S).totalDegree ≤ Dcore)
    (hcore : ∀ S ∈ nonemptyCoreSubsets, ∀ h k : ZMod p,
      ‖fourier₂ p (actualRestrictedCoreSubproduct p U α m m' n n' S) h k‖ ≤
        C * (p : ℝ) ^ 3 *
          (1 + Real.sqrt p * (if planeEval p (A S) h k = 0 then 1 else 0) +
            (p : ℝ) * if h = 0 ∧ k = 0 then 1 else 0)) :
    CurveExceptionalFourierBound p (81 + 175 * C + 13122 * Dphys)
      (15 * Dcore) α m m' n n' := by
  refine ⟨assembledCoreCurve p A, assembledCoreCurve_ne_zero p A hA,
    assembledCoreCurve_totalDegree_le p A Dcore hD, ?_⟩
  intro h k
  let E : ℝ := 1 + Real.sqrt p *
    (if planeEval p (assembledCoreCurve p A) h k = 0 then 1 else 0) +
      (p : ℝ) * if h = 0 ∧ k = 0 then 1 else 0
  have hE : 1 ≤ E := by
    dsimp only [E]
    have hs : 0 ≤ Real.sqrt p *
        (if planeEval p (assembledCoreCurve p A) h k = 0 then (1 : ℝ) else 0) := by
      positivity
    have ho : 0 ≤ (p : ℝ) * (if h = 0 ∧ k = 0 then (1 : ℝ) else 0) := by positivity
    linarith
  apply fourCycle_fourier_norm_le_of_core_envelope hbase p C hC Dphys U hU
    α m m' n n' hα hm hm' hn hn' h k E hE
  intro S hS
  apply (hcore S hS h k).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C * (p : ℝ) ^ 3)
  dsimp only [E]
  by_cases hAS : planeEval p (A S) h k = 0
  · have hall := planeEval_assembledCoreCurve_eq_zero p A S hS h k hAS
    simp only [ite_eq_left hAS, ite_eq_left hall, le_refl]
  · simp only [ite_eq_right hAS, mul_zero, add_zero]
    have hnonneg : 0 ≤ Real.sqrt p *
        (if planeEval p (assembledCoreCurve p A) h k = 0 then (1 : ℝ) else 0) := by
      positivity
    linarith

/-- Complete finite-exceptional assembly from the original corrected
subproduct trace identities and explicit stalk data. The distinct-index
geometry is precisely the obligation to supply the finite Fourier support
and vanishing degree zero; it is not inferred from a norm estimate. -/
theorem finiteExceptionalFourierBound_of_surface_stalks
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime]
    (B Dphys Rphys Dcore : ℕ) (U : Finset (ZMod p × ZMod p))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0)
    (P Q : Finset (Fin 4) → ZMod p → ZMod p → SurfaceStalk)
    (Zphys Zfourier : Finset (Fin 4) → Finset (ZMod p × ZMod p))
    (hZphys : ∀ S ∈ nonemptyCoreSubsets, (Zphys S).card ≤ Rphys)
    (hZfourier : ∀ S ∈ nonemptyCoreSubsets, (Zfourier S).card ≤ Dcore)
    (htrace : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, (x, y) ∈ U →
      (P S x y).trace = ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y)
    (hfourier : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      (Q S h k).trace = fourier₂ p (fun x y => (P S x y).trace) h k)
    (hPB : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, (P S x y).dimensionsLe B)
    (hPeig : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
      (P S x y).eigenvaluesLe ((p : ℝ) ^ 2)
        ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3))
    (hPminus : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
      (x, y) ∉ Zphys S → (P S x y).minusOne.dimension = 0)
    (hPzero : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, (P S x y).zero.dimension = 0)
    (hQB : ∀ S ∈ nonemptyCoreSubsets, ∀ h k, (Q S h k).dimensionsLe B)
    (hQeig : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      (Q S h k).eigenvaluesLe ((p : ℝ) ^ 3)
        ((p : ℝ) ^ 3 * Real.sqrt p) ((p : ℝ) ^ 4))
    (hQminus : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      (h, k) ∉ Zfourier S → (Q S h k).minusOne.dimension = 0)
    (hQzero : ∀ S ∈ nonemptyCoreSubsets, ∀ h k, (Q S h k).zero.dimension = 0) :
    FiniteExceptionalFourierBound p
      (81 + 175 * surfaceAssemblyCoreConstant B Dphys Rphys + 13122 * Dphys)
      (15 * Dcore) α m m' n n' := by
  apply finiteExceptionalFourierBound_of_actual_core_bounds hbase p
    (surfaceAssemblyCoreConstant B Dphys Rphys)
    (surfaceAssemblyCoreConstant_nonneg B Dphys Rphys) Dphys Dcore U hU
    α m m' n n' hα hm hm' hn hn' Zfourier hZfourier
  intro S hS h k
  have hrestriction : physicalRestriction p U
      (fun x y => ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y) =
      actualRestrictedCoreSubproduct p U α m m' n n' S := by
    funext x y
    rfl
  rw [← hrestriction]
  exact restricted_fourier_norm_le_finite_of_surface_stalks p B Dphys Rphys
      U (Zphys S) (Zfourier S) hU (hZphys S hS)
      (fun x y => ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y)
      (P S) (Q S) (htrace S hS) (hfourier S hS) (hPB S hS) (hPeig S hS)
      (hPminus S hS) (hPzero S hS) (hQB S hS) (hQeig S hS)
      (hQminus S hS) (hQzero S hS) h k

/-- Complete curve-exceptional assembly from explicit stalk data. The
transformed degree-zero origin support is retained exactly, and the final
exceptional polynomial is the product of the supplied nonzero equations. -/
theorem curveExceptionalFourierBound_of_surface_stalks
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime]
    (B Dphys Rphys Dcore : ℕ) (U : Finset (ZMod p × ZMod p))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0)
    (P Q : Finset (Fin 4) → ZMod p → ZMod p → SurfaceStalk)
    (Zphys : Finset (Fin 4) → Finset (ZMod p × ZMod p))
    (A : Finset (Fin 4) → MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hZphys : ∀ S ∈ nonemptyCoreSubsets, (Zphys S).card ≤ Rphys)
    (hA : ∀ S ∈ nonemptyCoreSubsets, A S ≠ 0)
    (hD : ∀ S ∈ nonemptyCoreSubsets, (A S).totalDegree ≤ Dcore)
    (htrace : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, (x, y) ∈ U →
      (P S x y).trace = ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y)
    (hfourier : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      (Q S h k).trace = fourier₂ p (fun x y => (P S x y).trace) h k)
    (hPB : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, (P S x y).dimensionsLe B)
    (hPeig : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
      (P S x y).eigenvaluesLe ((p : ℝ) ^ 2)
        ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3))
    (hPminus : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
      (x, y) ∉ Zphys S → (P S x y).minusOne.dimension = 0)
    (hPzero : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, (P S x y).zero.dimension = 0)
    (hQB : ∀ S ∈ nonemptyCoreSubsets, ∀ h k, (Q S h k).dimensionsLe B)
    (hQeig : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      (Q S h k).eigenvaluesLe ((p : ℝ) ^ 3)
        ((p : ℝ) ^ 3 * Real.sqrt p) ((p : ℝ) ^ 4))
    (hQminus : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      planeEval p (A S) h k ≠ 0 → (Q S h k).minusOne.dimension = 0)
    (hQzero : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      ¬ (h = 0 ∧ k = 0) → (Q S h k).zero.dimension = 0) :
    CurveExceptionalFourierBound p
      (81 + 175 * surfaceAssemblyCoreConstant B Dphys Rphys + 13122 * Dphys)
      (15 * Dcore) α m m' n n' := by
  apply curveExceptionalFourierBound_of_actual_core_bounds hbase p
    (surfaceAssemblyCoreConstant B Dphys Rphys)
    (surfaceAssemblyCoreConstant_nonneg B Dphys Rphys) Dphys Dcore U hU
    α m m' n n' hα hm hm' hn hn' A hA hD
  intro S hS h k
  have hrestriction : physicalRestriction p U
      (fun x y => ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y) =
      actualRestrictedCoreSubproduct p U α m m' n n' S := by
    funext x y
    rfl
  rw [← hrestriction]
  exact restricted_fourier_norm_le_curve_of_surface_stalks p B Dphys Rphys
      U (Zphys S) (A S) hU (hZphys S hS)
      (fun x y => ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y)
      (P S) (Q S) (htrace S hS) (hfourier S hS) (hPB S hS) (hPeig S hS)
      (hPminus S hS) (hPzero S hS) (hQB S hS) (hQeig S hS)
      (hQminus S hS) (hQzero S hS) h k

#print axioms surfaceAssemblyCoreConstant
#print axioms surfaceAssemblyCoreConstant_nonneg
#print axioms surfaceAssemblyCoreConstant_envelope
#print axioms restricted_fourier_norm_le_surface_trace
#print axioms restricted_fourier_norm_le_finite_of_surface_stalks
#print axioms restricted_fourier_norm_le_curve_of_surface_stalks
#print axioms assembledCoreCurve
#print axioms assembledCoreCurve_ne_zero
#print axioms assembledCoreCurve_totalDegree_le
#print axioms planeEval_assembledCoreCurve_eq_zero
#print axioms fourCycle_fourier_norm_le_of_core_envelope
#print axioms curveExceptionalFourierBound_of_actual_core_bounds
#print axioms finiteExceptionalFourierBound_of_surface_stalks
#print axioms curveExceptionalFourierBound_of_surface_stalks

end PrimeGap182.TypeIII
