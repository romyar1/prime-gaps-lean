import SourceDenseRows182
import SourcePairingMoments182

/-! Source support for actual finite prime configurations sampled by the
smooth profiles, and for all divisors of their products. -/

noncomputable section
open MeasureTheory PrimeGap186 PrimeGap182Analytic
open scoped BigOperators

namespace PrimeGap182

/-- Root, base face, enlarged face, and subtraction face, respectively. -/
def trialIntegerRadius : Fin 4 → ℚ :=
  ![trialRadius, trialBaseRadius, trialEnlargedRadius, trialSubtractionRadius]

def trialIntegerOuterRows (k : Fin 4) : List TrialSourceRow :=
  if k = 0 then trialApproxOuterRows else if k = 3 then [trialSubtractionSourceRow] else []

def trialIntegerInnerRows (k : Fin 4) : List TrialSourceRow :=
  if k = 1 then trialApproxOuterRows else if k = 2 then trialNewSourceRows else []

structure TrialIntegerSupport (k : Fin 4) (R : ℝ) (D : ℕ) : Prop where
  squarefree : Squarefree D
  radius : logSize R D ≤ (trialIntegerRadius k : ℝ)
  outer : ∀ row ∈ trialIntegerOuterRows k, TrialOuterOwnerBound row R D
  inner : ∀ row ∈ trialIntegerInnerRows k, TrialInnerOwnerBound row R D

set_option maxRecDepth 4096 in
theorem trialIntegerRows_data : ∀ k : Fin 4,
    (∀ row ∈ trialIntegerOuterRows k ++ trialIntegerInnerRows k,
      0 ≤ row.outerThreshold ∧ 0 ≤ row.innerThreshold ∧ 0 ≤ row.plateau) ∧
    (∀ row ∈ trialIntegerOuterRows k, trialMesh < row.activation) ∧
    (∀ row ∈ trialIntegerInnerRows k, trialMesh < row.activation) := by
  decide +kernel

theorem trialIntegerFace_radius (b : Fin 3) :
    trialIntegerRadius b.succ = trialApproxFaceRadius b := by fin_cases b <;> rfl

theorem trialIntegerFace_outer (b : Fin 3) :
    trialIntegerOuterRows b.succ = trialApproxFaceOuterRows b := by fin_cases b <;> rfl

theorem trialIntegerFace_inner (b : Fin 3) :
    trialIntegerInnerRows b.succ = trialApproxFaceInnerRows b := by fin_cases b <;> rfl

theorem trialIntegerSupport_of_bandDomain {d m : ℕ}
    (k : Fin 4) (W : ℕ) (R : ℝ) (hR : 1 < R) (a : Fin (m + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (hseed : a (0 : Fin (m + 1)).succ = (trialMesh : ℝ))
    (hlast : a (Fin.last (m + 1)) = selbergFragmentCap182)
    (s : Fin d → ℕ) (hsf : Squarefree (∏ i, s i))
    (hdiv : ∀ j, s j ∈ (∏ p ∈ fragmentPrimes W R selbergFragmentCap182, p).divisors)
    (hU : TrialBandSourceDomain (trialIntegerOuterRows k) (trialIntegerInnerRows k)
      (trialIntegerRadius k : ℝ) a (fun i => fragmentBandMasses a (primeLogConfiguration R (s i))))
    (D : ℕ) (hD : D ∣ ∏ i, s i) : TrialIntegerSupport k R D := by
  have hκ : 0 < selbergFragmentCap182 := by norm_num [selbergFragmentCap182, selbergRho182]
  have hfull : (∑ i, primeLogConfiguration R (s i)).restrict
      (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = ∑ i, primeLogConfiguration R (s i) := by
    rw [ha0, hlast]
    apply FiniteMeasure.toMeasure_injective
    simpa only [FiniteMeasure.restrict_measure_eq, FiniteMeasure.toMeasure_sum,
      Measure.restrict, map_sum] using Finset.sum_congr rfl
        (fun j (_ : j ∈ Finset.univ) => congrArg (fun c : FiniteMeasure ℝ => (c : Measure ℝ))
          (primeLogConfiguration_restrict_of_fragment_divisor W R selbergFragmentCap182
            hR hκ (s j) (hdiv j)))
  have hgap (j : Fin (m + 1)) (hj : 0 < a j.castSucc) :
      fragmentBandMasses a (∑ i, primeLogConfiguration R (s i)) j = 0 ∨
        a j.castSucc < fragmentBandMasses a (∑ i, primeLogConfiguration R (s i)) j := by
    simpa only [primeLogConfiguration_prod R Finset.univ s hsf, fragmentBandMasses] using
      primeLogConfiguration_restricted_mass_gap R (∏ i, s i) (a j.castSucc) (a j.succ) hj
  have hrows := trialBandSourceDomain_sound (trialIntegerOuterRows k) (trialIntegerInnerRows k)
    (trialIntegerRows_data k).2.1 (trialIntegerRows_data k).2.2 (trialIntegerRadius k : ℝ)
    a ha ha0 hseed (fun i => primeLogConfiguration R (s i)) hfull hgap hU
  have hDs := hsf.squarefree_of_dvd hD
  refine ⟨hDs, ?_, ?_, ?_⟩
  · have hm : logSize R (∏ i, s i) < (trialIntegerRadius k : ℝ) := by
      simpa only [trialTotalMass, primeLogConfiguration_total_mass d R hR s hsf] using hrows.2.2.1
    exact (Real.logb_le_logb_of_le hR (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hDs.ne_zero))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) hD))).trans hm.le
  · intro row hr
    have hg := (trialIntegerRows_data k).1 row (List.mem_append_left _ hr)
    exact trialOuterRowAllowed_divisor_owner row hg.1 hg.2.1 hg.2.2 R hR s hsf
      (hrows.1.1 row hr) D hD
  · intro row hr
    have hg := (trialIntegerRows_data k).1 row (List.mem_append_right _ hr)
    exact trialInnerRowAllowed_divisor_owner row hg.1 hg.2.1 hg.2.2 R hR s hsf
      (hrows.1.2 row hr) D hD

theorem TrialIntegerSupport.base_to_enlarged {R : ℝ} {D : ℕ} (h : TrialIntegerSupport 1 R D) :
    TrialIntegerSupport 2 R D := by
  refine ⟨h.squarefree, ?_, ?_, ?_⟩
  · exact h.radius.trans (by
      change (trialBaseRadius : ℝ) ≤ (trialEnlargedRadius : ℝ)
      norm_num [trialBaseRadius, trialEnlargedRadius])
  · simp only [trialIntegerOuterRows, Fin.reduceEq, ↓reduceIte, List.not_mem_nil, false_implies,
      implies_true]
  · intro row hr
    apply h.inner row
    change row ∈ trialApproxOuterRows
    exact List.mem_append_right _ hr

namespace TrialSmoothProfiles182

theorem root_integer_support (P : TrialSmoothProfiles182) (W : ℕ) (R : ℝ) (hR : 1 < R)
    (s : Fin 39 → ℕ) (hsf : Squarefree (∏ i, s i))
    (hdiv : ∀ j, s j ∈ (∏ p ∈ fragmentPrimes W R selbergFragmentCap182, p).divisors)
    (hf : P.F (fun i => fragmentBandMasses P.a (primeLogConfiguration R (s i))) ≠ 0)
    (D : ℕ) (hD : D ∣ ∏ i, s i) : TrialIntegerSupport 0 R D :=
  trialIntegerSupport_of_bandDomain 0 W R hR P.a P.strictMono P.zero P.seed P.last
    s hsf hdiv (P.F_support (subset_closure hf)) D hD

theorem face_integer_support (P : TrialSmoothProfiles182) (b : Fin 3) (i : Fin 39)
    (W : ℕ) (R : ℝ) (hR : 1 < R) (s : Fin 38 → ℕ) (hsf : Squarefree (∏ j, s j))
    (hdiv : ∀ j, s j ∈ (∏ p ∈ fragmentPrimes W R selbergFragmentCap182, p).divisors)
    (hf : P.bandMaskedFace b i (fun j => fragmentBandMasses P.a (primeLogConfiguration R (s j))) ≠ 0)
    (D : ℕ) (hD : D ∣ ∏ j, s j) : TrialIntegerSupport b.succ R D := by
  apply trialIntegerSupport_of_bandDomain b.succ W R hR P.a P.strictMono P.zero P.seed P.last
    s hsf hdiv _ D hD
  rw [trialIntegerFace_radius, trialIntegerFace_outer, trialIntegerFace_inner]
  exact P.bandMaskedFace_source b i _ hf

end TrialSmoothProfiles182

#print axioms trialIntegerRows_data
#print axioms trialIntegerSupport_of_bandDomain
#print axioms TrialIntegerSupport.base_to_enlarged
#print axioms TrialSmoothProfiles182.root_integer_support
#print axioms TrialSmoothProfiles182.face_integer_support

end PrimeGap182
