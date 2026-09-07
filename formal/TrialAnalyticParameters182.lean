import SourceDenseData182

/-! Exact analytic parameter checks for every literal trial source row.
The rational tolerance supplies room for all subpower transfers and for
the new Type II/III estimates. These are numerical inequalities only;
they do not assert any distribution theorem. -/

namespace PrimeGap182

def trialAnalyticTolerance182 : ℚ := 1 / 10 ^ 12

def MinorantAnalyticGuards182 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (j : ℕ) («ω» δ τ : K) : Prop :=
  let u := «ω» + τ
  let v := δ + τ
  let σ := (1 / 2 : K) - 41361 / 100000 + 2 * τ
  let γlo := (1 / 2 : K) - σ
  let γhi := (9 / 20 : K)
  0 < «ω» ∧ 0 < δ ∧ 0 < τ ∧ τ ≤ 1 / 10 ^ 10 ∧
    u < 3 / 200 ∧ 0 < σ ∧ σ < 1 / 2 ∧
    1 / 4 + 7 * u + 2 * v < 34941 / 100000 - τ ∧
    1 / 30 + 56 / 15 * max u (1 / 100) + 4 / 15 * v < 2159 / 25000 - 2 * τ ∧
    68 * u + 14 * v < 1 ∧
    ((j = 1 ∧ 54 * u + 15 * v + 5 * σ < 1) ∨
      (j = 2 ∧ 56 * u + 16 * v + 4 * σ < 1) ∨
      (j = 3 ∧ 12 * u + 6 * v < γlo ∧ γhi < 1 / 2 - 2 * u ∧
        2 * γhi + 4 * u + 2 * v < 1 ∧ 16 * u + 7 * v < γlo ∧
        3 / 2 + 40 * u + 16 * v < 5 * γlo ∧
        1 / 4 + 14 * u + 4 * v < γhi))

instance {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (j : ℕ) («ω» δ τ : K) : Decidable (MinorantAnalyticGuards182 j «ω» δ τ) := by
  unfold MinorantAnalyticGuards182
  infer_instance

def PrimeAnalyticGuards182 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (j : ℕ) («ω» δ τ : K) : Prop :=
  let u := «ω» + τ
  let v := δ + τ
  let σ := (1 / 10 : K) + τ
  0 < «ω» ∧ 0 < δ ∧ 0 < τ ∧ u < 1 / 4 ∧ v < 1 / 4 + u ∧
    σ < 1 / 2 ∧ 2 * u < σ ∧
    (((j = 1 ∧ 54 * u + 15 * v + 5 * σ < 1) ∨
      (j = 2 ∧ 56 * u + 16 * v + 4 * σ < 1)) ∧
      68 * u + 14 * v < 1 ∧ 1 / 18 + 28 / 9 * u + 2 / 9 * v < σ ∨
      j = 3 ∧ 240 * u + 80 * v < 3)

instance {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (j : ℕ) («ω» δ τ : K) : Decidable (PrimeAnalyticGuards182 j «ω» δ τ) := by
  unfold PrimeAnalyticGuards182
  infer_instance

set_option maxRecDepth 4096 in
theorem trialSourceRows_minorant_analytic : ∀ ν : Fin 2, ∀ row ∈ trialSourceRows ν,
    MinorantAnalyticGuards182 row.order row.omega row.delta trialAnalyticTolerance182 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialOldSourceRows_prime_analytic : ∀ row ∈ trialOldSourceRows,
    PrimeAnalyticGuards182 row.order row.omega row.delta trialAnalyticTolerance182 := by
  decide +kernel

theorem trialCommonSource_analytic :
    MinorantAnalyticGuards182 2 trialCommonSourceOmega trialCommonSourceDelta trialAnalyticTolerance182 ∧
    PrimeAnalyticGuards182 2 trialCommonSourceOmega trialCommonSourceDelta trialAnalyticTolerance182 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialSubtractionSource_analytic :
    MinorantAnalyticGuards182 trialSubtractionSourceRow.order trialSubtractionSourceRow.omega
      trialSubtractionSourceRow.delta trialAnalyticTolerance182 ∧
    PrimeAnalyticGuards182 trialSubtractionSourceRow.order trialSubtractionSourceRow.omega
      trialSubtractionSourceRow.delta trialAnalyticTolerance182 := by
  decide +kernel

theorem MinorantAnalyticGuards182.cast_real {j : ℕ} {«ω» δ τ : ℚ}
    (h : MinorantAnalyticGuards182 j «ω» δ τ) :
    MinorantAnalyticGuards182 j («ω» : ℝ) (δ : ℝ) (τ : ℝ) := by
  unfold MinorantAnalyticGuards182 at h ⊢
  dsimp only at h ⊢
  rify at h ⊢
  exact h

theorem PrimeAnalyticGuards182.cast_real {j : ℕ} {«ω» δ τ : ℚ}
    (h : PrimeAnalyticGuards182 j «ω» δ τ) :
    PrimeAnalyticGuards182 j («ω» : ℝ) (δ : ℝ) (τ : ℝ) := by
  unfold PrimeAnalyticGuards182 at h ⊢
  dsimp only at h ⊢
  rify at h ⊢
  exact h

#print axioms trialSourceRows_minorant_analytic
#print axioms trialOldSourceRows_prime_analytic
#print axioms trialCommonSource_analytic
#print axioms trialSubtractionSource_analytic
#print axioms MinorantAnalyticGuards182.cast_real

end PrimeGap182
