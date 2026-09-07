import IncidenceRawTaylor
import IncidenceSubpowerLoss
import IncidenceEnergyBudget

/-! Uniform budget for the literal remainder in
`incidenceRawSource_positive_taylor`. The Taylor cutoff is chosen only
from epsilon. Fixed constants and logarithmic profile bounds are then
absorbed uniformly over all supports of the stated polynomial height.
No source-distribution or remainder estimate is assumed here. -/

noncomputable section
namespace PrimeGap182Audit
open Filter
open scoped Topology

theorem incidenceTaylorRemainder_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 1000 + 48 * ε < 6 * ε * (J + 1 : ℕ) := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((1000 + 48 * ε) / (6 * ε))
  have h := (div_lt_iff₀ (by positivity : 0 < 6 * ε)).mp hJ
  refine ⟨J, ?_⟩
  push_cast
  nlinarith only [h, hε]

theorem incidenceTaylorRemainder_of_bounds
    (J : ℕ) (x ε Cj TM LM TD S Fcard Icard LN Dcount : ℝ)
    (hx : 1 ≤ x) (hx2 : 2 ≤ x)
    (hbudget : 1000 + 48 * ε < 6 * ε * (J + 1 : ℕ))
    (hCj : 0 ≤ Cj) (hCjx : Cj ≤ x) (hTM : 0 ≤ TM) (hTMx : TM ≤ x)
    (hLM : 0 ≤ LM) (hLMx : LM ≤ x) (hTD : 0 ≤ TD) (hS : 0 ≤ S)
    (hTS : TD * S ≤ x ^ (-3 * ε))
    (hF : 0 ≤ Fcard) (hFx : Fcard ≤ x ^ 100)
    (hI : 0 ≤ Icard) (hIx : Icard ≤ x ^ 100)
    (hLN : 0 ≤ LN) (hLNx : LN ≤ x)
    (hD : 0 ≤ Dcount) (hDx : Dcount ≤ x ^ 100) :
    2 * (Cj * (TM * LM) ^ 2 * (TD * S) ^ (J + 1)) ^ 2 *
        (Fcard * Icard * LN) ^ 2 * Dcount ^ 2 ≤ x ^ (-48 * ε) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  calc
    _ ≤ x * (x * (x * x) ^ 2 * (x ^ (-3 * ε)) ^ (J + 1)) ^ 2 *
        (x ^ 100 * x ^ 100 * x) ^ 2 * (x ^ 100) ^ 2 := by
      gcongr
    _ = x ^ 613 * ((x ^ (-3 * ε)) ^ (J + 1)) ^ 2 := by ring
    _ = x ^ ((613 : ℝ) - 6 * ε * (J + 1 : ℕ)) := by
      rw [← pow_mul, ← Real.rpow_natCast x 613, ← Real.rpow_mul_natCast hx0.le,
        ← Real.rpow_add hx0]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hbudget])

theorem incidenceTaylorRemainder_eventually
    (ε : ℝ) (hε : 0 < ε) (J : ℕ)
    (hbudget : 1000 + 48 * ε < 6 * ε * (J + 1 : ℕ))
    (Cj TM TD Kscale LMconst LNconst EM EN : ℝ)
    (hCj : 0 ≤ Cj) (hTM : 0 ≤ TM) (hTD : 0 ≤ TD)
    (_hKscale : 0 ≤ Kscale) (hLMconst : 0 ≤ LMconst) (hLNconst : 0 ≤ LNconst) :
    ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x ∧
      ∀ S Fcard Icard Dcount : ℝ,
      0 ≤ S → S ≤ Kscale * x ^ (-4 * ε) →
      0 ≤ Fcard → Fcard ≤ x ^ 100 →
      0 ≤ Icard → Icard ≤ x ^ 100 →
      0 ≤ Dcount → Dcount ≤ x ^ 100 →
      S ≤ 1 ∧
        2 * (Cj * (TM * (LMconst * (Real.log x) ^ EM)) ^ 2 *
          (TD * S) ^ (J + 1)) ^ 2 *
          (Fcard * Icard * (LNconst * (Real.log x) ^ EN)) ^ 2 * Dcount ^ 2 ≤
            x ^ (-48 * ε) := by
  filter_upwards [eventually_ge_atTop Cj, eventually_ge_atTop TM,
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop hε).eventually_ge_atTop Kscale,
    (tendsto_rpow_atTop hε).eventually_ge_atTop (TD * Kscale),
    incidenceLog_subpower LMconst EM 1 zero_lt_one,
    incidenceLog_subpower LNconst EN 1 zero_lt_one] with x hCjx hTMx hxe hx2 hK hTK hLMx hLNx
  have hx : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx2
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Real.rpow_one] at hLMx hLNx
  refine ⟨hxe, ?_⟩
  intro S Fcard Icard Dcount hS hSs hF hFx hI hIx hD hDx
  have hdecay : Kscale * x ^ (-4 * ε) ≤ x ^ (-3 * ε) := by
    calc
      _ ≤ x ^ ε * x ^ (-4 * ε) := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  have hTS : TD * S ≤ x ^ (-3 * ε) := by
    calc
      _ ≤ TD * (Kscale * x ^ (-4 * ε)) := mul_le_mul_of_nonneg_left hSs hTD
      _ = (TD * Kscale) * x ^ (-4 * ε) := by ring
      _ ≤ x ^ ε * x ^ (-4 * ε) := mul_le_mul_of_nonneg_right hTK (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  refine ⟨hSs.trans (hdecay.trans (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith))), ?_⟩
  exact incidenceTaylorRemainder_of_bounds J x ε Cj TM (LMconst * (Real.log x) ^ EM)
    TD S Fcard Icard (LNconst * (Real.log x) ^ EN) Dcount hx hx2 hbudget
    hCj hCjx hTM hTMx (mul_nonneg hLMconst (Real.rpow_nonneg hlog _)) hLMx hTD hS hTS
    hF hFx hI hIx (mul_nonneg hLNconst (Real.rpow_nonneg hlog _)) hLNx hD hDx

theorem incidenceTaylorRemainder_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 1000 + 48 * ε < 6 * ε * (J + 1 : ℕ) ∧
      ∀ Cj TM TD Kscale LMconst LNconst EM EN : ℝ,
      0 ≤ Cj → 0 ≤ TM → 0 ≤ TD → 0 ≤ Kscale → 0 ≤ LMconst → 0 ≤ LNconst →
      ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x ∧
        ∀ S Fcard Icard Dcount : ℝ,
        0 ≤ S → S ≤ Kscale * x ^ (-4 * ε) →
        0 ≤ Fcard → Fcard ≤ x ^ 100 →
        0 ≤ Icard → Icard ≤ x ^ 100 →
        0 ≤ Dcount → Dcount ≤ x ^ 100 →
        S ≤ 1 ∧
          2 * (Cj * (TM * (LMconst * (Real.log x) ^ EM)) ^ 2 *
            (TD * S) ^ (J + 1)) ^ 2 *
            (Fcard * Icard * (LNconst * (Real.log x) ^ EN)) ^ 2 * Dcount ^ 2 ≤
              x ^ (-48 * ε) := by
  obtain ⟨J, hJ⟩ := incidenceTaylorRemainder_cutoff ε hε
  exact ⟨J, hJ, fun Cj TM TD Kscale LMconst LNconst EM EN hCj hTM hTD hK hLM hLN =>
    incidenceTaylorRemainder_eventually ε hε J hJ Cj TM TD Kscale LMconst LNconst EM EN
      hCj hTM hTD hK hLM hLN⟩

#print axioms incidenceTaylorRemainder_cutoff
#print axioms incidenceTaylorRemainder_of_bounds
#print axioms incidenceTaylorRemainder_eventually
#print axioms incidenceTaylorRemainder_uniform

end PrimeGap182Audit
