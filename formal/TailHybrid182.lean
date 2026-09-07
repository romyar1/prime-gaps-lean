import SharpMinorant
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# Tail subtraction in the sharp-minorant first moment

The finite identity retains the canonical subtraction profile C independently
of the base profile B. Its exceptional square is exactly (A-C)^2. The signed
minorant and defect below are the actual arithmetic functions in SharpMinorant.

The asymptotic theorem is an assembly lemma: its seven moment estimates are
explicit premises to be supplied by the distribution and Selberg arguments.
It proves no such estimate by definition or by introducing an axiom.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace PrimeGap182Analytic

open Classical in
def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

theorem primeIndicator_nonneg (n : ℕ) : 0 ≤ primeIndicator n := by
  unfold primeIndicator
  split_ifs <;> norm_num

def tailCompletion (P b A B C H η : ℝ) : ℝ :=
  P * (2 * A * B - B ^ 2) +
    2 * (P - b) * (A - B) * H + 2 * b * (C - B) * H -
    P * H ^ 2 - η * b * (A - C) ^ 2 - η⁻¹ * b * H ^ 2

/-- Both squares are exact; no mixed term has been discarded. -/
theorem tailCompletion_identity (P b A B C H η : ℝ) (hη : η ≠ 0) :
    P * A ^ 2 - tailCompletion P b A B C H η =
      P * (A - B - H) ^ 2 + (b / η) * (η * (A - C) + H) ^ 2 := by
  unfold tailCompletion
  field_simp
  ring

theorem tailCompletion_le (P b A B C H η : ℝ)
    (hP : 0 ≤ P) (hb : 0 ≤ b) (hη : 0 < η) :
    tailCompletion P b A B C H η ≤ P * A ^ 2 := by
  rw [← sub_nonneg, tailCompletion_identity P b A B C H η hη.ne']
  exact add_nonneg (mul_nonneg hP (sq_nonneg _))
    (mul_nonneg (div_nonneg hb hη.le) (sq_nonneg _))

/-- Actual finite arithmetic first-moment inequality with a larger subtraction
array C. The correction H and all profiles may have either sign. -/
theorem sharp_tail_finite_first_moment (𝓗 s : Finset ℕ) (x a t η : ℝ)
    (hη : 0 < η) (A : ℕ → ℝ) (B C H : ℕ → ℕ → ℝ) :
    (∑ n ∈ s,
      ((∑ h ∈ 𝓗,
        tailCompletion (primeIndicator (n + h)) (sharpDefect x a (n + h))
          (A n) (B h n) (C h n) (t * H h n) η) - A n ^ 2)) ≤
      ∑ n ∈ s,
        (((𝓗.filter (fun h => (n + h).Prime)).card : ℝ) - 1) * A n ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro n _
  have hs := Finset.sum_le_sum (s := 𝓗) fun h _ =>
    tailCompletion_le (primeIndicator (n + h)) (sharpDefect x a (n + h))
      (A n) (B h n) (C h n) (t * H h n) η
      (primeIndicator_nonneg _) (sharpDefect_nonneg _ _ _) hη
  calc
    _ ≤ (∑ h ∈ 𝓗, primeIndicator (n + h) * A n ^ 2) - A n ^ 2 :=
      sub_le_sub_right hs _
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [primeIndicator, Finset.sum_boole, sub_mul, one_mul]

/-- The scalar choice uses the upper deficit only in the penalty. The two
mixed pairings must still use the same true deficit, which cancels exactly. -/
theorem tail_hybrid_coefficient_identity (ℓ κbar κ J : ℝ)
    (hℓ : ℓ ≠ 0) (hℓ1 : 1 - ℓ ≠ 0) (hκ : κbar ≠ 0) :
    let t := 1 - ℓ
    let η := κbar * (1 / ℓ - 1)
    2 * t * ((1 - κ) * J) + 2 * t * (κ * J) -
      t ^ 2 * J - η⁻¹ * t ^ 2 * (κbar * J) = (1 - ℓ) * J := by
  dsimp only
  have hη : κbar * (1 / ℓ - 1) ≠ 0 := by
    apply mul_ne_zero hκ
    rw [div_sub_one hℓ]
    exact div_ne_zero hℓ1 hℓ
  field_simp
  ring

/-- Assemble actual sharp-minorant moments. The exceptional moment EX is
formed after subtracting C, while MC pairs C-B only with the correction H.
There is no C-by-C distribution premise. -/
theorem sharp_tail_eventually_positive_first_moment
    (𝓗 : Finset ℕ) (a ρ ℓ κbar κ I J0 Jplus E : ℝ)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hκbar : 0 < κbar)
    (s : ℝ → Finset ℕ) (A : ℝ → ℕ → ℝ)
    (B C H : ℝ → ℕ → ℕ → ℝ) (Z : ℝ → ℝ) :
    let P := primeIndicator
    let b := fun x n => sharpDefect x a n
    let r := fun x n => sharpMinorant x a n
    let O := fun x => ∑ n ∈ s x, A x n ^ 2
    let L0 := fun x => ∑ n ∈ s x, ∑ h ∈ 𝓗,
      P (n + h) * (2 * A x n * B x h n - B x h n ^ 2)
    let MR := fun x => ∑ n ∈ s x, ∑ h ∈ 𝓗,
      r x (n + h) * (A x n - B x h n) * H x h n
    let MC := fun x => ∑ n ∈ s x, ∑ h ∈ 𝓗,
      b x (n + h) * (C x h n - B x h n) * H x h n
    let SP := fun x => ∑ n ∈ s x, ∑ h ∈ 𝓗,
      P (n + h) * H x h n ^ 2
    let SB := fun x => ∑ n ∈ s x, ∑ h ∈ 𝓗,
      b x (n + h) * H x h n ^ 2
    let EX := fun x => ∑ n ∈ s x, ∑ h ∈ 𝓗,
      b x (n + h) * (A x n - C x h n) ^ 2
    (∀ᶠ x : ℝ in atTop, 0 < Z x) →
    0 < ρ * (J0 + (1 - ℓ) * Jplus - κbar * (1 / ℓ - 1) * E) - I →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      O x ≤ (I + ε) * Z x ∧
      (ρ * J0 - ε) * Z x ≤ L0 x ∧
      (ρ * (1 - κ) * Jplus - ε) * Z x ≤ MR x ∧
      (ρ * κ * Jplus - ε) * Z x ≤ MC x ∧
      SP x ≤ (ρ * Jplus + ε) * Z x ∧
      SB x ≤ (ρ * κbar * Jplus + ε) * Z x ∧
      EX x ≤ (ρ * E + ε) * Z x) →
    ∀ᶠ x : ℝ in atTop,
      0 < ∑ n ∈ s x,
        (((𝓗.filter (fun h => (n + h).Prime)).card : ℝ) - 1) * A x n ^ 2 := by
  classical
  intro P b r O L0 MR MC SP SB EX hZ hmargin hmoments
  let t : ℝ := 1 - ℓ
  let η : ℝ := κbar * (1 / ℓ - 1)
  let β : ℝ := η⁻¹ * t ^ 2
  have ht : 0 < t := sub_pos.mpr hℓ1
  have hη : 0 < η := by
    apply mul_pos hκbar
    apply sub_pos.mpr
    exact (lt_div_iff₀ hℓ).mpr (by simpa using hℓ1)
  have hβ : 0 ≤ β := mul_nonneg (inv_nonneg.mpr hη.le) (sq_nonneg t)
  let τ : ℝ := 2 + 4 * t + t ^ 2 + β + η
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  let M : ℝ := ρ * (J0 + t * Jplus - η * E) - I
  have hM : 0 < M := hmargin
  let ε : ℝ := M / (2 * τ)
  have hε : 0 < ε := div_pos hM (mul_pos zero_lt_two hτ)
  have hsmall : M - ε * τ = M / 2 := by
    dsimp only [ε]
    field_simp
    ring
  have hcoef :
      2 * t * ((1 - κ) * Jplus) + 2 * t * (κ * Jplus) -
        t ^ 2 * Jplus - β * (κbar * Jplus) = t * Jplus :=
    tail_hybrid_coefficient_identity ℓ κbar κ Jplus hℓ.ne' ht.ne' hκbar.ne'
  filter_upwards [hZ, hmoments ε hε] with x hxZ hx
  rcases hx with ⟨hO, hL0, hMR, hMC, hSP, hSB, hEX⟩
  let L := L0 x + 2 * t * MR x + 2 * t * MC x -
    (t ^ 2 * SP x + β * SB x + η * EX x + O x)
  have hcombined := sub_le_sub
    (add_le_add
      (add_le_add hL0 (mul_le_mul_of_nonneg_left hMR (mul_nonneg zero_le_two ht.le)))
      (mul_le_mul_of_nonneg_left hMC (mul_nonneg zero_le_two ht.le)))
    (add_le_add
      (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hSP (sq_nonneg t))
          (mul_le_mul_of_nonneg_left hSB hβ))
        (mul_le_mul_of_nonneg_left hEX hη.le)) hO)
  have hmain : (M - ε * τ) * Z x ≤ L := by
    calc
      (M - ε * τ) * Z x =
          ((ρ * J0 - ε) * Z x +
            2 * t * ((ρ * (1 - κ) * Jplus - ε) * Z x) +
            2 * t * ((ρ * κ * Jplus - ε) * Z x)) -
          (t ^ 2 * ((ρ * Jplus + ε) * Z x) +
            β * ((ρ * κbar * Jplus + ε) * Z x) +
            η * ((ρ * E + ε) * Z x) + (I + ε) * Z x) := by
        dsimp only [M, τ]
        nlinarith only [congrArg (fun v : ℝ => ρ * v * Z x) hcoef]
      _ ≤ L := hcombined
  have hL : 0 < L := by
    rw [hsmall] at hmain
    exact (mul_pos (half_pos hM) hxZ).trans_le hmain
  have hpoint (n h : ℕ) :
      tailCompletion (P (n + h)) (b x (n + h))
          (A x n) (B x h n) (C x h n) (t * H x h n) η =
        P (n + h) * (2 * A x n * B x h n - B x h n ^ 2) +
          (2 * t) * (r x (n + h) * (A x n - B x h n) * H x h n) +
          (2 * t) * (b x (n + h) * (C x h n - B x h n) * H x h n) -
          t ^ 2 * (P (n + h) * H x h n ^ 2) -
          β * (b x (n + h) * H x h n ^ 2) -
          η * (b x (n + h) * (A x n - C x h n) ^ 2) := by
    dsimp only [tailCompletion, β, r, sharpMinorant, P, primeIndicator, b]
    ring
  have hsum :
      (∑ n ∈ s x, ((∑ h ∈ 𝓗,
        tailCompletion (P (n + h)) (b x (n + h))
          (A x n) (B x h n) (C x h n) (t * H x h n) η) - A x n ^ 2)) = L := by
    simp_rw [hpoint]
    dsimp only [L, L0, MR, MC, SP, SB, EX, O]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hfinite := sharp_tail_finite_first_moment 𝓗 (s x) x a t η hη
    (A x) (B x) (C x) (H x)
  change (∑ n ∈ s x, ((∑ h ∈ 𝓗,
    tailCompletion (P (n + h)) (b x (n + h))
      (A x n) (B x h n) (C x h n) (t * H x h n) η) - A x n ^ 2)) ≤ _ at hfinite
  rw [hsum] at hfinite
  exact hL.trans_le hfinite

#print axioms tailCompletion_identity
#print axioms tailCompletion_le
#print axioms sharp_tail_finite_first_moment
#print axioms tail_hybrid_coefficient_identity
#print axioms sharp_tail_eventually_positive_first_moment

end PrimeGap182Analytic
