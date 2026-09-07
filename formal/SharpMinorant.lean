import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!+# The sharp five-prime defect and its marked-pair majorant

The definitions in this file are literal arithmetic objects from
`harman_type_ii_addback.md` and `sharp_exceptional_pair_weight.md`.
In particular the product is the integer n in [x,2x], and its logarithm
is not replaced by 1. These results do not assume a distribution theorem.
The eventual mean and progression estimates require separate proofs.
-/

noncomputable section
open scoped BigOperators

namespace PrimeGap182Analytic

def fivePairs : Finset (Fin 5 × Fin 5) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (1, 2),
   (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)}

theorem fivePairs_card : fivePairs.card = 10 := by decide

theorem mem_fivePairs (i j : Fin 5) : (i, j) ∈ fivePairs ↔ i < j := by
  fin_cases i <;> fin_cases j <;> decide

theorem sum_fivePairs (v : Fin 5 → ℝ) :
    (∑ ij ∈ fivePairs, (v ij.1 + v ij.2)) = 4 * ∑ i, v i := by
  simp [fivePairs, Fin.sum_univ_succ]
  ring

/-- Exact real-exponent geometry; only the inequality log_x(n) ≥ 1 is used. -/
theorem five_pair_bounds_geometry (a : ℝ) (v : Fin 5 → ℝ)
    (hsum : 1 ≤ ∑ i, v i)
    (hpair : ∀ i j : Fin 5, i < j → v i + v j < a) :
    ∀ i, 1 - 2 * a < v i ∧ v i < (4 * a - 1) / 3 := by
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
  fin_cases i <;> constructor <;> dsimp <;> linarith

def pairHinge (t s : ℝ) : ℝ :=
  (12 / 5 : ℝ) * max (s - t) 0 / (2 / 5 - t)

theorem pairHinge_nonneg (t s : ℝ) (ht : t < 2 / 5) :
    0 ≤ pairHinge t s := by
  unfold pairHinge
  exact div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) (by linarith)

/-- The factor 24 counts the actual ten unordered pairs, uniformly in t. -/
theorem five_pair_hinge_majorant (t : ℝ) (ht : t < 2 / 5)
    (v : Fin 5 → ℝ) (hsum : 1 ≤ ∑ i, v i) :
    24 ≤ ∑ ij ∈ fivePairs, pairHinge t (v ij.1 + v ij.2) := by
  have hraw : (∑ ij ∈ fivePairs, (v ij.1 + v ij.2 - t)) ≤
      ∑ ij ∈ fivePairs, max (v ij.1 + v ij.2 - t) 0 :=
    Finset.sum_le_sum fun _ _ => le_max_left _ _
  have hid : (∑ ij ∈ fivePairs, (v ij.1 + v ij.2 - t)) =
      4 * (∑ i, v i) - 10 * t := by
    rw [Finset.sum_sub_distrib, sum_fivePairs]
    simp [fivePairs_card]
  rw [hid] at hraw
  have hsummax : 4 - 10 * t ≤
      ∑ ij ∈ fivePairs, max (v ij.1 + v ij.2 - t) 0 := by
    linarith
  have hden : 0 < (2 / 5 : ℝ) - t := by linarith
  simp only [pairHinge, ← Finset.sum_div, ← Finset.mul_sum]
  apply (le_div_iff₀ hden).mpr
  linarith

/-- The support of the literal sharp exceptional defect, with distinct primes. -/
def SharpExceptional (x a : ℝ) (n : ℕ) : Prop :=
  ∃ p : Fin 5 → ℕ, Function.Injective p ∧
    (∀ i, (p i).Prime) ∧ (∏ i, p i) = n ∧
    ∀ i j : Fin 5, i < j → ((p i : ℝ) * (p j : ℝ)) < x ^ a

open Classical in
def sharpDefect (x a : ℝ) (n : ℕ) : ℝ :=
  if SharpExceptional x a n then 24 else 0

open Classical in
def sharpMinorant (x a : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then 1 else 0) - sharpDefect x a n

theorem sharpDefect_nonneg (x a : ℝ) (n : ℕ) : 0 ≤ sharpDefect x a n := by
  unfold sharpDefect
  split_ifs <;> norm_num

theorem sharpMinorant_le_prime (x a : ℝ) (n : ℕ) :
    sharpMinorant x a n ≤ if n.Prime then 1 else 0 := by
  exact sub_le_self _ (sharpDefect_nonneg x a n)

theorem five_prime_log_sum (x : ℝ) (hx : 1 < x) (p : Fin 5 → ℕ)
    (hp : ∀ i, (p i).Prime) {n : ℕ} (hprod : (∏ i, p i) = n)
    (hxn : x ≤ (n : ℝ)) :
    1 ≤ ∑ i, Real.logb x (p i : ℝ) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hn0 : 0 < (n : ℝ) := hx0.trans_le hxn
  have hlog : (∑ i, Real.logb x (p i : ℝ)) = Real.logb x (n : ℝ) := by
    rw [← hprod, Nat.cast_prod, Real.logb_prod]
    intro i _
    exact_mod_cast (hp i).ne_zero
  rw [hlog]
  apply (Real.le_logb_iff_rpow_le hx hn0).mpr
  simpa using hxn

theorem five_prime_log_pair (x a : ℝ) (hx : 1 < x) (p : Fin 5 → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hpair : ∀ i j : Fin 5, i < j → (p i : ℝ) * (p j : ℝ) < x ^ a) :
    ∀ i j : Fin 5, i < j →
      Real.logb x (p i : ℝ) + Real.logb x (p j : ℝ) < a := by
  intro i j hij
  have hi : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
  have hj : (0 : ℝ) < p j := by exact_mod_cast (hp j).pos
  rw [← Real.logb_mul hi.ne' hj.ne']
  exact (Real.logb_lt_iff_lt_rpow hx (mul_pos hi hj)).mpr (hpair i j hij)

theorem sharpExceptional_exponent_geometry (x a : ℝ) (hx : 1 < x)
    (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime) {n : ℕ}
    (hprod : (∏ i, p i) = n) (hxn : x ≤ (n : ℝ))
    (hpair : ∀ i j : Fin 5, i < j → (p i : ℝ) * (p j : ℝ) < x ^ a) :
    ∀ i, x ^ (1 - 2 * a) < (p i : ℝ) ∧
      (p i : ℝ) < x ^ ((4 * a - 1) / 3) := by
  have hg := five_pair_bounds_geometry a (fun i => Real.logb x (p i : ℝ))
    (five_prime_log_sum x hx p hp hprod hxn) (five_prime_log_pair x a hx p hp hpair)
  intro i
  have hi : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
  exact ⟨(Real.lt_logb_iff_rpow_lt hx hi).mp (hg i).1,
    (Real.logb_lt_iff_lt_rpow hx hi).mp (hg i).2⟩

theorem sharpExceptional_pair_weight (x t : ℝ) (hx : 1 < x) (ht : t < 2 / 5)
    (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime) {n : ℕ}
    (hprod : (∏ i, p i) = n) (hxn : x ≤ (n : ℝ)) :
    24 ≤ ∑ ij ∈ fivePairs,
      pairHinge t (Real.logb x ((p ij.1 : ℝ) * (p ij.2 : ℝ))) := by
  have heq (ij : Fin 5 × Fin 5) :
      Real.logb x ((p ij.1 : ℝ) * (p ij.2 : ℝ)) =
        Real.logb x (p ij.1 : ℝ) + Real.logb x (p ij.2 : ℝ) := by
    apply Real.logb_mul <;> exact_mod_cast (hp _).ne_zero
  simp_rw [heq]
  exact five_pair_hinge_majorant t ht (fun i => Real.logb x (p i : ℝ))
    (five_prime_log_sum x hx p hp hprod hxn)

open Classical in
/-- Unordered pairs of actual prime divisors in the sharp range. -/
def sharpPairCarrier (x a : ℝ) (n : ℕ) : Finset (Finset ℕ) :=
  (n.primeFactors.powersetCard 2).filter fun s =>
    (∀ p ∈ s, x ^ (1 - 2 * a) < (p : ℝ)) ∧
      ((∏ p ∈ s, p : ℕ) : ℝ) < x ^ a

def arithmeticPairWeight (x t : ℝ) (s : Finset ℕ) : ℝ :=
  pairHinge t (Real.logb x ((∏ p ∈ s, p : ℕ) : ℝ))

theorem prime_pair_image_injective (p : Fin 5 → ℕ) (hp : Function.Injective p) :
    Set.InjOn (fun ij : Fin 5 × Fin 5 => ({p ij.1, p ij.2} : Finset ℕ)) fivePairs := by
  intro ij hij kl hkl heq
  have hij' := (mem_fivePairs ij.1 ij.2).mp hij
  have hkl' := (mem_fivePairs kl.1 kl.2).mp hkl
  have hs : ({p ij.1, p ij.2} : Set ℕ) = {p kl.1, p kl.2} := by
    simpa only [Finset.coe_pair] using congrArg (fun s : Finset ℕ => (s : Set ℕ)) heq
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext (hp h1) (hp h2)
  · have h1' := hp h1
    have h2' := hp h2
    rw [h1', h2'] at hij'
    exact False.elim ((not_lt_of_gt hkl') hij')

theorem sharp_pair_image_subset (x a : ℝ) (hx : 1 < x)
    (p : Fin 5 → ℕ) (hinj : Function.Injective p)
    (hp : ∀ i, (p i).Prime) {n : ℕ}
    (hprod : (∏ i, p i) = n) (hxn : x ≤ (n : ℝ))
    (hpair : ∀ i j : Fin 5, i < j → (p i : ℝ) * (p j : ℝ) < x ^ a) :
    fivePairs.image (fun ij => ({p ij.1, p ij.2} : Finset ℕ)) ⊆ sharpPairCarrier x a n := by
  have hn0 : n ≠ 0 := by
    have : (0 : ℝ) < n := (lt_trans zero_lt_one hx).trans_le hxn
    exact_mod_cast this.ne'
  have hmem (i : Fin 5) : p i ∈ n.primeFactors := by
    apply (hp i).mem_primeFactors _ hn0
    rw [← hprod]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  have hg := sharpExceptional_exponent_geometry x a hx p hp hprod hxn hpair
  rintro s hs
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hs
  have hij' := (mem_fivePairs ij.1 ij.2).mp hij
  have hne : p ij.1 ≠ p ij.2 := fun h => (ne_of_lt hij') (hinj h)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hne⟩, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hmem ij.1
    · exact hmem ij.2
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact (hg ij.1).1
    · exact (hg ij.2).1
  · simpa only [Finset.prod_pair hne, Nat.cast_mul] using hpair ij.1 ij.2 hij'

/-- The paper's pointwise marked-pair majorant, summed over genuine
unordered prime divisors. There is no permutation or factor-two loss. -/
theorem sharpDefect_le_arithmetic_pair_majorant (x a t : ℝ) (hx : 1 < x)
    (ht : t < 2 / 5) (n : ℕ) (hxn : x ≤ (n : ℝ)) :
    sharpDefect x a n ≤ ∑ s ∈ sharpPairCarrier x a n, arithmeticPairWeight x t s := by
  classical
  by_cases hex : SharpExceptional x a n
  · obtain ⟨p, hinj, hp, hprod, hpair⟩ := hex
    have hsub := sharp_pair_image_subset x a hx p hinj hp hprod hxn hpair
    have himg :
        (∑ s ∈ fivePairs.image (fun ij => ({p ij.1, p ij.2} : Finset ℕ)),
          arithmeticPairWeight x t s) =
        ∑ ij ∈ fivePairs,
          pairHinge t (Real.logb x ((p ij.1 : ℝ) * (p ij.2 : ℝ))) := by
      rw [Finset.sum_image (prime_pair_image_injective p hinj)]
      apply Finset.sum_congr rfl
      intro ij hij
      have hne : p ij.1 ≠ p ij.2 :=
        fun h => (ne_of_lt ((mem_fivePairs ij.1 ij.2).mp hij)) (hinj h)
      simp only [arithmeticPairWeight, Finset.prod_pair hne, Nat.cast_mul]
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (f := arithmeticPairWeight x t) hsub
      (fun s _ _ => pairHinge_nonneg t _ ht)
    rw [himg] at hsum
    have htwentyfour := sharpExceptional_pair_weight x t hx ht p hp hprod hxn
    have hex' : SharpExceptional x a n := ⟨p, hinj, hp, hprod, hpair⟩
    simpa only [sharpDefect, ite_eq_left hex'] using htwentyfour.trans hsum
  · simp only [sharpDefect, ite_eq_right hex]
    exact Finset.sum_nonneg fun s _ => pairHinge_nonneg t _ ht

/-- Rough exceptional integers are coprime to all coefficient moduli whose
prime factors lie below the strict roughness threshold. -/
theorem sharpExceptional_coprime_of_prime_cap (x a : ℝ) (hx : 1 < x)
    (n q : ℕ) (hxn : x ≤ (n : ℝ)) (hex : SharpExceptional x a n)
    (hq : ∀ r : ℕ, r.Prime → r ∣ q → (r : ℝ) ≤ x ^ (1 - 2 * a)) :
    Nat.Coprime n q := by
  obtain ⟨p, hinj, hp, hprod, hpair⟩ := hex
  have hg := sharpExceptional_exponent_geometry x a hx p hp hprod hxn hpair
  rw [← hprod, Nat.coprime_prod_left_iff]
  intro i _
  apply (hp i).coprime_iff_not_dvd.mpr
  intro hdvd
  exact (not_le_of_gt (hg i).1) (hq (p i) (hp i) hdvd)

#print axioms five_pair_bounds_geometry
#print axioms five_pair_hinge_majorant
#print axioms sharpMinorant_le_prime
#print axioms sharpExceptional_exponent_geometry
#print axioms sharpExceptional_pair_weight
#print axioms prime_pair_image_injective
#print axioms sharpDefect_le_arithmetic_pair_majorant
#print axioms sharpExceptional_coprime_of_prime_cap

end PrimeGap182Analytic
