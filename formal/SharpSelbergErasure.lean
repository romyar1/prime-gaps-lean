import Selberg39
import TailHybrid182

/-!
# Exact arithmetic erasure for the new sharp minorant

The root, its 38-coordinate erased array, and the sampled diagonal are actual
finite sums. Roughness removes the detected divisor exactly on prime and
sharp-exceptional inputs. The final theorem supplies the new coefficient cap
17277/100000 and roughness exponent 17278/100000; no distribution estimate
is assumed here.

The coordinate-erasure argument uses the checked arity adaptation of the
public 186 arithmetic identity. See Selberg39.lean for its source credits.
-/

noncomputable section
open scoped BigOperators
open PrimeGap182.Selberg

namespace PrimeGap182Analytic

open Classical in
def selbergRoot39 (y : (Fin 39 → ℕ) →₀ ℝ) (h : Fin 39 → ℕ) (n : ℕ) : ℝ :=
  ∑ d ∈ y.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors)),
    if ∀ j, d j ∣ n + h j then selbergCoefficient y d else 0

def selbergErasedArray39 (i : Fin 39) (y : (Fin 39 → ℕ) →₀ ℝ) :
    (Fin 38 → ℕ) →₀ ℝ :=
  y.sum fun r yr => Finsupp.single (fun j => r (i.succAbove j))
    (yr / ((r i).totient : ℝ))

open Classical in
def selbergErasedRoot39 (i : Fin 39) (y : (Fin 39 → ℕ) →₀ ℝ)
    (h : Fin 39 → ℕ) (n : ℕ) : ℝ :=
  let z := selbergErasedArray39 i y
  ∑ d ∈ z.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors)),
    if ∀ j, d j ∣ n + h (i.succAbove j) then selbergCoefficient z d else 0

theorem selbergRoot39_eq_erased_on_rough
    (i : Fin 39) (y : (Fin 39 → ℕ) →₀ ℝ) (h : Fin 39 → ℕ) (n : ℕ) (Y : ℝ)
    (hcap : ∀ d, selbergCoefficient y d ≠ 0 →
      ∀ p : ℕ, p.Prime → p ∣ d i → (p : ℝ) < Y)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n + h i → Y ≤ (p : ℝ)) :
    selbergRoot39 y h n = selbergErasedRoot39 i y h n := by
  classical
  unfold selbergRoot39 selbergErasedRoot39 selbergErasedArray39
  rw [← selberg_divisor_sum_weighted_erase i y h n]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hc : selbergCoefficient y d = 0
  · simp only [hc, ite_self]
  by_cases hdiv : ∀ j, d j ∣ n + h j
  · have hdi : d i = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      exact (not_lt_of_ge (hrough p hp (hpd.trans (hdiv i)))) (hcap d hc p hp hpd)
    simp only [hdiv, hdi, true_and]
  · simp only [hdiv, and_false, ite_false]

theorem sharpExceptional_prime_factor_lower (x a : ℝ) (hx : 1 < x)
    (n : ℕ) (hxn : x ≤ (n : ℝ)) (hex : SharpExceptional x a n)
    (q : ℕ) (hq : q.Prime) (hqn : q ∣ n) :
    x ^ (1 - 2 * a) < (q : ℝ) := by
  obtain ⟨p, _, hp, hprod, hpair⟩ := hex
  have hg := sharpExceptional_exponent_geometry x a hx p hp hprod hxn hpair
  rw [← hprod] at hqn
  obtain ⟨i, _, hqi⟩ := hq.prime.exists_mem_finset_dvd hqn
  have heq : q = p i := (Nat.prime_dvd_prime_iff_eq hq (hp i)).mp hqi
  simpa only [heq] using (hg i).1

/-- All three arithmetic weights have exactly the same erased root. -/
theorem selbergRoot39_sharp_erasure (x a : ℝ) (hx : 1 < x) (ha : 0 ≤ a)
    (i : Fin 39) (y : (Fin 39 → ℕ) →₀ ℝ) (h : Fin 39 → ℕ) (n : ℕ)
    (hxn : x ≤ ((n + h i : ℕ) : ℝ))
    (hcap : ∀ d, selbergCoefficient y d ≠ 0 →
      ∀ p : ℕ, p.Prime → p ∣ d i → (p : ℝ) < x ^ (1 - 2 * a)) :
    primeIndicator (n + h i) * selbergRoot39 y h n =
      primeIndicator (n + h i) * selbergErasedRoot39 i y h n ∧
    sharpDefect x a (n + h i) * selbergRoot39 y h n =
      sharpDefect x a (n + h i) * selbergErasedRoot39 i y h n ∧
    sharpMinorant x a (n + h i) * selbergRoot39 y h n =
      sharpMinorant x a (n + h i) * selbergErasedRoot39 i y h n := by
  classical
  have hP : primeIndicator (n + h i) * selbergRoot39 y h n =
      primeIndicator (n + h i) * selbergErasedRoot39 i y h n := by
    by_cases hp : (n + h i).Prime
    · apply congrArg (fun v : ℝ => primeIndicator (n + h i) * v)
      apply selbergRoot39_eq_erased_on_rough i y h n _ hcap
      intro p hpp hpd
      have heq : p = n + h i := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hpd
      rw [heq]
      exact (Real.rpow_le_self_of_one_le hx.le (by linarith : 1 - 2 * a ≤ 1)).trans hxn
    · simp only [primeIndicator, hp, ite_false, zero_mul]
  have hb : sharpDefect x a (n + h i) * selbergRoot39 y h n =
      sharpDefect x a (n + h i) * selbergErasedRoot39 i y h n := by
    by_cases hex : SharpExceptional x a (n + h i)
    · apply congrArg (fun v : ℝ => sharpDefect x a (n + h i) * v)
      apply selbergRoot39_eq_erased_on_rough i y h n _ hcap
      intro p hp hpd
      exact (sharpExceptional_prime_factor_lower x a hx _ hxn hex p hp hpd).le
    · simp only [sharpDefect, ite_eq_right hex, zero_mul]
  refine ⟨hP, hb, ?_⟩
  change (primeIndicator (n + h i) - sharpDefect x a (n + h i)) * _ =
    (primeIndicator (n + h i) - sharpDefect x a (n + h i)) * _
  rw [sub_mul, sub_mul, hP, hb]

open Classical in
def sampledDiagonal39 (W : ℕ) (R κ Z : ℝ) (f : (Fin 39 → ℕ) → ℝ) :
    (Fin 39 → ℕ) →₀ ℝ :=
  let q := ∏ p ∈ PrimeGap186.fragmentPrimes W R κ, p
  let T := (Fintype.piFinset (fun _ : Fin 39 => q.divisors)).filter
    fun r => Squarefree (∏ j, r j)
  ∑ r ∈ T, Finsupp.single r (f r / Z)

theorem sampledDiagonal39_prime_cap (x ρ ξ a : ℝ) (hx : 1 < x)
    (hρ : ρ ≠ 0) (hξ : ξ < 1 - 2 * a) (W : ℕ) (Z : ℝ)
    (f : (Fin 39 → ℕ) → ℝ) (i : Fin 39) (d : Fin 39 → ℕ)
    (hd : selbergCoefficient (sampledDiagonal39 W (x ^ ρ) (ξ / ρ) Z f) d ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpd : p ∣ d i) :
    (p : ℝ) < x ^ (1 - 2 * a) := by
  classical
  have hscale : (x ^ ρ) ^ (ξ / ρ) = x ^ ξ := by
    rw [← Real.rpow_mul (zero_le_one.trans hx.le)]
    congr 1
    field_simp
  have hpi {k : ℕ} (t : Fin k → Finset ℕ) (dec : DecidableEq (Fin k)) :
      @Fintype.piFinset (Fin k) dec _ (fun _ => ℕ) t =
        @Fintype.piFinset (Fin k) (Classical.typeDecidableEq _) _ (fun _ => ℕ) t := by
    ext r
    simp only [Fintype.mem_piFinset]
  have hfilter {k : ℕ} (s : Finset (Fin k → ℕ)) (p : (Fin k → ℕ) → Prop)
      (dec : DecidablePred p) :
      @Finset.filter _ p dec s =
        @Finset.filter _ p (fun r => Classical.propDecidable (p r)) s :=
    @Finset.filter_congr_decidable _ s p dec (fun r => Classical.propDecidable (p r))
  have hraw := selberg_sampled_coefficient_presieve W (x ^ ρ) (ξ / ρ) Z f d
  simp only [hpi, hfilter] at hraw
  simp only [sampledDiagonal39, hpi, hfilter] at hd
  have hpresieve := hraw hd
  have hpq : p ∣ ∏ q ∈ PrimeGap186.fragmentPrimes W (x ^ ρ) (ξ / ρ), q :=
    (hpd.trans (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).trans hpresieve.2.2.1
  obtain ⟨q, hq, hpq'⟩ := hp.prime.exists_mem_finset_dvd hpq
  have hqprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq'
  subst q
  have hpf : p ≤ ⌊(x ^ ρ) ^ (ξ / ρ)⌋₊ :=
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).1
  have hple : (p : ℝ) ≤ x ^ ξ := by
    rw [← hscale]
    exact (Nat.cast_le.mpr hpf).trans (Nat.floor_le (Real.rpow_nonneg
      (Real.rpow_nonneg (zero_le_one.trans hx.le) _) _))
  exact hple.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hx hξ)

theorem sampledDiagonal39_sharp182_erasure
    (x : ℝ) (hx : 1 < x) (W : ℕ) (Z : ℝ)
    (f : (Fin 39 → ℕ) → ℝ) (i : Fin 39) (h : Fin 39 → ℕ) (n : ℕ)
    (hxn : x ≤ ((n + h i : ℕ) : ℝ)) :
    let ρ : ℝ := 2624989 / 10000000
    let ξ : ℝ := 17277 / 100000
    let a : ℝ := 41361 / 100000
    let y := sampledDiagonal39 W (x ^ ρ) (ξ / ρ) Z f
    primeIndicator (n + h i) * selbergRoot39 y h n =
      primeIndicator (n + h i) * selbergErasedRoot39 i y h n ∧
    sharpDefect x a (n + h i) * selbergRoot39 y h n =
      sharpDefect x a (n + h i) * selbergErasedRoot39 i y h n ∧
    sharpMinorant x a (n + h i) * selbergRoot39 y h n =
      sharpMinorant x a (n + h i) * selbergErasedRoot39 i y h n := by
  intro ρ ξ a y
  apply selbergRoot39_sharp_erasure x a hx (by norm_num [a]) i y h n hxn
  intro d hd p hp hpd
  exact sampledDiagonal39_prime_cap x ρ ξ a hx (by norm_num [ρ])
    (by norm_num [ξ, a]) W Z f i d hd p hp hpd

#print axioms selbergRoot39_eq_erased_on_rough
#print axioms sharpExceptional_prime_factor_lower
#print axioms selbergRoot39_sharp_erasure
#print axioms sampledDiagonal39_prime_cap
#print axioms sampledDiagonal39_sharp182_erasure

end PrimeGap182Analytic
