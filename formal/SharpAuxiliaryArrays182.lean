import MixedAuxiliaryArithmetic182
import SharpSelbergErasure
import SharpRadialMajorant182

/-!
Explicit sharp auxiliary arrays, their proved energy limits and exact values
on the sharp exceptional support. The final pointwise theorem uses these
arrays for every pair bin and radial block, retaining the full signed sum.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic

def sharpAuxiliarySet (H : Finset ℕ) (κ x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊x ^ κ⌋₊).filter fun a => Squarefree a ∧ Nat.Coprime a (presievingModulus H x)

def sharpAuxiliaryNormalizer (H : Finset ℕ) (κ x : ℝ) : ℝ :=
  ∑ a ∈ sharpAuxiliarySet H κ x, 1 / (a.totient : ℝ)

def sharpAuxiliaryArray (H : Finset ℕ) (κ x : ℝ) : (Fin 1 → ℕ) →₀ ℝ :=
  ∑ a ∈ sharpAuxiliarySet H κ x,
    Finsupp.single (fun _ : Fin 1 => a) (1 / sharpAuxiliaryNormalizer H κ x)

theorem sharpAuxiliaryArray_energy_tendsto (H : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun x => fragmentNormalization (presievingModulus H x) x *
      diagonalHarmonic (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ))
        (sharpAuxiliaryArray H κ x)) atTop (nhds (1 / κ)) := by
  have hf := PrimeGap182.Selberg.sharp_auxiliary_family H κ (κ + 1) hκ (lt_add_one κ)
  simpa only [sharpAuxiliaryArray, sharpAuxiliaryNormalizer, sharpAuxiliarySet,
    diagonalHarmonic] using hf.1

theorem sharpAuxiliaryArray_bounds (H : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ x : ℝ in atTop,
      1 < x ∧ 0 < fragmentNormalization (presievingModulus H x) x ∧
        (∀ t, |sharpAuxiliaryArray H κ x t| ≤
          N / fragmentNormalization (presievingModulus H x) x) ∧
        ∀ t ∈ (sharpAuxiliaryArray H κ x).support,
          t 0 ∈ (∏ p ∈ fragmentPrimes (presievingModulus H x) x κ, p).divisors ∧
            (t 0 : ℝ) ≤ x ^ κ := by
  have hf := PrimeGap182.Selberg.sharp_auxiliary_family H κ (κ + 1) hκ (lt_add_one κ)
  simpa only [sharpAuxiliaryArray, sharpAuxiliaryNormalizer, sharpAuxiliarySet] using hf.2.1

theorem sharpAuxiliaryArray_root_one (H : Finset ℕ) (κ ξ : ℝ)
    (hκ : 0 < κ) (hκξ : κ < ξ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      (∀ p : ℕ, p.Prime → p ∣ n → x ^ ξ ≤ (p : ℝ)) →
        sampledSelbergRoot (sharpAuxiliaryArray H κ x) (fun _ => n) = 1 := by
  have hf := PrimeGap182.Selberg.sharp_auxiliary_family H κ ξ hκ hκξ
  simpa only [sampledSelbergRoot_one, sharpAuxiliaryArray, sharpAuxiliaryNormalizer,
    sharpAuxiliarySet, finPiFinset_eq_classical] using hf.2.2

theorem sharpAuxiliaryArray_root_one_on_exceptional (H : Finset ℕ) (κ a : ℝ)
    (hκ : 0 < κ) (hκa : κ < 1 - 2 * a) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x ≤ (n : ℝ) → SharpExceptional x a n →
      sampledSelbergRoot (sharpAuxiliaryArray H κ x) (fun _ => n) = 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    sharpAuxiliaryArray_root_one H κ (1 - 2 * a) hκ hκa] with x hx hu
  intro n hxn hex
  apply hu n
  intro p hp hpn
  exact (sharpExceptional_prime_factor_lower x a hx n hxn hex p hp hpn).le

theorem sharp182_auxiliary_radial_units {J : Type*} [Fintype J]
    (H : Finset ℕ) (ζ : Fin 1024 → J → ℝ)
    (hζ : ∀ j b, 0 < ζ j b ∧ ζ j b < 8639 / 50000) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x ≤ (n : ℝ) →
      SharpExceptional x (41361 / 100000) n → ∀ j b,
        sampledSelbergRoot (sharpAuxiliaryArray H (ζ j b) x) (fun _ => n) = 1 := by
  have hj : ∀ j b, ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x ≤ (n : ℝ) →
      SharpExceptional x (41361 / 100000) n →
        sampledSelbergRoot (sharpAuxiliaryArray H (ζ j b) x) (fun _ => n) = 1 := by
    intro j b
    apply sharpAuxiliaryArray_root_one_on_exceptional H (ζ j b) (41361 / 100000) (hζ j b).1
    have h := (hζ j b).2
    norm_num at h ⊢
    exact h
  have hall : ∀ᶠ x : ℝ in atTop, ∀ j b, ∀ n : ℕ, x ≤ (n : ℝ) →
      SharpExceptional x (41361 / 100000) n →
        sampledSelbergRoot (sharpAuxiliaryArray H (ζ j b) x) (fun _ => n) = 1 :=
    eventually_all.mpr fun j => eventually_all.mpr fun b => hj j b
  filter_upwards [hall] with x hx
  intro n hn hex j b
  exact hx j b n hn hex

theorem sharp182_radial_majorant_actual_auxiliaries {J : Type*} [Fintype J]
    (H : Finset ℕ) (blocks : Finset J) (ζ : Fin 1024 → J → ℝ)
    (hζ : ∀ j b, 0 < ζ j b ∧ ζ j b < 8639 / 50000) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x ≤ (n : ℝ) → ∀ C : J → ℝ,
      sharpDefect x (41361 / 100000) n * (∑ b ∈ blocks, C b) ^ 2 ≤ ∑ j : Fin 1024,
        pairHinge (19 / 50) (pairBinRight (8639 / 50000) (41361 / 100000) j) *
          ∑ pq ∈ markedPrimePairBin x (8639 / 50000) (41361 / 100000)
            (pairBinLeft (8639 / 50000) (41361 / 100000) j)
            (pairBinRight (8639 / 50000) (41361 / 100000) j),
            if pq.1 * pq.2 ∣ n then
              (∑ b ∈ blocks,
                sampledSelbergRoot (sharpAuxiliaryArray H (ζ j b) x) (fun _ => n) * C b) ^ 2 else 0 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), sharp182_auxiliary_radial_units H ζ hζ] with x hx hu
  intro n hn C
  apply sharp182_radial_auxiliary_square blocks x hx n hn
  intro hex j b _
  exact hu n hn hex j b

#print axioms sharpAuxiliaryArray_energy_tendsto
#print axioms sharpAuxiliaryArray_bounds
#print axioms sharpAuxiliaryArray_root_one_on_exceptional
#print axioms sharp182_radial_majorant_actual_auxiliaries

end PrimeGap182Analytic
