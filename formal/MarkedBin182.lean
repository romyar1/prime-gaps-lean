/-
Lean version: 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2).
Mathlib revision: bbcd1968ee6950abe88b85dba6995da346c4b2a8.

Upstream credits

This file includes adapted declarations and local proof fragments from the projects below.
Their credits and Apache 2.0 notices apply to portions derived from those projects. They do not
assert authorship or a license for independently developed material or for this entire file.
Some reuse is limited to subarguments within otherwise independent proofs.

Modified: namespaces and imports consolidated; declarations renamed and reorganized; helpers
inlined; statements, definitions and proofs refactored for this development and its Mathlib API.
The adaptations are not asserted to be verbatim copies of the upstream files.

Attribution: FormalPantheon (frenzymath) contributors.
Adapted areas include the Stepanov and Weil finite-field arguments, Dirichlet L-functions,
large-sieve and Bombieri-Vinogradov estimates, and selected Maynard/Selberg arithmetic,
congruence-counting and tail arguments. These credits include local fragments of the
root-multiplicity, fiber-count, Euler-product, discrepancy and Selberg-moment proofs; they do
not assert that every declaration in these areas is derived from upstream.
Pinned source tree:
https://github.com/frenzymath/FormalPantheon/tree/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1
Released upstream under the Apache License, Version 2.0:
https://github.com/frenzymath/FormalPantheon/blob/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/LICENSE

Attribution: PrimeNumberTheoremAnd (PNT+) contributors.
Authors of adapted upstream proof ranges include ajirving, giuseppe.sorge and teorth.
Adapted portions of the Mertens development run from `mangoldtLogError` through
`prime_correction_summable`; intervening arguments may be new or substantially rewritten.
Pinned source tree:
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/47fa48680663df41146704d02a5b092d792bd5b9
Released upstream under the Apache License, Version 2.0:
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/47fa48680663df41146704d02a5b092d792bd5b9/LICENSE

Copyright (c) 2026 Axiom Math. All rights reserved.
Authors: Axiom Math
Adapted portions of PrimeGapsLib occur in `PrimeGap186.finMulAntidiag_filter_coordinate`,
`PrimeGap186.zeta_pow_eq_card_finMulAntidiag`, `PrimeGap186.one_le_zeta_pow` and
`PrimeGap186.product_lcm_fiber_card_le`. The adaptations rename and move the declarations,
expand divisor-function notation, refactor finite-product arguments, and generalize the
product-fiber estimate to independent divisor supports.
Pinned source tree:
https://github.com/AxiomMath/PrimeGapsLib/tree/1faa7b14e82ddebc2772dfb9153922f01b106477
Released under Apache 2.0 license as described in the upstream LICENSE:
https://github.com/AxiomMath/PrimeGapsLib/blob/1faa7b14e82ddebc2772dfb9153922f01b106477/LICENSE
-/

import Selberg39
import MarkedPairMass182

/-!
The actual weighted prime-pair bin square limit for the sharp182 parameters.
Adapted from Selberg39's checked 39/38-coordinate theorem with pair cap
.41361, roughness .17278, and coefficient cap .17277. All canonical and
erased arrays, auxiliary roots, CRT errors, and harmonic limits are explicit.
The finite-combination theorem sums the signed profiles before squaring.
-/

open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
open scoped MeasureTheory.BoundedContinuousFunction Pointwise ContDiff
open MeasureTheory AddChar Filter Metric Real Finset Asymptotics
open ArithmeticFunction hiding log
open PrimeGap186 PrimeGap182.Selberg

namespace PrimeGap182Analytic

open Classical in
theorem canonical_and_erased_auxiliary_marked_bin_physical_square
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {m : ℕ} (i : Fin 39) (r_c ζ_a l s : ℝ)
    (hζ_a : 0 < ζ_a) (hζrough : ζ_a < (8639 : ℝ) / 50000)
    (hl : 2 * ((8639 : ℝ) / 50000) ≤ l) (hls : l < s)
    (hs : s ≤ (41361 : ℝ) / 100000)
    (hmargin : s + 2 * (r_c + ζ_a) < 1)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) =
      ((17277 : ℝ) / 100000) / ((2624989 : ℝ) / 10000000))
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G))
    (hbF : Bornology.IsBounded (Set.range F))
    (u : ℝ → ((Fin 1 → ℕ) →₀ ℝ)) (E_a : ℝ) :
    let ρ : ℝ := 2624989 / 10000000
    let ξ₀ : ℝ := 17277 / 100000
    let ζ : ℝ := ξ₀ / ρ
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * ζ) •
        Measure.map (fragmentBandMasses a)
          (fragmentLaw ζ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt G X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F X) →
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W : ℝ → ℕ := presievingModulus 𝓗
    let R : ℝ → ℝ := fun x => x ^ ρ
    let Bx : ℝ → ℝ := fun x => fragmentNormalization (W x) x
    let BR : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) ζ, p
    let T39 : ℝ → Finset (Fin 38 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 38 => (q x).divisors)).filter
        (fun r => Squarefree (∏ j, r j))
    let T40 : ℝ → Finset (Fin 39 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
        (fun r => Squarefree (∏ j, r j))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s =>
      fragmentBandMasses a
        (primeLogConfiguration (R x) s)
    let w : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T39 x, Finsupp.single r (G (fun j => X x (r j)) / BR x ^ 38)
    let y : ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T40 x, Finsupp.single r (F (fun j => X x (r j)) / BR x ^ 39)
    let z : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
      w x + (y x).sum (fun r yr =>
        Finsupp.single (fun j => r (i.succAbove j)) (yr / ((r i).totient : ℝ)))
    let qa : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) x ζ_a, p
    let Du : ℝ → Finset (Fin 1 → ℕ) := fun x =>
      (u x).support.biUnion
        (fun s => Fintype.piFinset (fun j => (s j).divisors))
    let Dz : ℝ → Finset (Fin 38 → ℕ) := fun x =>
      (z x).support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
    let L : ℝ → ℕ → ℝ := fun x t =>
      ∑ e ∈ Du x, if e 0 ∣ t then PrimeGap182.Selberg.selbergCoefficient (u x) e else 0
    let C : ℝ → ℕ → ℝ := fun x n =>
      ∑ d ∈ Dz x, if ∀ j, d j ∣ n + h (i.succAbove j) then
        PrimeGap182.Selberg.selbergCoefficient (z x) d else 0
    let H : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun Y =>
      G Y + ∫ t : Fin (m + 1) → ℝ, F (i.insertNth t Y) ∂ν
    (∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ x : ℝ in Filter.atTop,
      1 < x ∧ 0 < Bx x ∧
        (∀ t : Fin 1 → ℕ, |u x t| ≤ N / Bx x) ∧
        ∀ t ∈ (u x).support, t 0 ∈ (qa x).divisors ∧ (t 0 : ℝ) ≤ x ^ ζ_a) →
    Tendsto (fun x => Bx x * (u x).sum
      (fun t ut => ut ^ 2 / ((t 0).totient : ℝ))) atTop (nhds E_a) →
    (∀ᶠ x : ℝ in Filter.atTop,
      ∀ d : Fin 38 → ℕ,
        (PrimeGap182.Selberg.selbergCoefficient (w x) d ≠ 0 ∨
          PrimeGap182.Selberg.selbergCoefficient (y x) (i.insertNth 1 d) ≠ 0) →
        ((∏ j, d j : ℕ) : ℝ) ≤ x ^ r_c) →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop,
        ∀ b : ℕ,
          |(∑ v ∈ markedPrimePairBin x ((8639 : ℝ) / 50000)
                ((41361 : ℝ) / 100000) l s,
              ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
                  L x (n + h i) ^ 2 * C x n ^ 2 else 0) -
            (x / (W x : ℝ) / Bx x / BR x ^ 38) *
              ((∫ t in l..s,
                  Real.log ((t - (8639 : ℝ) / 50000) / ((8639 : ℝ) / 50000)) / t) *
                ((∫ Y : Fin 38 → Fin (m + 1) → ℝ, H Y ^ 2
                    ∂Measure.pi (fun _ : Fin 38 => ν)) *
                  E_a))| ≤
            ε * (x / (W x : ℝ) / Bx x / BR x ^ 38) := by
  intro ρ ξ₀ ζ ν cG cF h W R Bx BR q T39 T40 X w y z qa Du Dz L C H
    hauxData hulim hsourceRadius
  have hρ : 0 < ρ := by norm_num [ρ]
  have hζ : 0 < ζ := by norm_num [ζ, ξ₀, ρ]
  let κ : ℝ := max ζ (ζ_a / ρ)
  have hκ : 0 < κ := hζ.trans_le (le_max_left _ _)
  have hcap : ρ * κ < (8639 : ℝ) / 50000 := by
    dsimp only [κ]
    rw [mul_max_of_nonneg _ _ hρ.le]
    apply max_lt
    · norm_num [ζ, ξ₀, ρ]
    · rw [← mul_div_assoc, mul_div_cancel_left₀ _ hρ.ne']
      exact hζrough
  obtain ⟨M, hM, hamp⟩ :=
    PrimeGap182.Selberg.canonical_and_erased_diagonal_amplitude (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i ζ hζ a G F hbG hbF
  obtain ⟨N, hN, haux⟩ := hauxData
  have hzlim : Tendsto
      (fun x => BR x ^ 38 * (z x).sum
        (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))) atTop
      (nhds (∫ Y, H Y ^ 2 ∂Measure.pi (fun _ : Fin 38 => ν))) := by
    have hraw := PrimeGap182.Selberg.canonical_and_erased_polarized_harmonic_tendsto (𝓗 := 𝓗)
      i ζ hζ a ha ha0 haLast G G F F hG hG hF hF hbG hbG hbF hbF cG cG cF cF
    change Tendsto
      (fun x => BR x ^ 38 * (z x).sum
        (fun r zr => zr * z x r / (∏ j, ((r j).totient : ℝ)))) atTop
      (nhds (∫ Y, H Y * H Y ∂Measure.pi (fun _ : Fin 38 => ν))) at hraw
    simpa only [Finsupp.sum, pow_two] using hraw
  have hharmonic : Tendsto
      (fun x => (Bx x * BR x ^ 38) *
        ((u x).sum (fun t ut => ut ^ 2 / ((t 0).totient : ℝ)) *
          (z x).sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))))
      atTop (nhds ((∫ Y, H Y ^ 2 ∂Measure.pi (fun _ : Fin 38 => ν)) * E_a)) := by
    convert hzlim.mul hulim using 1
    funext x
    ring
  let pairMass : ℝ → ℝ := fun x =>
    ∑ v ∈ markedPrimePairBin x ((8639 : ℝ) / 50000)
        ((41361 : ℝ) / 100000) l s, (((v.1 * v.2 : ℕ) : ℝ))⁻¹
  let pairI : ℝ := ∫ t in l..s,
    Real.log ((t - (8639 : ℝ) / 50000) / ((8639 : ℝ) / 50000)) / t
  have hpair : Tendsto pairMass atTop (nhds pairI) :=
    markedPrimePairBin_harmonic_tendsto_general (8639 / 50000) (41361 / 100000)
      l s (by norm_num) hl hls hs
  let S : ℝ → ℕ → ℝ := fun x b =>
    ∑ v ∈ markedPrimePairBin x ((8639 : ℝ) / 50000)
        ((41361 : ℝ) / 100000) l s,
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
          L x (n + h i) ^ 2 * C x n ^ 2 else 0
  let A : ℝ → ℝ := fun x => x / (W x : ℝ)
  let B : ℝ → ℝ := fun x => Bx x * BR x ^ 38
  let E₀ : ℝ → ℝ := fun x =>
    (u x).sum (fun t ut => ut ^ 2 / ((t 0).totient : ℝ)) *
      (z x).sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))
  let E : ℝ → ℝ := fun x => pairMass x * E₀ x
  let I₀ : ℝ :=
    (∫ Y, H Y ^ 2 ∂Measure.pi (fun _ : Fin 38 => ν)) *
      E_a
  let I : ℝ := pairI * I₀
  have hlim : Tendsto (fun x => B x * E x) atTop (nhds I) := by
    have hbase : Tendsto (fun x => B x * E₀ x) atTop (nhds I₀) := hharmonic
    convert hpair.mul hbase using 1
    funext x
    exact mul_left_comm _ _ _
  have hpos : ∀ᶠ x : ℝ in atTop, 0 ≤ A x ∧ 0 < B x := by
    filter_upwards [hamp, haux] with x hampx hauxx
    obtain ⟨hx, hBR, _, _, _, _, _, _, _, _⟩ := hampx
    obtain ⟨_, hBx, _, _⟩ := hauxx
    exact ⟨div_nonneg (zero_lt_one.trans hx).le (Nat.cast_nonneg _),
      mul_pos hBx (pow_pos hBR 38)⟩
  have harithmetic : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop, ∀ b : ℕ,
        |S x b - A x * E x| ≤ ε * (A x / B x) := by
    intro ε hε
    have hcomparison := PrimeGap182.Selberg.selberg39_auxiliary_marked_bin_uniform (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      i κ r_c ζ_a M N ((8639 : ℝ) / 50000) ((41361 : ℝ) / 100000) l s
      hκ hζ_a hM.le hN (by norm_num) (by norm_num) (by linarith) hcap hmargin ε hε
    filter_upwards [hamp, haux, hsourceRadius, hcomparison]
      with x hampx hauxx hradx hcompx
    obtain ⟨hx, _, _, _, _, _, _, hzcoeff, hzsupport, hzbound⟩ := hampx
    obtain ⟨_, _, hubound, husupport⟩ := hauxx
    have hcommon := fragment_divisors_common_cap
      (W x) x ρ ζ ζ_a hx hρ
    have hzradius : ∀ r ∈ (z x).support,
        ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r_c := by
      apply PrimeGap182.Selberg.selberg_diagonal_support_le_of_coefficient_le
        (z x) (fun r hr => (hzsupport r hr).1) (x ^ r_c)
      intro d hd
      apply hradx d
      by_cases hwzero : PrimeGap182.Selberg.selbergCoefficient (w x) d = 0
      · right
        intro hyzero
        apply hd
        rw [hzcoeff d, hwzero, hyzero, add_zero]
      · exact Or.inl hwzero
    have hucommon : ∀ t ∈ (u x).support,
        t 0 ∈ (∏ p ∈ fragmentPrimes (W x) (R x) κ, p).divisors ∧
          (t 0 : ℝ) ≤ x ^ ζ_a := by
      intro t ht
      exact ⟨hcommon.2 (husupport t ht).1, (husupport t ht).2⟩
    have hzcommon : ∀ r ∈ (z x).support,
        Squarefree (∏ j, r j) ∧
          (∀ j, r j ∈
            (∏ p ∈ fragmentPrimes (W x) (R x) κ, p).divisors) ∧
          ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r_c := by
      intro r hr
      exact ⟨(hzsupport r hr).1, fun j => hcommon.1 ((hzsupport r hr).2 j),
        hzradius r hr⟩
    intro b
    have hb := hcompx.2.2.2 (u x) (z x) hucommon hzcommon hubound hzbound b
    have heq : pairMass x * (A x * E₀ x) = A x * E x :=
      mul_left_comm _ _ _
    rw [← heq]
    simpa only [S, A, B, E₀, pairMass, mul_pow, one_div, div_mul_eq_div_div] using hb
  have hfinal := PrimeGap182.Selberg.uniform_scaled_error_of_normalized_tendsto
    S A B E I hpos hlim harithmetic
  simpa only [S, A, B, I, I₀, pairI, div_mul_eq_div_div] using hfinal

open Classical in
theorem canonical_and_erased_auxiliary_marked_bin_physical_square_finset
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {J : Type*} {m : ℕ} (𝒥 : Finset J) (c : J → ℝ)
    (i : Fin 39) (r_c ζ_a l s : ℝ)
    (hζ_a : 0 < ζ_a) (hζrough : ζ_a < (8639 : ℝ) / 50000)
    (hl : 2 * ((8639 : ℝ) / 50000) ≤ l) (hls : l < s)
    (hs : s ≤ (41361 : ℝ) / 100000)
    (hmargin : s + 2 * (r_c + ζ_a) < 1)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) =
      ((17277 : ℝ) / 100000) / ((2624989 : ℝ) / 10000000))
    (G : J → (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : J → (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : ∀ j ∈ 𝒥, Measurable (G j)) (hF : ∀ j ∈ 𝒥, Measurable (F j))
    (hbG : ∀ j ∈ 𝒥, Bornology.IsBounded (Set.range (G j)))
    (hbF : ∀ j ∈ 𝒥, Bornology.IsBounded (Set.range (F j)))
    (u : ℝ → ((Fin 1 → ℕ) →₀ ℝ)) (E_a : ℝ) :
    let ρ : ℝ := 2624989 / 10000000
    let ξ₀ : ℝ := 17277 / 100000
    let ζ : ℝ := ξ₀ / ρ
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * ζ) •
        Measure.map (fragmentBandMasses a)
          (fragmentLaw ζ)
    (∀ j ∈ 𝒥, ∀ᵐ X ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt (G j) X) →
    (∀ j ∈ 𝒥, ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt (F j) X) →
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W : ℝ → ℕ := presievingModulus 𝓗
    let R : ℝ → ℝ := fun x => x ^ ρ
    let Bx : ℝ → ℝ := fun x => fragmentNormalization (W x) x
    let BR : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) ζ, p
    let T39 : ℝ → Finset (Fin 38 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 38 => (q x).divisors)).filter
        (fun r => Squarefree (∏ k, r k))
    let T40 : ℝ → Finset (Fin 39 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
        (fun r => Squarefree (∏ k, r k))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x t =>
      fragmentBandMasses a
        (primeLogConfiguration (R x) t)
    let w : J → ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun j x =>
      ∑ r ∈ T39 x, Finsupp.single r (G j (fun k => X x (r k)) / BR x ^ 38)
    let y : J → ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun j x =>
      ∑ r ∈ T40 x, Finsupp.single r (F j (fun k => X x (r k)) / BR x ^ 39)
    let z : J → ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun j x =>
      w j x + (y j x).sum (fun r yr =>
        Finsupp.single (fun k => r (i.succAbove k)) (yr / ((r i).totient : ℝ)))
    let qa : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) x ζ_a, p
    let Du : ℝ → Finset (Fin 1 → ℕ) := fun x =>
      (u x).support.biUnion
        (fun t => Fintype.piFinset (fun k => (t k).divisors))
    let Dz : J → ℝ → Finset (Fin 38 → ℕ) := fun j x =>
      (z j x).support.biUnion
        (fun r => Fintype.piFinset (fun k => (r k).divisors))
    let L : ℝ → ℕ → ℝ := fun x t =>
      ∑ e ∈ Du x, if e 0 ∣ t then PrimeGap182.Selberg.selbergCoefficient (u x) e else 0
    let C : ℝ → ℕ → ℝ := fun x n =>
      ∑ j ∈ 𝒥, c j *
        (∑ d ∈ Dz j x, if ∀ k, d k ∣ n + h (i.succAbove k) then
          PrimeGap182.Selberg.selbergCoefficient (z j x) d else 0)
    let H : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun Y =>
      ∑ j ∈ 𝒥, c j *
        (G j Y + ∫ t : Fin (m + 1) → ℝ, F j (i.insertNth t Y) ∂ν)
    (∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ x : ℝ in Filter.atTop,
      1 < x ∧ 0 < Bx x ∧
        (∀ t : Fin 1 → ℕ, |u x t| ≤ N / Bx x) ∧
        ∀ t ∈ (u x).support, t 0 ∈ (qa x).divisors ∧ (t 0 : ℝ) ≤ x ^ ζ_a) →
    Tendsto (fun x => Bx x * (u x).sum
      (fun t ut => ut ^ 2 / ((t 0).totient : ℝ))) atTop (nhds E_a) →
    (∀ j ∈ 𝒥, ∀ᶠ x : ℝ in Filter.atTop,
      ∀ d : Fin 38 → ℕ,
        (PrimeGap182.Selberg.selbergCoefficient (w j x) d ≠ 0 ∨
          PrimeGap182.Selberg.selbergCoefficient (y j x) (i.insertNth 1 d) ≠ 0) →
        ((∏ k, d k : ℕ) : ℝ) ≤ x ^ r_c) →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop,
        ∀ b : ℕ,
          |(∑ v ∈ markedPrimePairBin x ((8639 : ℝ) / 50000)
                ((41361 : ℝ) / 100000) l s,
              ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
                  L x (n + h i) ^ 2 * C x n ^ 2 else 0) -
            (x / (W x : ℝ) / Bx x / BR x ^ 38) *
              ((∫ t in l..s,
                  Real.log ((t - (8639 : ℝ) / 50000) / ((8639 : ℝ) / 50000)) / t) *
                ((∫ Y : Fin 38 → Fin (m + 1) → ℝ, H Y ^ 2
                    ∂Measure.pi (fun _ : Fin 38 => ν)) *
                  E_a))| ≤
            ε * (x / (W x : ℝ) / Bx x / BR x ^ 38) := by
  intro ρ ξ₀ ζ ν cG cF h W R Bx BR q T39 T40 X w y z qa Du Dz L C H
    hauxData hulim hsourceRadius
  let Gsum : (Fin 38 → Fin (m + 1) → ℝ) → ℝ :=
    fun Y => ∑ j ∈ 𝒥, c j * G j Y
  let Fsum : (Fin 39 → Fin (m + 1) → ℝ) → ℝ :=
    fun Y => ∑ j ∈ 𝒥, c j * F j Y
  obtain ⟨hGsum, hbGsum, hcGsum⟩ := PrimeGap182.Selberg.finite_profile_combination_regular
    (Measure.pi (fun _ : Fin 38 => ν)) 𝒥 c G hG hbG cG
  obtain ⟨hFsum, hbFsum, hcFsum⟩ := PrimeGap182.Selberg.finite_profile_combination_regular
    (Measure.pi (fun _ : Fin 39 => ν)) 𝒥 c F hF hbF cF
  let wsum : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
    ∑ r ∈ T39 x, Finsupp.single r (Gsum (fun k => X x (r k)) / BR x ^ 38)
  let ysum : ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun x =>
    ∑ r ∈ T40 x, Finsupp.single r (Fsum (fun k => X x (r k)) / BR x ^ 39)
  let zsum : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
    wsum x + (ysum x).sum (fun r yr =>
      Finsupp.single (fun k => r (i.succAbove k)) (yr / ((r i).totient : ℝ)))
  let Csum : ℝ → ℕ → ℝ := fun x n =>
    ∑ d ∈ (zsum x).support.biUnion
        (fun r => Fintype.piFinset (fun k => (r k).divisors)),
      if ∀ k, d k ∣ n + h (i.succAbove k) then PrimeGap182.Selberg.selbergCoefficient (zsum x) d else 0
  let Hsum : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun Y =>
    Gsum Y + ∫ t : Fin (m + 1) → ℝ, Fsum (i.insertNth t Y) ∂ν
  have hw (x : ℝ) : wsum x = ∑ j ∈ 𝒥, c j • w j x :=
    PrimeGap182.Selberg.canonical_diagonal_finset_smul 𝒥 c (T39 x) (X x) (BR x) G
  have hy (x : ℝ) : ysum x = ∑ j ∈ 𝒥, c j • y j x :=
    PrimeGap182.Selberg.canonical_diagonal_finset_smul 𝒥 c (T40 x) (X x) (BR x) F
  have hz (x : ℝ) : zsum x = ∑ j ∈ 𝒥, c j • z j x := by
    dsimp only [zsum, z]
    rw [hw x, hy x, PrimeGap182.Selberg.weighted_erasure_finset_smul]
    simp only [smul_add, Finset.sum_add_distrib]
  have hC : Csum = C := by
    funext x n
    dsimp only [Csum, C, Dz]
    rw [hz x]
    have hroot := PrimeGap182.Selberg.selberg_divisor_root_finset_combination 𝒥 c (fun j => z j x)
      (fun k => n + h (i.succAbove k))
    refine Eq.trans ?_ (Eq.trans hroot ?_)
    · refine Finset.sum_congr ?_ ?_
      · ext d
        simp only [Finset.mem_biUnion, Fintype.mem_piFinset]
      · intro d _
        split_ifs <;> rfl
    · apply Finset.sum_congr rfl
      intro j _
      apply congrArg (fun t : ℝ => c j * t)
      refine Finset.sum_congr ?_ ?_
      · ext d
        simp only [Finset.mem_biUnion, Fintype.mem_piFinset]
      · intro d _
        split_ifs <;> rfl
  have hH : Hsum = H := by
    funext Y
    change (∑ j ∈ 𝒥, c j * G j Y) +
        (∫ t, (∑ j ∈ 𝒥, c j * F j (i.insertNth t Y)) ∂ν) =
      ∑ j ∈ 𝒥, c j * (G j Y + ∫ t, F j (i.insertNth t Y) ∂ν)
    rw [(PrimeGap182.Selberg.fixed_band_erased_finset_integral 𝒥 c i ζ a F hF hbF).2.2.2 Y]
    simp only [mul_add, Finset.sum_add_distrib, ν]
  have hradSum : ∀ᶠ x : ℝ in atTop, ∀ d : Fin 38 → ℕ,
      (PrimeGap182.Selberg.selbergCoefficient (wsum x) d ≠ 0 ∨
        PrimeGap182.Selberg.selbergCoefficient (ysum x) (i.insertNth 1 d) ≠ 0) →
      ((∏ k, d k : ℕ) : ℝ) ≤ x ^ r_c := by
    filter_upwards [(Filter.eventually_all_finset 𝒥).2 hsourceRadius] with x hx
    intro d hd
    rcases hd with hd | hd
    · rw [hw x] at hd
      exact PrimeGap182.Selberg.selbergCoefficient_finset_radius 𝒥 c (fun j => w j x) d (x ^ r_c)
        (fun j hj hne => hx j hj d (Or.inl hne)) hd
    · rw [hy x] at hd
      obtain ⟨j, hj, _, hne⟩ :=
        (PrimeGap182.Selberg.selbergCoefficient_finset_combination 𝒥 c (fun j => y j x)).2 (i.insertNth 1 d) hd
      exact hx j hj d (Or.inr hne)
  have hmain := canonical_and_erased_auxiliary_marked_bin_physical_square
    (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
    i r_c ζ_a l s hζ_a hζrough hl hls hs hmargin a ha ha0 haLast Gsum Fsum
    hGsum hFsum hbGsum hbFsum u E_a hcGsum hcFsum hauxData hulim hradSum
  change (∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ b : ℕ,
    |(∑ v ∈ markedPrimePairBin x ((8639 : ℝ) / 50000)
          ((41361 : ℝ) / 100000) l s,
        ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
            L x (n + h i) ^ 2 * Csum x n ^ 2 else 0) -
      (x / (W x : ℝ) / Bx x / BR x ^ 38) *
        ((∫ t in l..s,
            Real.log ((t - (8639 : ℝ) / 50000) / ((8639 : ℝ) / 50000)) / t) *
          ((∫ Y : Fin 38 → Fin (m + 1) → ℝ, Hsum Y ^ 2
              ∂Measure.pi (fun _ : Fin 38 => ν)) *
            E_a))| ≤
      ε * (x / (W x : ℝ) / Bx x / BR x ^ 38)) at hmain
  simpa only [hC, hH] using hmain

#print axioms canonical_and_erased_auxiliary_marked_bin_physical_square
#print axioms canonical_and_erased_auxiliary_marked_bin_physical_square_finset
end PrimeGap182Analytic
