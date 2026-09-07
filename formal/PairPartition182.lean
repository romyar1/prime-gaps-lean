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

import MarkedPairMass182

/-!
Exact disjoint partition of actual unordered prime-divisor pairs. Both the
roughness threshold and upper pair exponent are parameters. This adapts the
public cardinality proof at line 144626 to expose its stronger set partition,
so it transports arbitrary weights without a multiplicity loss.
-/

noncomputable section
open scoped BigOperators Topology
open PrimeGap186 Real Filter

namespace PrimeGap182Analytic

def pairBinRight (xi a : ℝ) (j : Fin 1024) : ℝ :=
  2 * xi + ((j.val : ℝ) + 1) * ((a - 2 * xi) / 1024)

def pairBinLeft (xi a : ℝ) (j : Fin 1024) : ℝ :=
  pairBinRight xi a j - (a - 2 * xi) / 1024

open Classical in
def markedPairCarrier (x xi a : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Nat.primesLE n) ×ˢ (Nat.primesLE n)).filter
    (fun pq => pq.1 < pq.2 ∧ pq.1 * pq.2 ∣ n ∧
      x ^ xi ≤ (pq.1 : ℝ) ∧ x ^ xi ≤ (pq.2 : ℝ) ∧
      ((pq.1 * pq.2 : ℕ) : ℝ) < x ^ a)

open Classical in
def markedDivisorPairBin (x xi a : ℝ) (j : Fin 1024) (n : ℕ) : Finset (ℕ × ℕ) :=
  (markedPrimePairBin x xi a (pairBinLeft xi a j) (pairBinRight xi a j)).filter
    (fun pq => pq.1 * pq.2 ∣ n)

theorem markedPairCarrier_partition (x xi a : ℝ) (hx : 1 < x)
    (hgap : 2 * xi < a) (n : ℕ) (hn : 0 < n) :
    markedPairCarrier x xi a n = Finset.univ.biUnion (fun j => markedDivisorPairBin x xi a j n) ∧
    (↑(Finset.univ : Finset (Fin 1024)) : Set (Fin 1024)).PairwiseDisjoint
      (fun j => markedDivisorPairBin x xi a j n) := by
  classical
  let h : ℝ := (a - 2 * xi) / 1024
  let R (j : Fin 1024) : ℝ := pairBinRight xi a j
  let s (pq : ℕ × ℕ) : ℝ := Real.logb x ((pq.1 * pq.2 : ℕ) : ℝ)
  let U : Finset (ℕ × ℕ) := ((Nat.primesLE n) ×ˢ (Nat.primesLE n)).filter
    (fun pq => pq.1 < pq.2 ∧ pq.1 * pq.2 ∣ n ∧
      x ^ xi ≤ (pq.1 : ℝ) ∧ x ^ xi ≤ (pq.2 : ℝ) ∧
      ((pq.1 * pq.2 : ℕ) : ℝ) < x ^ a)
  let B (j : Fin 1024) : Finset (ℕ × ℕ) :=
    (markedPrimePairBin x xi a (R j - h) (R j)).filter
      (fun pq => pq.1 * pq.2 ∣ n)
  change U = Finset.univ.biUnion B ∧
    (↑(Finset.univ : Finset (Fin 1024)) : Set (Fin 1024)).PairwiseDisjoint B
  have hh : 0 < h := div_pos (sub_pos.mpr hgap) (by norm_num)
  have ha : 2 * xi + 1024 * h = a := by
    dsimp only [h]
    ring
  have hR (j : Fin 1024) : R j = 2 * xi + ((j.val : ℝ) + 1) * h := by
    rfl
  have hB (j : Fin 1024) (pq : ℕ × ℕ) :
      pq ∈ B j ↔ pq ∈ U ∧ R j - h < s pq ∧ s pq ≤ R j := by
    constructor
    · intro hpq
      obtain ⟨hbin, hd⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hbox, hlt, hp, hq, hl, hu, hprod⟩ := Finset.mem_filter.mp hbin
      have hpp := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).1
      have hqp := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).2
      refine ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hlt, hd, hp, hq, hprod⟩, hl, hu⟩
      · exact Nat.mem_primesLE.mpr
          ⟨Nat.le_of_dvd hn ((dvd_mul_right pq.1 pq.2).trans hd), hpp⟩
      · exact Nat.mem_primesLE.mpr
          ⟨Nat.le_of_dvd hn ((dvd_mul_left pq.2 pq.1).trans hd), hqp⟩
    · rintro ⟨hpq, hl, hu⟩
      obtain ⟨hbox, hlt, hd, hp, hq, hprod⟩ := Finset.mem_filter.mp hpq
      have hpp := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).1
      have hqp := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).2
      have hpbound : pq.1 ≤ ⌊x ^ a⌋₊ := Nat.le_floor
        ((Nat.cast_le.mpr (Nat.le_mul_of_pos_right pq.1 hqp.pos)).trans hprod.le)
      have hqbound : pq.2 ≤ ⌊x ^ a⌋₊ := Nat.le_floor
        ((Nat.cast_le.mpr (Nat.le_mul_of_pos_left pq.2 hpp.pos)).trans hprod.le)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hpbound, hpp⟩, Nat.mem_primesLE.mpr ⟨hqbound, hqp⟩⟩,
          hlt, hp, hq, hl, hu, hprod⟩, hd⟩
  have hbounds (pq : ℕ × ℕ) (hpq : pq ∈ U) : 2 * xi < s pq ∧ s pq < a := by
    obtain ⟨hbox, hlt, _, hp, _, hprod⟩ := Finset.mem_filter.mp hpq
    have hpp := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).1
    have hqp := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).2
    have hp0 : 0 < (pq.1 : ℝ) := Nat.cast_pos.mpr hpp.pos
    have hq0 : 0 < (pq.2 : ℝ) := Nat.cast_pos.mpr hqp.pos
    have hplog : xi ≤ Real.logb x (pq.1 : ℝ) :=
      (Real.le_logb_iff_rpow_le hx hp0).mpr hp
    have hpqlog : Real.logb x (pq.1 : ℝ) < Real.logb x (pq.2 : ℝ) :=
      Real.logb_lt_logb hx hp0 (Nat.cast_lt.mpr hlt)
    have hs : s pq = Real.logb x (pq.1 : ℝ) + Real.logb x (pq.2 : ℝ) := by
      dsimp only [s]
      rw [Nat.cast_mul, Real.logb_mul hp0.ne' hq0.ne']
    constructor
    · rw [hs]
      linarith
    · exact (Real.logb_lt_iff_lt_rpow hx
        (Nat.cast_pos.mpr (Nat.mul_pos hpp.pos hqp.pos))).mpr hprod
  have hceil (z : ℝ) (j : Fin 1024) (hz : R j - h < z ∧ z ≤ R j) :
      ⌈(z - 2 * xi) / h⌉₊ = j.val + 1 := by
    rw [Nat.ceil_eq_iff (Nat.add_one_ne_zero j.val)]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [lt_div_iff₀ hh, div_le_iff₀ hh]
    simp only [hR] at hz
    constructor <;> nlinarith [hz.1, hz.2]
  have hexist (z : ℝ) (hz : 2 * xi < z ∧ z < a) :
      ∃ j : Fin 1024, R j - h < z ∧ z ≤ R j := by
    have hcover :=
      Ioc_subset_biUnion_Ioc 1024 (fun i : ℕ => 2 * xi + (i : ℝ) * h)
        (by simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_ofNat, ha] using
          (show z ∈ Set.Ioc (2 * xi) a from ⟨hz.1, hz.2.le⟩))
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_Ioc, exists_prop] at hcover
    obtain ⟨i, hi, hl, hu⟩ := hcover
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only [Nat.cast_add, Nat.cast_one] at hu
    simp only [hR]
    constructor <;> nlinarith
  have hUnion : U = Finset.univ.biUnion B := by
    ext pq
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hpq
      obtain ⟨j, hj⟩ := hexist (s pq) (hbounds pq hpq)
      exact ⟨j, (hB j pq).mpr ⟨hpq, hj⟩⟩
    · rintro ⟨j, hj⟩
      exact ((hB j pq).mp hj).1
  have hdisj :
      (↑(Finset.univ : Finset (Fin 1024)) : Set (Fin 1024)).PairwiseDisjoint B := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro pq hpi hpj
    have hi := hceil (s pq) i ((hB i pq).mp hpi).2
    have hj := hceil (s pq) j ((hB j pq).mp hpj).2
    exact hij (Fin.ext (Nat.add_right_cancel (hi.symm.trans hj)))
  exact ⟨hUnion, hdisj⟩

theorem markedPairCarrier_weighted_partition (x xi a : ℝ) (hx : 1 < x)
    (hgap : 2 * xi < a) (n : ℕ) (hn : 0 < n) (w : ℕ × ℕ → ℝ) :
    (∑ pq ∈ markedPairCarrier x xi a n, w pq) =
      ∑ j : Fin 1024, ∑ pq ∈ markedDivisorPairBin x xi a j n, w pq := by
  classical
  obtain ⟨hU, hd⟩ := markedPairCarrier_partition x xi a hx hgap n hn
  rw [hU, Finset.sum_biUnion hd]

#print axioms markedPairCarrier_partition
#print axioms markedPairCarrier_weighted_partition
end PrimeGap182Analytic
