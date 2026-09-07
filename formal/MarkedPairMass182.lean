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

import PrimeGaps186

/-!
General prime-pair harmonic mass, adapted from the public proof at lines
45680--45811. The roughness and pair cap are parameters. Positivity of the
pair cap follows from 0<ξ and 2ξ≤l<u≤a. Endpoint equality contributes at
most one unordered pair and tends to zero. No finite-field input is used.
-/

open scoped BigOperators Topology
open MeasureTheory Filter PrimeGap186

namespace PrimeGap182Analytic

theorem markedPrimePairBin_harmonic_tendsto_general
    (ξ a l u : ℝ) (hξ : 0 < ξ)
    (hl : 2 * ξ ≤ l)
    (hlu : l < u) (hu : u ≤ a) :
    Tendsto
      (fun x : ℝ =>
        ∑ v ∈ markedPrimePairBin x ξ
            a l u,
          (((v.1 * v.2 : ℕ) : ℝ))⁻¹)
      atTop
      (nhds (∫ s in l..u,
        Real.log ((s - ξ) / ξ) / s)) := by
  classical
  let P : ℝ → Finset ℕ := fun x => Nat.primesLE ⌊x ^ a⌋₊
  let C : ℝ → ℝ → Finset (ℕ × ℕ) := fun x s =>
    ((P x) ×ˢ (P x)).filter (fun v =>
      v.1 < v.2 ∧ x ^ ξ ≤ (v.1 : ℝ) ∧ x ^ ξ ≤ (v.2 : ℝ) ∧
        ((v.1 * v.2 : ℕ) : ℝ) ≤ x ^ s)
  let w : ℕ × ℕ → ℝ := fun v => (((v.1 * v.2 : ℕ) : ℝ))⁻¹
  let B : ℝ → ℝ := fun x => ∑ v ∈ markedPrimePairBin x ξ a l u, w v
  let D : ℝ → ℝ := fun x => (∑ v ∈ C x u, w v) - ∑ v ∈ C x l, w v
  have ha : 0 < a := by linarith
  have hCu := unordered_prime_pair_cumulative_tendsto ξ a u hξ (hl.trans hlu.le) hu
  have hCl := unordered_prime_pair_cumulative_tendsto ξ a l hξ hl (hlu.le.trans hu)
  have hD : Tendsto D atTop (nhds ((∫ t in ξ..(u / 2), Real.log ((u - t) / t) / t) -
      ∫ t in ξ..(l / 2), Real.log ((l - t) / t) / t)) := hCu.sub hCl
  have herror : Tendsto (fun x : ℝ => B x - D x) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (g := fun x : ℝ => (x ^ a)⁻¹)
      (Eventually.of_forall (fun _ => abs_nonneg _))
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      have hsub : C x l ⊆ C x u := by
        intro v hv
        obtain ⟨hvP, hlt, hp, hq, hpq⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hvP, hlt, hp, hq,
          hpq.trans (Real.rpow_le_rpow_of_exponent_le hx.le hlu.le)⟩
      let Q : Finset (ℕ × ℕ) := C x u \ C x l
      let E : Finset (ℕ × ℕ) := Q.filter (fun v => ¬ ((v.1 * v.2 : ℕ) : ℝ) < x ^ a)
      have hQ (v : ℕ × ℕ) (hv : v ∈ Q) :
          v ∈ (P x) ×ˢ (P x) ∧ v.1 < v.2 ∧
            x ^ ξ ≤ (v.1 : ℝ) ∧ x ^ ξ ≤ (v.2 : ℝ) ∧
            x ^ l < ((v.1 * v.2 : ℕ) : ℝ) ∧
            ((v.1 * v.2 : ℕ) : ℝ) ≤ x ^ u := by
        obtain ⟨hvu, hvl⟩ := Finset.mem_sdiff.mp hv
        obtain ⟨hvP, hlt, hp, hq, hpq⟩ := Finset.mem_filter.mp hvu
        refine ⟨hvP, hlt, hp, hq, ?_, hpq⟩
        by_contra! he
        exact hvl (Finset.mem_filter.mpr ⟨hvP, hlt, hp, hq, he⟩)
      have hbin : markedPrimePairBin x ξ a l u =
          Q.filter (fun v => ((v.1 * v.2 : ℕ) : ℝ) < x ^ a) := by
        ext v
        by_cases hvP : v ∈ (P x) ×ˢ (P x)
        · have hp : v.1.Prime := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hvP).1
          have hq : v.2.Prime := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hvP).2
          have hpq0 : 0 < ((v.1 * v.2 : ℕ) : ℝ) := by
            exact_mod_cast mul_pos hp.pos hq.pos
          simp only [markedPrimePairBin, Q, C, P, Finset.mem_filter,
            Finset.mem_sdiff, ← Real.logb_le_iff_le_rpow hx hpq0, not_and, not_le]
          tauto
        · simp only [markedPrimePairBin, Q, C, P, Finset.mem_filter, Finset.mem_sdiff] at *
          tauto
      have hEvalue (v : ℕ × ℕ) (hv : v ∈ E) :
          ((v.1 * v.2 : ℕ) : ℝ) = x ^ a := by
        obtain ⟨hvQ, hvnot⟩ := Finset.mem_filter.mp hv
        exact le_antisymm ((hQ v hvQ).2.2.2.2.2.trans
          (Real.rpow_le_rpow_of_exponent_le hx.le hu)) (le_of_not_gt hvnot)
      have hEcard : E.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro v hv z hz
        have hvQ := hQ v (Finset.mem_filter.mp hv).1
        have hzQ := hQ z (Finset.mem_filter.mp hz).1
        have hvp : v.1.Prime := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hvQ.1).1
        have hzp : z.1.Prime := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hzQ.1).1
        have hzq : z.2.Prime := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hzQ.1).2
        have he : v.1 * v.2 = z.1 * z.2 := by
          exact_mod_cast (hEvalue v hv).trans (hEvalue z hz).symm
        have hvq : v.2.Prime := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hvQ.1).2
        have hperm : List.Perm [v.1, v.2] [z.1, z.2] :=
          _root_.perm_of_prod_eq_prod (by simpa using he)
            (by simpa using And.intro hvp.prime hvq.prime)
            (by simpa using And.intro hzp.prime hzq.prime)
        have hlist : [v.1, v.2] = [z.1, z.2] :=
          List.Perm.eq_of_pairwise' (r := (· ≤ ·))
            (List.pairwise_pair.mpr hvQ.2.1.le) (List.pairwise_pair.mpr hzQ.2.1.le) hperm
        have hp : v.1 = z.1 ∧ v.2 = z.2 := by simpa using hlist
        exact Prod.ext hp.1 hp.2
      have hEsum : (∑ v ∈ E, w v) ≤ (x ^ a)⁻¹ := by
        apply (Finset.sum_le_card_nsmul E w ((x ^ a)⁻¹)
          (fun v hv => (congrArg Inv.inv (hEvalue v hv)).le)).trans
        simpa only [one_nsmul] using
          nsmul_le_nsmul_left (inv_nonneg.mpr (Real.rpow_nonneg hx0.le a)) hEcard
      have hsplit : B x + (∑ v ∈ E, w v) = D x := by
        dsimp only [B, D]
        rw [hbin]
        change (∑ v ∈ Q.filter (fun v => ((v.1 * v.2 : ℕ) : ℝ) < x ^ a), w v) +
          (∑ v ∈ Q.filter (fun v => ¬ ((v.1 * v.2 : ℕ) : ℝ) < x ^ a), w v) = _
        rw [Finset.sum_filter_add_sum_filter_not]
        exact Finset.sum_sdiff_eq_sub hsub
      have hnonneg : 0 ≤ ∑ v ∈ E, w v :=
        Finset.sum_nonneg (fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      have heq : B x - D x = -(∑ v ∈ E, w v) := by linarith
      rw [heq, abs_neg, abs_of_nonneg hnonneg]
      exact hEsum
    · exact (tendsto_rpow_atTop ha).inv_tendsto_atTop
  have hlim := herror.add hD
  rw [marked_pair_cdf_difference hξ hl hlu.le] at hlim
  simpa only [sub_add_cancel, zero_add, B, w] using hlim

#print axioms markedPrimePairBin_harmonic_tendsto_general
end PrimeGap182Analytic
