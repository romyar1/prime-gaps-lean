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

import MixedSelbergCRT182

/-!
The actual product of the one-coordinate auxiliary sieve and the erased
38-coordinate Selberg root is represented as a complete 39-coordinate
divisor root. This exposes the finite support and its L1 estimate for
mixed-radius arguments. Adapted from the checked Selberg39 proof.
-/

open scoped BigOperators
open PrimeGap186 PrimeGap182.Selberg
namespace PrimeGap182Analytic

open Classical in
theorem auxiliary_product_divisor_representation
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (x κ : ℝ) (_hx : 1 < x) (hκ : 0 < κ) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W := PrimeGap186.presievingModulus 𝓗 x
    let R := x ^ ρ
    let P := PrimeGap186.fragmentPrimes W R κ
    let q : ℕ := ∏ p ∈ P, p
    ∀ (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ),
      (∀ s ∈ u.support, s 0 ∈ q.divisors) →
      (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
      let Du := u.support.biUnion
        (fun s => Fintype.piFinset (fun j => (s j).divisors))
      let Dz := z.support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
      let L : ℕ → ℝ := fun t =>
        ∑ e ∈ Du, if e 0 ∣ t then PrimeGap182.Selberg.selbergCoefficient u e else 0
      let C : ℕ → ℝ := fun n =>
        ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
          PrimeGap182.Selberg.selbergCoefficient z d else 0
      ∀ (M : ℕ), 0 < M → Nat.Coprime W M →
        (∀ s ∈ u.support, Nat.Coprime (s 0) M) →
        (∀ r ∈ z.support, Nat.Coprime (∏ j, r j) M) →
        ∃ (D : Finset (Fin 39 → ℕ)) (lam : (Fin 39 → ℕ) → ℝ),
          (∀ a ∈ D, Squarefree (∏ j, a j) ∧ Nat.Coprime (∏ j, a j) W ∧
            Nat.Coprime (∏ j, a j) M ∧ ∀ j, a j ∣ q) ∧
          (∀ n : ℕ, L (n + h i) * C n = divisorRootOn D lam h n) ∧
          (∑ a ∈ D, |lam a|) ≤
            (∑ e ∈ Du, |PrimeGap182.Selberg.selbergCoefficient u e|) *
              (∑ d ∈ Dz, |PrimeGap182.Selberg.selbergCoefficient z d|) := by
  refine (fun (_ : 0 < κ) => ?_) hκ
  classical
  intro ρ h W R P q u z hu hz Du Dz L C M hM hWM huM hzM
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hpW (p : ℕ) (hp : p ∈ P) : ¬ p ∣ W := (Finset.mem_filter.mp hp).2
  have hq : 0 < q := Finset.prod_pos fun p hp => (hP p hp).pos
  have hqsf : Squarefree q := PrimeGap186.squarefree_prime_prod P hP
  have hqW : Nat.Coprime q W :=
    Nat.Coprime.prod_left fun p hp => (hP p hp).coprime_iff_not_dvd.mpr (hpW p hp)
  have hW : 0 < W := PrimeGap186.presieving_pos 𝓗 x
  have hinj : Function.Injective h :=
    (𝓗.orderEmbOfFin h𝓗_card).injective
  have hcover : ∀ a c : Fin 39, h a ≠ h c → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h c) → p ∣ W := by
    intro a c hac p hp hpd
    exact PrimeGap182.Selberg.difference_prime_dvd_presieving 𝓗 x
      (𝓗.orderEmbOfFin_mem h𝓗_card a)
      (𝓗.orderEmbOfFin_mem h𝓗_card c) hac hp hpd
  have hU (e : Fin 1 → ℕ) (he : e ∈ Du) :
      Squarefree (e 0) ∧ e 0 ∣ q ∧ Nat.Coprime (e 0) W := by
    obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp he
    have hes0 := (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hes 0)).1
    have heq : e 0 ∣ q := hes0.trans (Nat.mem_divisors.mp (hu s hs)).1
    exact ⟨hqsf.squarefree_of_dvd heq, heq, hqW.of_dvd_left heq⟩
  have hZ (d : Fin 38 → ℕ) (hd : d ∈ Dz) :
      Squarefree (∏ j, d j) ∧ (∀ j, d j ∣ q) ∧ Nat.Coprime (∏ j, d j) W := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    have hdr' : ∀ j, d j ∣ r j :=
      fun j => (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hdr j)).1
    have hdq : ∀ j, d j ∣ q :=
      fun j => (hdr' j).trans (Nat.mem_divisors.mp ((hz r hr).2 j)).1
    refine ⟨(hz r hr).1.squarefree_of_dvd ?_, hdq, ?_⟩
    · exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hdr' j)
    · exact Nat.coprime_fintype_prod_left_iff.mpr fun j => hqW.of_dvd_left (hdq j)
  have hUM (e : Fin 1 → ℕ) (he : e ∈ Du) : Nat.Coprime (e 0) M := by
    obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp he
    exact (huM s hs).of_dvd_left
      (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hes 0)).1
  have hZM (d : Fin 38 → ℕ) (hd : d ∈ Dz) : Nat.Coprime (∏ j, d j) M := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    exact (hzM r hr).of_dvd_left
      (Finset.prod_dvd_prod_of_dvd _ _
        (fun j _ => (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hdr j)).1))
  have hcompatible (e : Fin 1 → ℕ) (he : e ∈ Du)
      (d : Fin 38 → ℕ) (n : ℕ)
      (hen : e 0 ∣ n + h i) (hdn : ∀ j, d j ∣ n + h (i.succAbove j)) :
      Nat.Coprime (e 0) (∏ j, d j) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro j
    by_contra hc
    obtain ⟨p, hp, hpe, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpW' : ¬ p ∣ W := hp.coprime_iff_not_dvd.mp
      ((hU e he).2.2.of_dvd_left hpe)
    have hdist : p ∣ Nat.dist (h i) (h (i.succAbove j)) := by
      rw [← Nat.dist_add_add_left n, Nat.dist]
      exact dvd_add (Nat.dvd_sub (hpe.trans hen) (hpd.trans (hdn j)))
        (Nat.dvd_sub (hpd.trans (hdn j)) (hpe.trans hen))
    exact hpW' (hcover i (i.succAbove j)
      (fun hij => (Fin.succAbove_ne i j) (hinj hij).symm) p hp hdist)
  let E : ((Fin 1 → ℕ) × (Fin 38 → ℕ)) ≃ (Fin 39 → ℕ) :=
    ((Equiv.funUnique (Fin 1) ℕ).prodCongr (Equiv.refl (Fin 38 → ℕ))).trans
      (Fin.insertNthEquiv (fun _ : Fin 39 => ℕ) i)
  let good := (Du ×ˢ Dz).filter (fun t => Nat.Coprime (t.1 0) (∏ j, t.2 j))
  let D := good.map E.toEmbedding
  let lam : (Fin 39 → ℕ) → ℝ := fun a =>
    PrimeGap182.Selberg.selbergCoefficient u (fun _ => a i) *
      PrimeGap182.Selberg.selbergCoefficient z (fun j => a (i.succAbove j))
  have hE (t : (Fin 1 → ℕ) × (Fin 38 → ℕ)) :
      E t = i.insertNth (t.1 0) t.2 := rfl
  have hfun (e : Fin 1 → ℕ) : (fun _ : Fin 1 => e 0) = e :=
    funext fun j => congrArg e (Subsingleton.elim 0 j)
  have hlam (t : (Fin 1 → ℕ) × (Fin 38 → ℕ)) :
      lam (E t) = PrimeGap182.Selberg.selbergCoefficient u t.1 * PrimeGap182.Selberg.selbergCoefficient z t.2 := by
    simp only [lam, hE, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hfun]
  have hdiv (t : (Fin 1 → ℕ) × (Fin 38 → ℕ)) (n : ℕ) :
      (∀ j, E t j ∣ n + h j) ↔
        t.1 0 ∣ n + h i ∧ ∀ j, t.2 j ∣ n + h (i.succAbove j) := by
    rw [Fin.forall_iff_succAbove i]
    simp only [hE, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have hD : ∀ a ∈ D,
      Squarefree (∏ j, a j) ∧ Nat.Coprime (∏ j, a j) W ∧
        Nat.Coprime (∏ j, a j) M ∧ ∀ j, a j ∣ q := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨ht, hcop⟩ := Finset.mem_filter.mp ht
    obtain ⟨he, hd⟩ := Finset.mem_product.mp ht
    have hu' := hU t.1 he
    have hz' := hZ t.2 hd
    change Squarefree (∏ j, E t j) ∧ Nat.Coprime (∏ j, E t j) W ∧
      Nat.Coprime (∏ j, E t j) M ∧ _
    rw [hE, Fin.prod_insertNth]
    refine ⟨(Nat.squarefree_mul hcop).mpr ⟨hu'.1, hz'.1⟩,
      hu'.2.2.mul_left hz'.2.2, (hUM t.1 he).mul_left (hZM t.2 hd), ?_⟩
    change ∀ j, E t j ∣ q
    rw [hE]
    rw [Fin.forall_iff_succAbove i]
    simpa only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using
      And.intro hu'.2.1 hz'.2.1
  have hvalue (n : ℕ) :
      L (n + h i) * C n =
        ∑ a ∈ D, if ∀ j, a j ∣ n + h j then lam a else 0 := by
    have hexpand :
        L (n + h i) * C n =
          ∑ t ∈ Du ×ˢ Dz,
            if t.1 0 ∣ n + h i ∧ ∀ j, t.2 j ∣ n + h (i.succAbove j) then
              PrimeGap182.Selberg.selbergCoefficient u t.1 * PrimeGap182.Selberg.selbergCoefficient z t.2
            else 0 := by
      simp only [L, C, Finset.sum_mul_sum, Finset.sum_product,
        ite_mul, mul_ite, mul_zero, zero_mul, ← ite_and, and_comm]
    rw [hexpand]
    change _ = ∑ a ∈ good.map E.toEmbedding,
      if ∀ j, a j ∣ n + h j then lam a else 0
    rw [Finset.sum_map]
    change _ = ∑ t ∈ good, if ∀ j, E t j ∣ n + h j then lam (E t) else 0
    simp_rw [hdiv, hlam]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t ht hnot
    have hc : ¬ Nat.Coprime (t.1 0) (∏ j, t.2 j) :=
      fun hc => hnot (Finset.mem_filter.mpr ⟨ht, hc⟩)
    have hn : ¬ (t.1 0 ∣ n + h i ∧ ∀ j, t.2 j ∣ n + h (i.succAbove j)) :=
      fun hn => hc (hcompatible t.1 (Finset.mem_product.mp ht).1 t.2 n hn.1 hn.2)
    exact ite_eq_right hn
  have hl1 : (∑ a ∈ D, |lam a|) ≤
      (∑ e ∈ Du, |PrimeGap182.Selberg.selbergCoefficient u e|) *
        (∑ d ∈ Dz, |PrimeGap182.Selberg.selbergCoefficient z d|) := by
    calc
      _ = ∑ t ∈ good,
          |PrimeGap182.Selberg.selbergCoefficient u t.1| * |PrimeGap182.Selberg.selbergCoefficient z t.2| := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro t _
        change |lam (E t)| = _
        rw [hlam, abs_mul]
      _ ≤ ∑ t ∈ Du ×ˢ Dz,
          |PrimeGap182.Selberg.selbergCoefficient u t.1| * |PrimeGap182.Selberg.selbergCoefficient z t.2| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by rw [Finset.sum_product, Finset.sum_mul_sum]
  refine ⟨D, lam, hD, ?_, hl1⟩
  intro n
  refine (hvalue n).trans ?_
  unfold divisorRootOn
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : ∀ j, d j ∣ n + h j <;> simp only [hd, ite_false]

#print axioms auxiliary_product_divisor_representation

end PrimeGap182Analytic
