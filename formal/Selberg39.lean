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
# Selberg arithmetic at arity 39

Adapted from the pinned public source, lines 177733--189859.
The generator records every changed code token. Legacy exceptional-defect
templates in this block retain their explicit old defect; the new sharp
minorant and its distribution are connected in separate modules.
-/

open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
open scoped MeasureTheory.BoundedContinuousFunction Pointwise
open MeasureTheory AddChar Filter Metric
open PrimeGap186

namespace PrimeGap182.Selberg
section
open Finset

/--
The selected coordinate set encoded by a Boolean choice of the distinguished coordinate `i` and
an optional coordinate from its `39`-element complement.
-/
def auxiliaryPrimeState (i : Fin 39) (s : Bool × Option (Fin 38)) :
    Finset (Fin 39) :=
  (if s.1 then {i} else ∅) ∪ s.2.toFinset.map i.succAboveEmb

/--
The local divisibility contrast `(1 - p * 1_{p ∣ n + h j}) / (p - 1)`. For prime `p`, it equals
`-1` on the forbidden residue class and `1 / (p - 1)` elsewhere.
-/
noncomputable def selbergPrimePsi
    (p : ℕ) (h : Fin 39 → ℕ) (j : Fin 39) (n : ℕ) : ℝ :=
  (1 - (p : ℝ) * (if p ∣ n + h j then 1 else 0)) / ((p : ℝ) - 1)

/--
The normalized residue average of the product of the two auxiliary-state basis functions modulo
`p`. Each basis function is the product of the local divisibility contrasts at its selected
coordinates.
-/
noncomputable def auxiliaryCategoricalGram
    (p : ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (s t : Bool × Option (Fin 38)) : ℝ :=
  (1 / (p : ℝ)) * ∑ n ∈ Finset.range p,
    (∏ j ∈ auxiliaryPrimeState i s, selbergPrimePsi p h j n) *
      (∏ j ∈ auxiliaryPrimeState i t, selbergPrimePsi p h j n)

/--
The analogous auxiliary-state Gram entry in the independent Boolean model, where each coordinate
has weight `1 / p` for `true` and `1 - 1 / p` for `false`. The sum runs over all `40`-coordinate
Boolean assignments.
-/
noncomputable def auxiliaryIndependentGram
    (p : ℕ) (i : Fin 39) (s t : Bool × Option (Fin 38)) : ℝ :=
  let ψ : Bool → ℝ :=
    fun b => (1 - (p : ℝ) * (if b then 1 else 0)) / ((p : ℝ) - 1)
  ∑ ω : Fin 39 → Bool,
    (∏ j : Fin 39, if ω j then 1 / (p : ℝ) else 1 - 1 / (p : ℝ)) *
      (∏ j ∈ auxiliaryPrimeState i s, ψ (ω j)) *
        (∏ j ∈ auxiliaryPrimeState i t, ψ (ω j))

theorem difference_prime_dvd_presieving (H : Finset ℕ) (x : ℝ)
    {a b p : ℕ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hp : p.Prime) (hpd : p ∣ Nat.dist a b) : p ∣ presievingModulus H x := by
  classical
  unfold presievingModulus
  apply Finset.dvd_prod_of_mem (fun q : ℕ => q)
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨b, hb,
    Nat.mem_primeFactors.mpr ⟨hp, hpd, fun hzero => hab (Nat.eq_of_dist_eq_zero hzero)⟩⟩⟩

theorem auxiliaryPrimeState_false_none (i : Fin 39) :
    auxiliaryPrimeState i (false, none) = ∅ := by
  simp [auxiliaryPrimeState]

theorem auxiliaryPrimeState_true_none (i : Fin 39) :
    auxiliaryPrimeState i (true, none) = {i} := by
  simp [auxiliaryPrimeState]

theorem auxiliaryPrimeState_false_some (i : Fin 39) (j : Fin 38) :
    auxiliaryPrimeState i (false, some j) = {i.succAbove j} := by
  simp [auxiliaryPrimeState]

theorem auxiliaryPrimeState_true_some (i : Fin 39) (j : Fin 38) :
    auxiliaryPrimeState i (true, some j) = {i, i.succAbove j} := by
  simp [auxiliaryPrimeState]

theorem auxiliaryPrimeState_injective (i : Fin 39) :
    Function.Injective (auxiliaryPrimeState i) := by
  classical
  have hmem (s : Bool × Option (Fin 38)) :
      i ∈ auxiliaryPrimeState i s ↔ s.1 := by
    rcases s with ⟨b, o⟩
    cases b <;> cases o <;> simp [auxiliaryPrimeState]
  have herase (s : Bool × Option (Fin 38)) :
      (auxiliaryPrimeState i s).erase i = s.2.toFinset.map i.succAboveEmb := by
    rcases s with ⟨b, o⟩
    cases b <;> cases o <;> simp [auxiliaryPrimeState]
  intro s t hst
  have hb : s.1 = t.1 := by
    apply Bool.eq_iff_iff.mpr
    rw [← hmem s, ← hmem t, hst]
  have ho : s.2.toFinset = t.2.toFinset := by
    apply Finset.map_injective i.succAboveEmb
    rw [← herase s, ← herase t, hst]
  apply Prod.ext hb
  cases hs : s.2 <;> cases ht : t.2 <;> simp_all

theorem auxiliaryPrimeState_image (i : Fin 39) :
    Finset.univ.image (auxiliaryPrimeState i) =
      ({∅, {i}} : Finset (Finset (Fin 39))) ∪
        ((Finset.univ.erase i).image fun j => {j}) ∪
        ((Finset.univ.erase i).image fun j => {i, j}) := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨⟨b, o⟩, _, rfl⟩ := Finset.mem_image.mp hS
    cases b with
    | false =>
      cases o with
      | none => simp [auxiliaryPrimeState_false_none]
      | some j =>
        rw [auxiliaryPrimeState_false_some]
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i.succAbove j, by simp, rfl⟩))
    | true =>
      cases o with
      | none => simp [auxiliaryPrimeState_true_none]
      | some j =>
        rw [auxiliaryPrimeState_true_some]
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i.succAbove j, by simp, rfl⟩)
  · intro hS
    rcases Finset.mem_union.mp hS with hS | hS
    · rcases Finset.mem_union.mp hS with hS | hS
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hS
        rcases hS with rfl | rfl
        · exact Finset.mem_image.mpr ⟨(false, none), Finset.mem_univ _,
            auxiliaryPrimeState_false_none i⟩
        · exact Finset.mem_image.mpr ⟨(true, none), Finset.mem_univ _,
            auxiliaryPrimeState_true_none i⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
        obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Finset.ne_of_mem_erase hj)
        refine Finset.mem_image.mpr ⟨(false, some k), Finset.mem_univ _, ?_⟩
        rw [auxiliaryPrimeState_false_some, hk]
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Finset.ne_of_mem_erase hj)
      refine Finset.mem_image.mpr ⟨(true, some k), Finset.mem_univ _, ?_⟩
      rw [auxiliaryPrimeState_true_some, hk]

theorem auxiliaryPrimeState_card_states (i : Fin 39) :
    (Finset.univ.image (auxiliaryPrimeState i)).card = 78 := by
  classical
  rw [Finset.card_image_of_injective _ (auxiliaryPrimeState_injective i)]
  simp

theorem auxiliaryIndependentGram_mass (p : ℕ) (i : Fin 39) (hp : p.Prime)
    (hD : ∀ s t : Bool × Option (Fin 38),
      auxiliaryIndependentGram p i s t =
        if s = t then 1 / ((p : ℝ) - 1) ^ (auxiliaryPrimeState i s).card else 0) :
    let a : ℝ := (p : ℝ) - 1
    let d : ℝ := ∑ s : Bool × Option (Fin 38),
      ∑ t : Bool × Option (Fin 38), auxiliaryIndependentGram p i s t
    d = (1 + 38 / a) * (1 + 1 / a) ∧
      1 ≤ d ∧ d ≤ (1 + 1 / a) ^ 39 := by
  classical
  dsimp only
  let a : ℝ := (p : ℝ) - 1
  have ha1 : 1 ≤ a := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    dsimp [a]
    linarith
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ha1)
  have hb : 0 ≤ 1 / a := div_nonneg zero_le_one (le_trans zero_le_one ha1)
  have hdiag :
      (∑ s : Bool × Option (Fin 38),
        ∑ t : Bool × Option (Fin 38), auxiliaryIndependentGram p i s t) =
      ∑ s : Bool × Option (Fin 38), 1 / a ^ (auxiliaryPrimeState i s).card := by
    simp only [a, hD, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hmass :
      (∑ s : Bool × Option (Fin 38), 1 / a ^ (auxiliaryPrimeState i s).card) =
        (1 + 38 / a) * (1 + 1 / a) := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [auxiliaryPrimeState]
    field_simp [ha]
    ring
  have hd := hdiag.trans hmass
  refine ⟨hd, ?_, ?_⟩
  · rw [hd]
    have h39 : 0 ≤ 38 / a := div_nonneg (by norm_num) (le_trans zero_le_one ha1)
    nlinarith [mul_nonneg h39 hb]
  · rw [hd]
    have hpow : 1 + (38 : ℝ) * (1 / a) ≤ (1 + 1 / a) ^ 38 :=
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1 / a) 38
    calc
      (1 + 38 / a) * (1 + 1 / a) =
          (1 + (38 : ℝ) * (1 / a)) * (1 + 1 / a) := by ring
      _ ≤ (1 + 1 / a) ^ 38 * (1 + 1 / a) :=
        mul_le_mul_of_nonneg_right hpow (by linarith)
      _ = (1 + 1 / a) ^ 39 := (pow_succ _ 38).symm

theorem auxiliaryIndependentGram_product (p : ℕ) (i : Fin 39)
    (s t : Bool × Option (Fin 38)) :
    let ψ : Bool → ℝ :=
      fun b => (1 - (p : ℝ) * (if b then 1 else 0)) / ((p : ℝ) - 1)
    auxiliaryIndependentGram p i s t =
      ∏ j : Fin 39, ∑ b : Bool,
        (if b then 1 / (p : ℝ) else 1 - 1 / (p : ℝ)) *
          (if j ∈ auxiliaryPrimeState i s then ψ b else 1) *
            (if j ∈ auxiliaryPrimeState i t then ψ b else 1) := by
  classical
  dsimp only
  rw [Fintype.prod_sum]
  simp only [auxiliaryIndependentGram, Finset.prod_mul_distrib,
    Finset.prod_ite_mem_eq]

theorem auxiliaryIndependentGram_eq (p : ℕ) (i : Fin 39)
    (s t : Bool × Option (Fin 38)) (hp : p.Prime)
    (hinj : Function.Injective (auxiliaryPrimeState i)) :
    auxiliaryIndependentGram p i s t =
      if s = t then 1 / ((p : ℝ) - 1) ^ (auxiliaryPrimeState i s).card else 0 := by
  classical
  let S := auxiliaryPrimeState i s
  let T := auxiliaryPrimeState i t
  let ψ : Bool → ℝ :=
    fun b => (1 - (p : ℝ) * (if b then 1 else 0)) / ((p : ℝ) - 1)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have ha : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1
  have hmoment (j : Fin 39) :
      (∑ b : Bool,
        (if b then 1 / (p : ℝ) else 1 - 1 / (p : ℝ)) *
          (if j ∈ S then ψ b else 1) * (if j ∈ T then ψ b else 1)) =
        if j ∈ S then (if j ∈ T then 1 / ((p : ℝ) - 1) else 0)
        else (if j ∈ T then 0 else 1) := by
    dsimp only [ψ]
    rw [Fintype.sum_bool]
    by_cases hs : j ∈ S <;> by_cases ht : j ∈ T
    all_goals
      simp only [hs, ht, Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, sub_zero]
      field_simp [hp0, ha]
      ring
  calc
    auxiliaryIndependentGram p i s t =
        ∏ j : Fin 39,
          if j ∈ S then (if j ∈ T then 1 / ((p : ℝ) - 1) else 0)
          else (if j ∈ T then 0 else 1) := by
      rw [auxiliaryIndependentGram_product]
      exact Finset.prod_congr rfl fun j _ => hmoment j
    _ = if s = t then 1 / ((p : ℝ) - 1) ^ S.card else 0 := by
      by_cases hst : s = t
      · subst t
        rw [ite_eq_left rfl]
        simp +contextual [S, T]
      · rw [ite_eq_right hst]
        have hST : S ≠ T := fun h => hst (hinj h)
        have hdiff : ∃ j : Fin 39, ¬ (j ∈ S ↔ j ∈ T) := by
          by_contra! h
          exact hST (Finset.ext h)
        obtain ⟨j, hj⟩ := hdiff
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        by_cases hs : j ∈ S <;> by_cases ht : j ∈ T <;> simp_all

theorem physical_residues_injective
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (x : ℝ) (p : ℕ) (hp : p.Prime)
    (hpW : ¬ p ∣ presievingModulus 𝓗 x) :
    Function.Injective (fun j : Fin 39 =>
      (𝓗.orderEmbOfFin h𝓗_card j : ZMod p)) := by
  intro j k heq
  apply (𝓗.orderEmbOfFin h𝓗_card).injective
  by_contra hne
  apply hpW
  apply difference_prime_dvd_presieving 𝓗 x
    (𝓗.orderEmbOfFin_mem h𝓗_card j)
    (𝓗.orderEmbOfFin_mem h𝓗_card k) hne hp
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ p).mp heq
  rw [Nat.dist]
  exact dvd_add hmod.symm.dvd' hmod.dvd'

theorem residue_hit_unique (p : ℕ) (h : Fin 39 → ℕ)
    (hinj : Function.Injective (fun j => (h j : ZMod p)))
    (n : ℕ) (j k : Fin 39) (hj : p ∣ n + h j) (hk : p ∣ n + h k) : j = k := by
  apply hinj
  have hj' : (n : ZMod p) + (h j : ZMod p) = 0 := by
    simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff (n + h j) p).mpr hj
  have hk' : (n : ZMod p) + (h k : ZMod p) = 0 := by
    simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff (n + h k) p).mpr hk
  exact add_left_cancel (hj'.trans hk'.symm)

theorem single_pole_count (p c : ℕ) (hp : 0 < p) :
    (∑ n ∈ Finset.range p, if p ∣ n + c then (1 : ℝ) else 0) = 1 := by
  classical
  let : NeZero p := ⟨ne_of_gt hp⟩
  let m : ℕ := (-(c : ZMod p)).val
  have hm : m ∈ Finset.range p := Finset.mem_range.mpr (ZMod.val_lt _)
  have hiff (n : ℕ) (hn : n ∈ Finset.range p) : p ∣ n + c ↔ n = m := by
    constructor
    · intro hd
      have heq : (n : ZMod p) = -(c : ZMod p) := by
        apply eq_neg_iff_add_eq_zero.mpr
        simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff (n + c) p).mpr hd
      have hv := congrArg ZMod.val heq
      simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)] using hv
    · rintro rfl
      apply (ZMod.natCast_eq_zero_iff (m + c) p).mp
      simp only [Nat.cast_add, m, ZMod.natCast_zmod_val, neg_add_cancel]
  calc
    _ = ∑ n ∈ Finset.range p, if n = m then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl fun n hn => by simp only [hiff n hn]
    _ = 1 := by simp [hm]

theorem categorical_numerator_identity (p : ℕ) (h : Fin 39 → ℕ)
    (hinj : Function.Injective (fun j => (h j : ZMod p)))
    (S T : Finset (Fin 39)) (n : ℕ) :
    (∏ j ∈ S, (1 - (p : ℝ) * (if p ∣ n + h j then 1 else 0))) *
        (∏ j ∈ T, (1 - (p : ℝ) * (if p ∣ n + h j then 1 else 0))) =
      1 - (p : ℝ) * (∑ j ∈ S ∪ T, if p ∣ n + h j then 1 else 0) +
        (p : ℝ) * ((p : ℝ) - 1) *
          (∑ j ∈ S ∩ T, if p ∣ n + h j then 1 else 0) := by
  classical
  by_cases hex : ∃ j : Fin 39, p ∣ n + h j
  · obtain ⟨j, hj⟩ := hex
    have hiff (k : Fin 39) : p ∣ n + h k ↔ k = j :=
      ⟨fun hk => residue_hit_unique p h hinj n k j hk hj, fun hk => hk ▸ hj⟩
    simp_rw [hiff, mul_ite, mul_one, mul_zero, sub_ite, sub_zero]
    by_cases hs : j ∈ S <;> by_cases ht : j ∈ T <;> simp [hs, ht]
    ring
  · simp [not_exists.mp hex]

theorem auxiliaryCategoricalGram_eq (p : ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (s t : Bool × Option (Fin 38)) (hp : p.Prime)
    (hinj : Function.Injective (fun j => (h j : ZMod p))) :
    let a : ℝ := (p : ℝ) - 1
    let S := auxiliaryPrimeState i s
    let T := auxiliaryPrimeState i t
    auxiliaryCategoricalGram p h i s t =
      (1 - ((S ∪ T).card : ℝ) + a * ((S ∩ T).card : ℝ)) /
        a ^ (S.card + T.card) := by
  classical
  let a : ℝ := (p : ℝ) - 1
  let S := auxiliaryPrimeState i s
  let T := auxiliaryPrimeState i t
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have ha : a ≠ 0 := sub_ne_zero.mpr hp1
  have hterm (n : ℕ) :
      (∏ j ∈ S, selbergPrimePsi p h j n) *
          (∏ j ∈ T, selbergPrimePsi p h j n) =
        (1 - (p : ℝ) * (∑ j ∈ S ∪ T, if p ∣ n + h j then 1 else 0) +
          (p : ℝ) * a * (∑ j ∈ S ∩ T, if p ∣ n + h j then 1 else 0)) /
            a ^ (S.card + T.card) := by
    simp only [selbergPrimePsi, Finset.prod_div_distrib, Finset.prod_const,
      div_mul_div_comm, ← pow_add]
    exact congrArg (fun z : ℝ => z / a ^ (S.card + T.card))
      (categorical_numerator_identity p h hinj S T n)
  have hmass (R : Finset (Fin 39)) :
      (∑ n ∈ Finset.range p, ∑ j ∈ R, if p ∣ n + h j then (1 : ℝ) else 0) =
        (R.card : ℝ) := by
    rw [Finset.sum_comm]
    simp_rw [single_pole_count p _ hp.pos]
    simp
  change (1 / (p : ℝ)) * (∑ n ∈ Finset.range p,
      (∏ j ∈ S, selbergPrimePsi p h j n) * (∏ j ∈ T, selbergPrimePsi p h j n)) =
    (1 - ((S ∪ T).card : ℝ) + a * ((S ∩ T).card : ℝ)) / a ^ (S.card + T.card)
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hmass (S ∪ T), hmass (S ∩ T)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp [hp0, ha]

theorem selbergPrimePsi_pair (p : ℕ) (h : Fin 39 → ℕ) (hp : p.Prime)
    (hinj : Function.Injective (fun j => (h j : ZMod p)))
    (j k : Fin 39) (hjk : j ≠ k) (n : ℕ) :
    selbergPrimePsi p h j n * selbergPrimePsi p h k n =
      (selbergPrimePsi p h j n + selbergPrimePsi p h k n) / ((p : ℝ) - 1) -
        1 / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have ha : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1
  have hnot : ¬ (p ∣ n + h j ∧ p ∣ n + h k) :=
    fun hh => hjk (residue_hit_unique p h hinj n j k hh.1 hh.2)
  unfold selbergPrimePsi
  by_cases hj : p ∣ n + h j <;> by_cases hk : p ∣ n + h k
  · exact (hnot ⟨hj, hk⟩).elim
  all_goals
    simp only [hj, hk, ↓reduceIte, mul_one, mul_zero, sub_zero]
    field_simp [ha]
    ring

theorem auxiliary_abs_div_four_le (a z : ℝ) (ha : 0 < a)
    (hz : |z| ≤ 2 * a ^ 2) : |z / a ^ 4| ≤ 2 / a ^ 2 := by
  rw [abs_div, abs_of_pos (pow_pos ha 4),
    div_le_div_iff₀ (pow_pos ha 4) (pow_pos ha 2)]
  nlinarith [mul_le_mul_of_nonneg_right hz (sq_nonneg a)]

theorem auxiliary_state_formula_error (p : ℕ) (hp : p.Prime)
    (i : Fin 39) (s t : Bool × Option (Fin 38)) :
    let a : ℝ := (p : ℝ) - 1
    let S := auxiliaryPrimeState i s
    let T := auxiliaryPrimeState i t
    |(1 - ((S ∪ T).card : ℝ) + a * ((S ∩ T).card : ℝ)) /
        a ^ (S.card + T.card) - (if s = t then 1 / a ^ S.card else 0)| ≤
      8 / (p : ℝ) ^ 2 := by
  classical
  let a : ℝ := (p : ℝ) - 1
  let S := auxiliaryPrimeState i s
  let T := auxiliaryPrimeState i t
  let e : ℝ := (1 - ((S ∪ T).card : ℝ) + a * ((S ∩ T).card : ℝ)) /
    a ^ (S.card + T.card) - (if s = t then 1 / a ^ S.card else 0)
  change |e| ≤ 8 / (p : ℝ) ^ 2
  have hpcast : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have haa : a ≤ a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hapos.le]
  have hcases :
      e = 0 / a ^ 4 ∨ e = -(a ^ 2) / a ^ 4 ∨
        e = (a ^ 2 - a) / a ^ 4 ∨ e = -(2 * a) / a ^ 4 ∨
        e = -((a - 1) ^ 2) / a ^ 4 ∨ e = (a - 2) / a ^ 4 := by
    rcases s with ⟨b, u⟩
    rcases t with ⟨c, v⟩
    dsimp [e, S, T]
    by_cases huv : u = v <;>
      cases b <;> cases c <;> cases u <;> cases v <;>
      simp_all only [Nat.ofNat_le_cast, auxiliaryPrimeState, Bool.false_eq_true, ↓reduceIte,
        Option.toFinset_none, map_empty, union_idempotent, card_empty, CharP.cast_eq_zero,
        sub_zero, inter_self, mul_zero, add_zero, pow_zero, ne_eq, eq_comm, zero_ne_one,
        not_false_eq_true, div_self, sub_self, zero_div, true_or, reduceCtorEq,
        Option.some.injEq, Option.toFinset_some, map_singleton, Fin.succAboveEmb_apply,
        empty_union, card_singleton, Nat.cast_one, mul_one, zero_add, Nat.reduceAdd, pow_one,
        one_div, union_empty, notMem_empty, inter_singleton_of_notMem, Prod.mk.injEq, and_true,
        singleton_union, union_insert, mem_singleton, Fin.ne_succAbove, card_insert_of_notMem,
        Nat.cast_ofNat, inter_insert_of_notMem, inter_empty, insert_union, mem_insert, or_true,
        inter_singleton_of_mem, not_true_eq_false, and_false, Fin.succAbove_inj, and_self,
        or_self, or_false, insert_eq_of_mem, inter_insert_of_mem, insert_empty_eq] <;>
      solve
      | left; field_simp [ne_of_gt hapos]; ring
      | right; left; field_simp [ne_of_gt hapos]; ring
      | right; right; left; field_simp [ne_of_gt hapos]; ring
      | right; right; right; left; field_simp [ne_of_gt hapos]; ring
      | right; right; right; right; left; field_simp [ne_of_gt hapos]; ring
      | right; right; right; right; right; field_simp [ne_of_gt hapos]; ring
  have hsmall : |e| ≤ 2 / a ^ 2 := by
    rcases hcases with h | h | h | h | h | h <;> rw [h] <;>
      apply auxiliary_abs_div_four_le a _ hapos <;>
      rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg (a - 1)]
  refine hsmall.trans ?_
  have hp_eq : (p : ℝ) = a + 1 := by dsimp [a]; ring
  apply (div_le_div_iff₀ (pow_pos hapos 2) (sq_pos_of_pos (by linarith))).mpr
  rw [hp_eq]
  nlinarith [sq_nonneg (a - 1)]

open Classical in
theorem selberg39_auxiliary_local_gram
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (x : ℝ) (i : Fin 39) (p : ℕ)
    (hp : p.Prime) (hpW : ¬ p ∣ presievingModulus 𝓗 x) :
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let a : ℝ := (p : ℝ) - 1
    let A : Finset (Finset (Fin 39)) := Finset.univ.image (auxiliaryPrimeState i)
    let d : ℝ := ∑ s : Bool × Option (Fin 38),
      ∑ t : Bool × Option (Fin 38), auxiliaryIndependentGram p i s t
    Function.Injective (auxiliaryPrimeState i) ∧
      A = ({∅, {i}} : Finset (Finset (Fin 39))) ∪
        ((Finset.univ.erase i).image fun j => {j}) ∪
        ((Finset.univ.erase i).image fun j => {i, j}) ∧
      A.card = 78 ∧
      (∀ j : Fin 38, ∀ n : ℕ,
        selbergPrimePsi p h i n * selbergPrimePsi p h (i.succAbove j) n =
          (selbergPrimePsi p h i n + selbergPrimePsi p h (i.succAbove j) n) / a -
            1 / a ^ 2) ∧
      (∀ s t : Bool × Option (Fin 38),
        let S := auxiliaryPrimeState i s
        let T := auxiliaryPrimeState i t
        auxiliaryCategoricalGram p h i s t =
            (1 - ((S ∪ T).card : ℝ) + a * ((S ∩ T).card : ℝ)) /
              a ^ (S.card + T.card) ∧
          auxiliaryIndependentGram p i s t =
            (if s = t then 1 / a ^ S.card else 0) ∧
          |auxiliaryCategoricalGram p h i s t -
            auxiliaryIndependentGram p i s t| ≤ 8 / (p : ℝ) ^ 2) ∧
      (∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38),
        |auxiliaryCategoricalGram p h i s t -
          auxiliaryIndependentGram p i s t|) ≤ 48672 / (p : ℝ) ^ 2 ∧
      d = (1 + 38 / a) * (1 + 1 / a) ∧
      1 ≤ d ∧ d ≤ (1 + 1 / a) ^ 39 := by
  dsimp only
  let h : Fin 39 → ℕ :=
    𝓗.orderEmbOfFin h𝓗_card
  have hres : Function.Injective (fun j => (h j : ZMod p)) :=
    physical_residues_injective (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) x p hp hpW
  have hD := fun s t => auxiliaryIndependentGram_eq p i s t hp
    (auxiliaryPrimeState_injective i)
  have hK := fun s t => auxiliaryCategoricalGram_eq p h i s t hp hres
  have herr (s t : Bool × Option (Fin 38)) :
      |auxiliaryCategoricalGram p h i s t - auxiliaryIndependentGram p i s t| ≤
        8 / (p : ℝ) ^ 2 := by
    rw [hK s t, hD s t]
    exact auxiliary_state_formula_error p hp i s t
  refine ⟨auxiliaryPrimeState_injective i, auxiliaryPrimeState_image i,
    auxiliaryPrimeState_card_states i, ?_, ?_, ?_,
    auxiliaryIndependentGram_mass p i hp hD⟩
  · intro j n
    exact selbergPrimePsi_pair p h hp hres i (i.succAbove j) (Fin.ne_succAbove i j) n
  · intro s t
    exact ⟨hK s t, hD s t, herr s t⟩
  · calc
      _ ≤ ∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38),
          (8 / (p : ℝ) ^ 2) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => herr s t
      _ = 48672 / (p : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_bool, Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
        ring

/-!
## Selberg coefficients and quadratic moments
-/

/-- The normalized input in Equation (3.2) of the main paper is `Y(r) = y_r / B_R^m`.
For a nonzero divisor sum, squarefree product support gives Moebius multiplicativity.
The scalar and product identities below make this normalization explicit. -/
noncomputable def selbergCoefficient
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ) (d : ι → ℕ) : ℝ := by
  classical
  exact (ArithmeticFunction.moebius (∏ i, d i) : ℝ) *
    (∏ i, (d i : ℝ)) *
    y.sum (fun r yr =>
      if ∀ i, d i ∣ r i then yr / (∏ i, ((r i).totient : ℝ)) else 0)

theorem coprime_of_squarefree_fintype_prod
    {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hd : Squarefree (∏ i, d i)) {i j : ι} (hij : i ≠ j) :
    Nat.Coprime (d i) (d j) := by
  classical
  apply Nat.coprime_of_squarefree_mul
  apply hd.squarefree_of_dvd
  simpa [Finset.prod_pair hij] using
    Finset.prod_dvd_prod_of_subset ({i, j} : Finset ι) Finset.univ d (by simp)

theorem selbergCoefficient_eq_prod
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ)
    (hy : ∀ r ∈ y.support, Squarefree (∏ i, r i)) (d : ι → ℕ) :
    selbergCoefficient y d =
      (∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ)) *
        y.sum (fun r yr =>
          if ∀ i, d i ∣ r i then yr / (∏ i, ((r i).totient : ℝ)) else 0) := by
  classical
  rw [selbergCoefficient, Finsupp.mul_sum, Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro r hr
  by_cases hdr : ∀ i, d i ∣ r i
  · have hd : Squarefree (∏ i, d i) :=
      (hy r hr).squarefree_of_dvd (Finset.prod_dvd_prod_of_dvd d r (fun i _ => hdr i))
    have hmu : (ArithmeticFunction.moebius (∏ i, d i) : ℝ) =
        ∏ i, (ArithmeticFunction.moebius (d i) : ℝ) := by
      exact_mod_cast ArithmeticFunction.IsMultiplicative.map_prod d
        ArithmeticFunction.isMultiplicative_moebius Finset.univ
        (fun i _ j _ hij => coprime_of_squarefree_fintype_prod d hd hij)
    simp only [ite_eq_left hdr, hmu, Finset.prod_mul_distrib]
  · simp only [ite_eq_right hdr, mul_zero]

theorem auxiliary_prime_selection_mem (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : P → Bool) :
    (∏ p : P, if b p then (p : ℕ) else 1) ∈ (∏ p ∈ P, p).divisors := by
  classical
  refine Nat.mem_divisors.mpr ⟨?_, (squarefree_prime_prod P hP).ne_zero⟩
  rw [← Finset.prod_coe_sort P (fun p : ℕ => p)]
  apply Finset.prod_dvd_prod_of_dvd
  intro p _
  split_ifs <;> simp

theorem auxiliary_prime_selection_dvd_iff (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : P → Bool) (p : P) :
    (p : ℕ) ∣ (∏ a : P, if b a then (a : ℕ) else 1) ↔ b p = true := by
  classical
  rw [(hP p.val p.property).prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨a, _, ha⟩
    by_cases hb : b a = true
    · rw [ite_eq_left hb] at ha
      have hap : a = p := Subtype.ext
        (((hP a.val a.property).dvd_iff_eq (hP p.val p.property).ne_one).mp ha)
      simpa only [hap] using hb
    · rw [ite_eq_right hb] at ha
      exact False.elim ((hP p.val p.property).ne_one (Nat.dvd_one.mp ha))
  · intro hp
    refine ⟨p, Finset.mem_univ p, ?_⟩
    simp only [hp, ite_true, dvd_refl]

theorem auxiliary_prime_selection_recover (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) (hr : r ∈ (∏ p ∈ P, p).divisors) :
    (∏ p : P, if decide ((p : ℕ) ∣ r) then (p : ℕ) else 1) = r := by
  classical
  have hq := (squarefree_prime_prod P hP).ne_zero
  calc
    _ = ∏ p ∈ P.filter (fun p => p ∣ r), p := by
      simp only [Finset.prod_filter, decide_eq_true_eq]
      exact Finset.prod_coe_sort P (fun p : ℕ => if p ∣ r then p else 1)
    _ = ∏ p ∈ r.primeFactors, p := by
      rw [← Nat.primeFactors_prod hP,
        Nat.primeFactors_filter_dvd_of_dvd hq (Nat.mem_divisors.mp hr).1]
    _ = r := Nat.prod_primeFactors_of_squarefree
      ((squarefree_prime_prod P hP).squarefree_of_dvd (Nat.mem_divisors.mp hr).1)

theorem auxiliary_root_valid (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (σ : P → Bool × Option (Fin 38)) :
    let q : ℕ := ∏ p ∈ P, p
    let rootA : Fin 1 → ℕ := fun _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : Fin 38 → ℕ :=
      fun j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    rootA 0 ∈ q.divisors ∧ Squarefree (∏ j, rootR j) ∧
      ∀ j, rootR j ∈ q.divisors := by
  classical
  dsimp only
  refine ⟨auxiliary_prime_selection_mem P hP (fun p => (σ p).1), ?_, ?_⟩
  · have hprod :
        (∏ j : Fin 38, ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1) =
          ∏ p : P, if (σ p).2.isSome then (p : ℕ) else 1 := by
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro p _
      cases (σ p).2 <;> simp
    rw [hprod]
    exact (squarefree_prime_prod P hP).squarefree_of_dvd
      (Nat.mem_divisors.mp
        (auxiliary_prime_selection_mem P hP (fun p => (σ p).2.isSome))).1
  · intro j
    simpa only [decide_eq_true_eq] using
      auxiliary_prime_selection_mem P hP (fun p => decide ((σ p).2 = some j))

theorem auxiliary_root_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
      fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
      fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    Function.Injective (fun σ => (rootA σ, rootR σ)) := by
  classical
  intro rootA rootR σ τ hστ
  have hA : rootA σ = rootA τ := congrArg Prod.fst hστ
  have hR : rootR σ = rootR τ := congrArg Prod.snd hστ
  have hRiff (ω : P → Bool × Option (Fin 38)) (p : P) (j : Fin 38) :
      (p : ℕ) ∣ rootR ω j ↔ (ω p).2 = some j := by
    simpa only [rootR, decide_eq_true_eq] using
      auxiliary_prime_selection_dvd_iff P hP
        (fun a => decide ((ω a).2 = some j)) p
  funext p
  apply Prod.ext
  · apply Bool.eq_iff_iff.mpr
    rw [← auxiliary_prime_selection_dvd_iff P hP (fun a => (σ a).1) p,
      ← auxiliary_prime_selection_dvd_iff P hP (fun a => (τ a).1) p]
    change (p : ℕ) ∣ rootA σ 0 ↔ (p : ℕ) ∣ rootA τ 0
    rw [hA]
  · apply Option.ext
    intro j
    rw [← hRiff σ p j, ← hRiff τ p j, hR]

theorem auxiliary_root_configuration (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    let q : ℕ := ∏ p ∈ P, p
    let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
      fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
      fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    ∀ (s : Fin 1 → ℕ) (r : Fin 38 → ℕ),
      (s 0 ∈ q.divisors ∧ Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) ↔
        ∃! σ : P → Bool × Option (Fin 38), rootA σ = s ∧ rootR σ = r := by
  classical
  intro q rootA rootR s r
  constructor
  · rintro ⟨hs, hsq, hr⟩
    have howner_unique (p : P) (j k : Fin 38)
        (hj : (p : ℕ) ∣ r j) (hk : (p : ℕ) ∣ r k) : j = k := by
      by_contra hjk
      exact (hP p.val p.property).ne_one
        (Nat.eq_one_of_dvd_coprimes
          (coprime_of_squarefree_fintype_prod r hsq hjk) hj hk)
    let owner (p : P) : Option (Fin 38) :=
      if H : ∃ j, (p : ℕ) ∣ r j then some H.choose else none
    have howner (p : P) (j : Fin 38) : owner p = some j ↔ (p : ℕ) ∣ r j := by
      dsimp only [owner]
      split_ifs with H
      · constructor
        · intro heq
          have hj : H.choose = j := Option.some.inj heq
          exact hj ▸ H.choose_spec
        · intro hj
          exact congrArg some (howner_unique p H.choose j H.choose_spec hj)
      · constructor
        · intro heq
          cases heq
        · intro hj
          exact False.elim (H ⟨j, hj⟩)
    let σ (p : P) : Bool × Option (Fin 38) := (decide ((p : ℕ) ∣ s 0), owner p)
    have hA : rootA σ = s := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact auxiliary_prime_selection_recover P hP (s 0) hs
    have hR : rootR σ = r := by
      funext j
      simpa only [rootR, σ, howner, decide_eq_true_eq] using
        auxiliary_prime_selection_recover P hP (r j) (hr j)
    refine ⟨σ, ⟨hA, hR⟩, ?_⟩
    intro τ hτ
    apply auxiliary_root_injective P hP
    exact Prod.ext (hτ.1.trans hA.symm) (hτ.2.trans hR.symm)
  · rintro ⟨σ, ⟨hA, hR⟩, _⟩
    have hv := auxiliary_root_valid P hP σ
    change rootA σ 0 ∈ q.divisors ∧ Squarefree (∏ j, rootR σ j) ∧
      (∀ j, rootR σ j ∈ q.divisors) at hv
    rw [hA, hR] at hv
    exact hv

theorem auxiliary_root_sum {M : Type*} [AddCommMonoid M]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : (Fin 1 → ℕ) → (Fin 38 → ℕ) → M) :
    let q : ℕ := ∏ p ∈ P, p
    let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
      fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
      fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    (∑ σ : P → Bool × Option (Fin 38), f (rootA σ) (rootR σ)) =
      ∑ s ∈ Fintype.piFinset (fun _ : Fin 1 => q.divisors),
        ∑ r ∈ (Fintype.piFinset (fun _ : Fin 38 => q.divisors)).filter
          (fun r => Squarefree (∏ j, r j)), f s r := by
  classical
  intro q rootA rootR
  let SA := Fintype.piFinset (fun _ : Fin 1 => q.divisors)
  let SR := (Fintype.piFinset (fun _ : Fin 38 => q.divisors)).filter
    (fun r => Squarefree (∏ j, r j))
  have hmem (s : Fin 1 → ℕ) (r : Fin 38 → ℕ) :
      (s, r) ∈ SA ×ˢ SR ↔
        s 0 ∈ q.divisors ∧ Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors := by
    simp only [SA, SR, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_filter,
      Fin.forall_fin_one, and_left_comm, and_comm]
  calc
    _ = ∑ sr ∈ SA ×ˢ SR, f sr.1 sr.2 := by
      refine Finset.sum_bij (fun σ _ => (rootA σ, rootR σ)) ?_ ?_ ?_ ?_
      · intro σ _
        exact (hmem _ _).mpr (auxiliary_root_valid P hP σ)
      · intro σ _ τ _ hστ
        exact auxiliary_root_injective P hP hστ
      · rintro ⟨s, r⟩ hsr
        obtain ⟨σ, hσ, _⟩ :=
          (auxiliary_root_configuration P hP s r).mp ((hmem s r).mp hsr)
        exact ⟨σ, Finset.mem_univ _, Prod.ext hσ.1 hσ.2⟩
      · intro σ _
        rfl
    _ = _ := Finset.sum_product SA SR (fun sr => f sr.1 sr.2)

theorem totient_eq_primeFactors_prod (n : ℕ) (hn : Squarefree n) :
    (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
  have hnat : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    apply mul_right_cancel₀ hn.ne_zero
    simpa only [Nat.prod_primeFactors_of_squarefree hn, mul_comm] using
      Nat.totient_mul_prod_primeFactors n
  rw [hnat, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (Nat.prime_of_mem_primeFactors hp).ne_zero), Nat.cast_one]

theorem selberg_scalar_pointwise_expansion (r t : ℕ) (hr : Squarefree r) :
    (∑ d ∈ r.divisors,
      if d ∣ t then (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) else 0) /
        (r.totient : ℝ) =
      ∏ p ∈ r.primeFactors,
        (1 - (p : ℝ) * (if p ∣ t then 1 else 0)) / ((p : ℝ) - 1) := by
  classical
  let f : ArithmeticFunction ℝ :=
    ⟨fun d => if d ∣ t then (d : ℝ) else 0, by simp⟩
  have hf : f.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f]
    · intro m n hmn
      change (if m * n ∣ t then ((m * n : ℕ) : ℝ) else 0) =
        (if m ∣ t then (m : ℝ) else 0) * (if n ∣ t then (n : ℝ) else 0)
      have hdiv : m * n ∣ t ↔ m ∣ t ∧ n ∣ t :=
        ⟨fun h => ⟨dvd_trans (dvd_mul_right m n) h,
          dvd_trans (dvd_mul_left n m) h⟩,
          fun h => hmn.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      by_cases hm : m ∣ t <;> by_cases hn : n ∣ t <;>
        simp [hdiv, hm, hn, Nat.cast_mul]
  rw [Finset.prod_div_distrib, totient_eq_primeFactors_prod r hr]
  congr 1
  calc
    (∑ d ∈ r.divisors,
        if d ∣ t then (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) else 0) =
        ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) * f d := by
      simp [f, mul_ite]
    _ = ∏ p ∈ r.primeFactors, (1 - f p) :=
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
        f hf hr).symm
    _ = ∏ p ∈ r.primeFactors, (1 - (p : ℝ) * (if p ∣ t then 1 else 0)) := by
      simp [f, mul_ite]

theorem selberg_pointwise_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y : (ι → ℕ) →₀ ℝ) (t : ι → ℕ)
    (hy : ∀ r ∈ y.support, Squarefree (∏ j, r j)) :
    let D := y.support.biUnion
      (fun r => Fintype.piFinset (fun j => (r j).divisors))
    (∑ d ∈ D, if ∀ j, d j ∣ t j then selbergCoefficient y d else 0) =
      ∑ r ∈ y.support, y r * ∏ j, ∏ p ∈ (r j).primeFactors,
        (1 - (p : ℝ) * (if p ∣ t j then 1 else 0)) / ((p : ℝ) - 1) := by
  classical
  intro D
  have hmuProd (d : ι → ℕ) (hd : Squarefree (∏ j, d j)) :
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ) =
        ∏ j, (ArithmeticFunction.moebius (d j) : ℝ) := by
    exact_mod_cast ArithmeticFunction.IsMultiplicative.map_prod d
      ArithmeticFunction.isMultiplicative_moebius Finset.univ
      (fun i _ j _ hij => coprime_of_squarefree_fintype_prod d hd hij)
  have hbox (r : ι → ℕ) (hr : Squarefree (∏ j, r j)) :
      (∑ d ∈ Fintype.piFinset (fun j => (r j).divisors),
        if ∀ j, d j ∣ t j then
          (ArithmeticFunction.moebius (∏ j, d j) : ℝ) * ∏ j, (d j : ℝ) else 0) /
          (∏ j, ((r j).totient : ℝ)) =
        ∏ j, ∏ p ∈ (r j).primeFactors,
          (1 - (p : ℝ) * (if p ∣ t j then 1 else 0)) / ((p : ℝ) - 1) := by
    calc
      _ = (∏ j, ∑ d ∈ (r j).divisors,
          if d ∣ t j then (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) else 0) /
            (∏ j, ((r j).totient : ℝ)) := by
        congr 1
        calc
          _ = ∑ d ∈ Fintype.piFinset (fun j => (r j).divisors),
              ∏ j, if d j ∣ t j then
                (ArithmeticFunction.moebius (d j) : ℝ) * (d j : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdr : ∀ j, d j ∣ r j := fun j =>
              Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hd j)
            rw [hmuProd d (hr.squarefree_of_dvd (Finset.prod_dvd_prod_of_dvd d r
              (fun j _ => hdr j))), Fintype.prod_ite_zero, Finset.prod_mul_distrib]
          _ = _ := (Finset.prod_univ_sum (fun j => (r j).divisors)
            (fun j d => if d ∣ t j then
              (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) else 0)).symm
      _ = ∏ j, (∑ d ∈ (r j).divisors,
          if d ∣ t j then (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) else 0) /
            ((r j).totient : ℝ) := by rw [Finset.prod_div_distrib]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        exact selberg_scalar_pointwise_expansion (r j) (t j)
          (hr.squarefree_of_dvd (Finset.dvd_prod_of_mem r (Finset.mem_univ j)))
  calc
    _ = ∑ d ∈ D, ∑ r ∈ y.support,
        (if (∀ j, d j ∣ t j) ∧ (∀ j, d j ∣ r j) then
          (ArithmeticFunction.moebius (∏ j, d j) : ℝ) * ∏ j, (d j : ℝ) else 0) *
            (y r / (∏ j, ((r j).totient : ℝ))) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [selbergCoefficient, Finsupp.sum]
      by_cases hdt : ∀ j, d j ∣ t j
      · simp [hdt, Finset.mul_sum, mul_ite, ite_mul]
      · simp [hdt]
    _ = ∑ r ∈ y.support, ∑ d ∈ D,
        (if (∀ j, d j ∣ t j) ∧ (∀ j, d j ∣ r j) then
          (ArithmeticFunction.moebius (∏ j, d j) : ℝ) * ∏ j, (d j : ℝ) else 0) *
            (y r / (∏ j, ((r j).totient : ℝ))) := Finset.sum_comm
    _ = ∑ r ∈ y.support, y r *
        ((∑ d ∈ Fintype.piFinset (fun j => (r j).divisors),
          if ∀ j, d j ∣ t j then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ) * ∏ j, (d j : ℝ) else 0) /
              (∏ j, ((r j).totient : ℝ))) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_mul]
      have hset : D.filter (fun d => ∀ j, d j ∣ r j) =
          Fintype.piFinset (fun j => (r j).divisors) := by
        ext d
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hdr⟩ j
          exact ⟨hdr j, ((hy r hr).squarefree_of_dvd
            (Finset.dvd_prod_of_mem r (Finset.mem_univ j))).ne_zero⟩
        · intro hdr
          refine ⟨Finset.mem_biUnion.mpr ⟨r, hr, ?_⟩, fun j => (hdr j).1⟩
          exact Fintype.mem_piFinset.mpr fun j => Nat.mem_divisors.mpr (hdr j)
      have hrestrict :
          (∑ d ∈ D, if (∀ j, d j ∣ t j) ∧ (∀ j, d j ∣ r j) then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ) * ∏ j, (d j : ℝ) else 0) =
          ∑ d ∈ Fintype.piFinset (fun j => (r j).divisors),
            if ∀ j, d j ∣ t j then
              (ArithmeticFunction.moebius (∏ j, d j) : ℝ) * ∏ j, (d j : ℝ) else 0 := by
        rw [← hset, Finset.sum_filter]
        simp only [← ite_and, and_comm]
      rw [hrestrict]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hbox r (hy r hr)]

theorem auxiliary_prime_selection_product (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : P → Bool) (f : ℕ → ℝ) :
    (∏ r ∈ (∏ p : P, if b p then (p : ℕ) else 1).primeFactors, f r) =
      ∏ p : P, if b p then f (p : ℕ) else 1 := by
  classical
  let n : ℕ := ∏ p : P, if b p then (p : ℕ) else 1
  have hn := Nat.mem_divisors.mp (auxiliary_prime_selection_mem P hP b)
  have hfilter := Nat.primeFactors_filter_dvd_of_dvd
    (squarefree_prime_prod P hP).ne_zero hn.1
  rw [Nat.primeFactors_prod hP] at hfilter
  change (∏ r ∈ n.primeFactors, f r) = _
  calc
    _ = ∏ r ∈ P, if r ∣ n then f r else 1 := by
      rw [← hfilter, Finset.prod_filter]
    _ = ∏ p : P, if b p then f (p : ℕ) else 1 := by
      rw [← Finset.prod_coe_sort P (fun r : ℕ => if r ∣ n then f r else 1)]
      apply Finset.prod_congr rfl
      intro p _
      change (if (p : ℕ) ∣ (∏ a : P, if b a then (a : ℕ) else 1)
        then f (p : ℕ) else 1) = _
      simp only [auxiliary_prime_selection_dvd_iff P hP b p]

theorem auxiliary_root_totient (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (i : Fin 39) (σ : P → Bool × Option (Fin 38)) :
    let rootA : Fin 1 → ℕ := fun _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : Fin 38 → ℕ :=
      fun j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    ((rootA 0).totient : ℝ) * (∏ j, ((rootR j).totient : ℝ)) =
      ∏ p : P, ((p : ℝ) - 1) ^ (auxiliaryPrimeState i (σ p)).card := by
  classical
  dsimp only
  have hphi (b : P → Bool) :
      ((∏ p : P, if b p then (p : ℕ) else 1).totient : ℝ) =
        ∏ p : P, if b p then (p : ℝ) - 1 else 1 := by
    have hn := (squarefree_prime_prod P hP).squarefree_of_dvd
      (Nat.mem_divisors.mp (auxiliary_prime_selection_mem P hP b)).1
    rw [totient_eq_primeFactors_prod _ hn]
    exact auxiliary_prime_selection_product P hP b (fun p => (p : ℝ) - 1)
  have hR (j : Fin 38) :
      ((∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1).totient : ℝ) =
        ∏ p : P, if (σ p).2 = some j then (p : ℝ) - 1 else 1 := by
    simpa only [decide_eq_true_eq] using hphi (fun p => decide ((σ p).2 = some j))
  rw [hphi (fun p => (σ p).1)]
  simp_rw [hR]
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rcases σ p with ⟨b, o⟩
  cases b <;> cases o <;> simp [auxiliaryPrimeState, pow_two]

theorem auxiliary_independent_tensor (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (i : Fin 39)
    (amplitude : (P → Bool × Option (Fin 38)) → ℝ) :
    let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
      fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
      fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    (∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
      amplitude σ * amplitude τ *
        ∏ p : P, auxiliaryIndependentGram (p : ℕ) i (σ p) (τ p)) =
      ∑ σ : P → Bool × Option (Fin 38),
        amplitude σ ^ 2 /
          (((rootA σ 0).totient : ℝ) * ∏ j, ((rootR σ j).totient : ℝ)) := by
  classical
  intro rootA rootR
  let Φ (σ : P → Bool × Option (Fin 38)) : ℝ :=
    ((rootA σ 0).totient : ℝ) * ∏ j, ((rootR σ j).totient : ℝ)
  have hprod (σ τ : P → Bool × Option (Fin 38)) :
      (∏ p : P, auxiliaryIndependentGram (p : ℕ) i (σ p) (τ p)) =
        if σ = τ then 1 / Φ σ else 0 := by
    have hlocal (p : P) := auxiliaryIndependentGram_eq (p : ℕ) i (σ p) (τ p)
      (hP p.val p.property) (auxiliaryPrimeState_injective i)
    simp only [hlocal, Fintype.prod_ite_zero, ← funext_iff]
    congr 1
    rw [show Φ σ = ∏ p : P, ((p : ℝ) - 1) ^ (auxiliaryPrimeState i (σ p)).card from
      auxiliary_root_totient P hP i σ]
    simp only [one_div, Finset.prod_inv_distrib]
  simp_rw [hprod, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Φ, pow_two, div_eq_mul_inv, one_mul]

theorem auxiliary_independent_harmonic (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (i : Fin 39)
    (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ)
    (hu : ∀ s ∈ u.support, s 0 ∈ (∏ p ∈ P, p).divisors)
    (hz : ∀ r ∈ z.support, Squarefree (∏ j, r j) ∧
      ∀ j, r j ∈ (∏ p ∈ P, p).divisors) :
    let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
      fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
      fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    (∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
      (u (rootA σ) * z (rootR σ)) * (u (rootA τ) * z (rootR τ)) *
        ∏ p : P, auxiliaryIndependentGram (p : ℕ) i (σ p) (τ p)) =
      u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) *
        z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ))) := by
  classical
  intro rootA rootR
  let q : ℕ := ∏ p ∈ P, p
  let SA := Fintype.piFinset (fun _ : Fin 1 => q.divisors)
  let SR := (Fintype.piFinset (fun _ : Fin 38 => q.divisors)).filter
    (fun r => Squarefree (∏ j, r j))
  have hSA : u.support ⊆ SA := by
    intro s hs
    simpa only [SA, Fintype.mem_piFinset, Fin.forall_fin_one] using hu s hs
  have hSR : z.support ⊆ SR := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (hz r hr).2, (hz r hr).1⟩
  have huSum :
      (∑ s ∈ SA, u s ^ 2 / ((s 0).totient : ℝ)) =
        u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) :=
    (Finsupp.sum_of_support_subset u hSA
      (fun s us => us ^ 2 / ((s 0).totient : ℝ)) (fun _ _ => by simp)).symm
  have hzSum :
      (∑ r ∈ SR, z r ^ 2 / (∏ j, ((r j).totient : ℝ))) =
        z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ))) :=
    (Finsupp.sum_of_support_subset z hSR
      (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ))) (fun _ _ => by simp)).symm
  rw [auxiliary_independent_tensor P hP i]
  calc
    _ = ∑ s ∈ SA, ∑ r ∈ SR,
        (u s * z r) ^ 2 /
          (((s 0).totient : ℝ) * ∏ j, ((r j).totient : ℝ)) :=
      auxiliary_root_sum P hP (fun s r =>
        (u s * z r) ^ 2 / (((s 0).totient : ℝ) * ∏ j, ((r j).totient : ℝ)))
    _ = (∑ s ∈ SA, u s ^ 2 / ((s 0).totient : ℝ)) *
        (∑ r ∈ SR, z r ^ 2 / (∏ j, ((r j).totient : ℝ))) := by
      simp only [mul_pow, div_mul_div_comm, Finset.sum_mul_sum]
    _ = _ := by rw [huSum, hzSum]

theorem sum_range_eq_sum_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℝ) :
    (∑ n ∈ Finset.range q, f (n : ZMod q)) = ∑ n : ZMod q, f n := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    change (∑ n : ZMod (q + 1), f (n.val : ZMod (q + 1))) = _
    simp only [ZMod.natCast_zmod_val]

theorem prime_product_average (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (f : ∀ p : P, ZMod (p : ℕ) → ℝ) :
    let q : ℕ := ∏ p ∈ P, p
    (1 / (q : ℝ)) * ∑ n ∈ Finset.range q, ∏ p : P, f p (n : ZMod (p : ℕ)) =
      ∏ p : P, (1 / ((p : ℕ) : ℝ)) *
        ∑ n ∈ Finset.range (p : ℕ), f p (n : ZMod (p : ℕ)) := by
  classical
  dsimp only
  let q : ℕ := ∏ p : P, (p : ℕ)
  have hq_eq : q = ∏ p ∈ P, p := by
    dsimp only [q]
    exact Finset.prod_coe_sort P (fun p : ℕ => p)
  rw [← hq_eq]
  have hp_pos (p : P) : 0 < (p : ℕ) := (hP p p.property).pos
  have hq : 0 < q := by
    dsimp only [q]
    exact Finset.prod_pos (fun p _ => hp_pos p)
  let : NeZero q := ⟨ne_of_gt hq⟩
  let : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨ne_of_gt (hp_pos p)⟩
  have hc : Pairwise (fun p r : P => Nat.Coprime (p : ℕ) (r : ℕ)) := by
    intro p r hpr
    apply (Nat.coprime_primes (hP p p.property) (hP r r.property)).mpr
    exact fun h => hpr (Subtype.ext h)
  let E : ZMod q ≃+* (∀ p : P, ZMod (p : ℕ)) :=
    ZMod.prodEquivPi (fun p : P => (p : ℕ)) hc
  have hE (n : ℕ) (p : P) : E (n : ZMod q) p = (n : ZMod (p : ℕ)) := by
    dsimp only [E]
    rw [ZMod.prodEquivPi_apply]
    exact map_natCast _ n
  have hsum : (∑ n ∈ Finset.range q, ∏ p : P, f p (n : ZMod (p : ℕ))) =
      ∏ p : P, ∑ n : ZMod (p : ℕ), f p n := by
    calc
      _ = ∑ n ∈ Finset.range q, ∏ p : P, f p (E (n : ZMod q) p) := by
        simp only [hE]
      _ = ∑ n : ZMod q, ∏ p : P, f p (E n p) :=
        sum_range_eq_sum_zmod q (fun n : ZMod q => ∏ p : P, f p (E n p))
      _ = ∑ n : ∀ p : P, ZMod (p : ℕ), ∏ p : P, f p (n p) :=
        E.toEquiv.sum_comp (fun n : ∀ p : P, ZMod (p : ℕ) => ∏ p : P, f p (n p))
      _ = ∏ p : P, ∑ n : ZMod (p : ℕ), f p n := (Fintype.prod_sum f).symm
  rw [hsum]
  simp_rw [sum_range_eq_sum_zmod]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [q, one_div, Finset.prod_inv_distrib, Nat.cast_prod]

theorem auxiliary_categorical_product_average (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (h : Fin 39 → ℕ) (i : Fin 39)
    (σ τ : P → Bool × Option (Fin 38)) :
    let q : ℕ := ∏ p ∈ P, p
    (1 / (q : ℝ)) * ∑ n ∈ Finset.range q, ∏ p : P,
      (∏ j ∈ auxiliaryPrimeState i (σ p), selbergPrimePsi (p : ℕ) h j n) *
        (∏ j ∈ auxiliaryPrimeState i (τ p), selbergPrimePsi (p : ℕ) h j n) =
      ∏ p : P, auxiliaryCategoricalGram (p : ℕ) h i (σ p) (τ p) := by
  classical
  let f : ∀ p : P, ZMod (p : ℕ) → ℝ := fun p t =>
    (∏ j ∈ auxiliaryPrimeState i (σ p), selbergPrimePsi (p : ℕ) h j t.val) *
      (∏ j ∈ auxiliaryPrimeState i (τ p), selbergPrimePsi (p : ℕ) h j t.val)
  have hpsi (p : P) (n : ℕ) (j : Fin 39) :
      selbergPrimePsi (p : ℕ) h j (n : ZMod (p : ℕ)).val =
        selbergPrimePsi (p : ℕ) h j n := by
    simp only [selbergPrimePsi, ZMod.val_natCast, Nat.dvd_iff_mod_eq_zero,
      Nat.add_mod, Nat.mod_mod]
  simpa only [f, hpsi, auxiliaryCategoricalGram] using prime_product_average P hP f

theorem auxiliary_affine_bijective (q W : ℕ)
    (hcop : Nat.Coprime q W) (b : ℕ) :
    Function.Bijective (fun t : ZMod q => (b : ZMod q) + (W : ZMod q) * t) :=
  ((ZMod.unitOfCoprime W hcop.symm).mulLeft.trans
    (Equiv.addLeft (b : ZMod q))).bijective

theorem auxiliary_affine_period_average (q W : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime q W) (V : ℕ → ℝ) (hV : Function.Periodic V q) (b : ℕ) :
    (1 / (q : ℝ)) * ∑ n ∈ Finset.range q, (V (b + W * n)) ^ 2 =
      (1 / (q : ℝ)) * ∑ n ∈ Finset.range q, (V n) ^ 2 := by
  classical
  let : NeZero q := ⟨ne_of_gt hq⟩
  have hs := (auxiliary_affine_bijective q W hcop b).sum_comp
    (fun t : ZMod q => (V t.val) ^ 2)
  rw [← sum_range_eq_sum_zmod q, ← sum_range_eq_sum_zmod q] at hs
  apply congrArg (fun s : ℝ => (1 / (q : ℝ)) * s)
  simpa only [← Nat.cast_add, ← Nat.cast_mul, ZMod.val_natCast,
    hV.map_mod_nat] using hs

theorem auxiliaryPrimeState_prod {M : Type*} [CommMonoid M]
    (i : Fin 39) (b : Bool) (o : Option (Fin 38)) (f : Fin 39 → M) :
    (if b then f i else 1) *
        (∏ j : Fin 38, if o = some j then f (i.succAbove j) else 1) =
      ∏ j ∈ auxiliaryPrimeState i (b, o), f j := by
  classical
  cases b <;> cases o <;> simp [auxiliaryPrimeState, Finset.prod_ite_eq]

open Classical in
theorem auxiliary_pointwise_expansion
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h : Fin 39 → ℕ) (i : Fin 39)
    (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ)
    (hu : ∀ s ∈ u.support, s 0 ∈ (∏ p ∈ P, p).divisors)
    (hz : ∀ r ∈ z.support,
      Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ (∏ p ∈ P, p).divisors) :
    let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
      fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
      fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    let Du := u.support.biUnion
      (fun s => Fintype.piFinset (fun j => (s j).divisors))
    let Dz := z.support.biUnion
      (fun r => Fintype.piFinset (fun j => (r j).divisors))
    let L : ℕ → ℝ := fun t =>
      ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
    let C : ℕ → ℝ := fun n =>
      ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
        selbergCoefficient z d else 0
    let V : ℕ → ℝ := fun n => L (n + h i) * C n
    let amplitude : (P → Bool × Option (Fin 38)) → ℝ :=
      fun σ => u (rootA σ) * z (rootR σ)
    ∀ n : ℕ,
      V n = ∑ σ : P → Bool × Option (Fin 38),
        amplitude σ * ∏ p : P, ∏ j ∈ auxiliaryPrimeState i (σ p),
          selbergPrimePsi (p : ℕ) h j n := by
  intro rootA rootR Du Dz L C V amplitude n
  let q : ℕ := ∏ p ∈ P, p
  let SA := Fintype.piFinset (fun _ : Fin 1 => q.divisors)
  let SR := (Fintype.piFinset (fun _ : Fin 38 => q.divisors)).filter
    (fun r => Squarefree (∏ j, r j))
  let FA (s : Fin 1 → ℕ) : ℝ :=
    u s * ∏ p ∈ (s 0).primeFactors, selbergPrimePsi p h i n
  let FR (r : Fin 38 → ℕ) : ℝ :=
    z r * ∏ j, ∏ p ∈ (r j).primeFactors, selbergPrimePsi p h (i.succAbove j) n
  have huSq : ∀ s ∈ u.support, Squarefree (∏ j, s j) := by
    intro s hs
    simpa only [Fin.prod_univ_one] using
      (squarefree_prime_prod P hP).squarefree_of_dvd
        (Nat.mem_divisors.mp (hu s hs)).1
  have hL : L (n + h i) = ∑ s ∈ u.support, FA s := by
    simpa only [L, Du, FA, Fin.forall_fin_one, Fin.prod_univ_one, selbergPrimePsi] using
      selberg_pointwise_expansion u (fun _ => n + h i) huSq
  have hC : C n = ∑ r ∈ z.support, FR r := by
    have he := selberg_pointwise_expansion z (fun j => n + h (i.succAbove j))
      (fun r hr => (hz r hr).1)
    refine Eq.trans ?_ he
    apply Finset.sum_congr rfl
    intro d _
    by_cases hdt : ∀ j : Fin 38, d j ∣ n + h (i.succAbove j) <;> simp [hdt]
  have huSA : u.support ⊆ SA := by
    intro s hs
    simpa only [SA, Fintype.mem_piFinset, Fin.forall_fin_one] using hu s hs
  have hzSR : z.support ⊆ SR := by
    intro r hr
    exact Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (hz r hr).2, (hz r hr).1⟩
  have hsumA : (∑ s ∈ u.support, FA s) = ∑ s ∈ SA, FA s := by
    apply Finset.sum_subset huSA
    intro s _ hs
    simp only [FA, Finsupp.notMem_support_iff.mp hs, zero_mul]
  have hsumR : (∑ r ∈ z.support, FR r) = ∑ r ∈ SR, FR r := by
    apply Finset.sum_subset hzSR
    intro r _ hr
    simp only [FR, Finsupp.notMem_support_iff.mp hr, zero_mul]
  have hAprod (σ : P → Bool × Option (Fin 38)) :
      (∏ p ∈ (rootA σ 0).primeFactors, selbergPrimePsi p h i n) =
        ∏ p : P, if (σ p).1 then selbergPrimePsi (p : ℕ) h i n else 1 :=
    auxiliary_prime_selection_product P hP (fun p => (σ p).1)
      (fun p => selbergPrimePsi p h i n)
  have hRprod (σ : P → Bool × Option (Fin 38)) :
      (∏ j : Fin 38, ∏ p ∈ (rootR σ j).primeFactors,
        selbergPrimePsi p h (i.succAbove j) n) =
        ∏ p : P, ∏ j : Fin 38,
          if (σ p).2 = some j then selbergPrimePsi (p : ℕ) h (i.succAbove j) n
          else 1 := by
    calc
      _ = ∏ j : Fin 38, ∏ p : P,
          if (σ p).2 = some j then selbergPrimePsi (p : ℕ) h (i.succAbove j) n
          else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        simpa only [decide_eq_true_eq] using
          auxiliary_prime_selection_product P hP
            (fun p => decide ((σ p).2 = some j))
            (fun p => selbergPrimePsi p h (i.succAbove j) n)
      _ = _ := Finset.prod_comm
  have hconfigured (σ : P → Bool × Option (Fin 38)) :
      FA (rootA σ) * FR (rootR σ) =
        amplitude σ * ∏ p : P, ∏ j ∈ auxiliaryPrimeState i (σ p),
          selbergPrimePsi (p : ℕ) h j n := by
    dsimp only [FA, FR, amplitude]
    rw [hAprod, hRprod]
    calc
      _ = (u (rootA σ) * z (rootR σ)) * ∏ p : P,
          (if (σ p).1 then selbergPrimePsi (p : ℕ) h i n else 1) *
            (∏ j : Fin 38, if (σ p).2 = some j then
              selbergPrimePsi (p : ℕ) h (i.succAbove j) n else 1) := by
        rw [Finset.prod_mul_distrib]
        ring
      _ = _ := by
        congr 1
        apply Finset.prod_congr rfl
        intro p _
        exact auxiliaryPrimeState_prod i (σ p).1 (σ p).2
          (fun j => selbergPrimePsi (p : ℕ) h j n)
  calc
    V n = (∑ s ∈ u.support, FA s) * (∑ r ∈ z.support, FR r) := by
      change L (n + h i) * C n = _
      rw [hL, hC]
    _ = (∑ s ∈ SA, FA s) * (∑ r ∈ SR, FR r) := by rw [hsumA, hsumR]
    _ = ∑ s ∈ SA, ∑ r ∈ SR, FA s * FR r := by rw [Finset.sum_mul_sum]
    _ = ∑ σ : P → Bool × Option (Fin 38), FA (rootA σ) * FR (rootR σ) :=
      (auxiliary_root_sum P hP (fun s r => FA s * FR r)).symm
    _ = _ := Finset.sum_congr rfl fun σ _ => hconfigured σ

theorem selberg_sum_periodic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (y : (ι → ℕ) →₀ ℝ) (h : ι → ℕ)
    (hy : ∀ r ∈ y.support, ∀ j, r j ∣ q) :
    let D := y.support.biUnion
      (fun r => Fintype.piFinset (fun j => (r j).divisors))
    Function.Periodic
      (fun n => ∑ d ∈ D, if ∀ j, d j ∣ n + h j then selbergCoefficient y d else 0) q := by
  classical
  intro D n
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
  have hdq (j : ι) : d j ∣ q :=
    (Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr j)).trans (hy r hr j)
  have hiff : (∀ j, d j ∣ n + q + h j) ↔ (∀ j, d j ∣ n + h j) := by
    exact forall_congr' fun j => by
      rw [Nat.add_right_comm]
      exact (Nat.dvd_add_iff_left (hdq j)).symm
  simp only [hiff]

theorem auxiliary_categorical_tensor (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (h : Fin 39 → ℕ) (i : Fin 39)
    (amplitude : (P → Bool × Option (Fin 38)) → ℝ) (V : ℕ → ℝ)
    (hexp : ∀ n, V n = ∑ σ : P → Bool × Option (Fin 38),
      amplitude σ * ∏ p : P, ∏ j ∈ auxiliaryPrimeState i (σ p),
        selbergPrimePsi (p : ℕ) h j n) :
    let q : ℕ := ∏ p ∈ P, p
    (1 / (q : ℝ)) * ∑ n ∈ Finset.range q, V n ^ 2 =
      ∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        amplitude σ * amplitude τ *
          ∏ p : P, auxiliaryCategoricalGram (p : ℕ) h i (σ p) (τ p) := by
  classical
  intro q
  have hpoint (n : ℕ) :
      V n ^ 2 = ∑ σ : P → Bool × Option (Fin 38),
        ∑ τ : P → Bool × Option (Fin 38), amplitude σ * amplitude τ *
          ∏ p : P,
            (∏ j ∈ auxiliaryPrimeState i (σ p), selbergPrimePsi (p : ℕ) h j n) *
              (∏ j ∈ auxiliaryPrimeState i (τ p), selbergPrimePsi (p : ℕ) h j n) := by
    simp only [hexp n, pow_two, Finset.sum_mul_sum, Finset.prod_mul_distrib,
      mul_assoc, mul_left_comm]
  simp_rw [hpoint]
  calc
    _ = ∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        amplitude σ * amplitude τ * ((1 / (q : ℝ)) *
          ∑ n ∈ Finset.range q, ∏ p : P,
            (∏ j ∈ auxiliaryPrimeState i (σ p), selbergPrimePsi (p : ℕ) h j n) *
              (∏ j ∈ auxiliaryPrimeState i (τ p), selbergPrimePsi (p : ℕ) h j n)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      simp only [q, auxiliary_categorical_product_average P hP h i]

open Classical in
theorem selberg39_auxiliary_exact_period_bridge
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (x κ : ℝ) (hx : 1 < x) (hκ : 0 < κ) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W := presievingModulus 𝓗 x
    let R := x ^ ρ
    let P := fragmentPrimes W R κ
    let q : ℕ := ∏ p ∈ P, p
    let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
      fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
    let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
      fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
    ∀ (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ),
      (∀ s ∈ u.support, s 0 ∈ q.divisors) →
      (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
      let Du := u.support.biUnion
        (fun s => Fintype.piFinset (fun j => (s j).divisors))
      let Dz := z.support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
      let L : ℕ → ℝ := fun t =>
        ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
      let C : ℕ → ℝ := fun n =>
        ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
          selbergCoefficient z d else 0
      let V : ℕ → ℝ := fun n => L (n + h i) * C n
      let amplitude : (P → Bool × Option (Fin 38)) → ℝ :=
        fun σ => u (rootA σ) * z (rootR σ)
      let mean : ℝ := (1 / (q : ℝ)) * ∑ n ∈ Finset.range q, V n ^ 2
      let tensorK : ℝ := ∑ σ : P → Bool × Option (Fin 38),
        ∑ τ : P → Bool × Option (Fin 38),
          amplitude σ * amplitude τ *
            ∏ p : P, auxiliaryCategoricalGram (p : ℕ) h i (σ p) (τ p)
      let tensorD : ℝ := ∑ σ : P → Bool × Option (Fin 38),
        ∑ τ : P → Bool × Option (Fin 38),
          amplitude σ * amplitude τ *
            ∏ p : P, auxiliaryIndependentGram (p : ℕ) i (σ p) (τ p)
      let harmonic : ℝ :=
        u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) *
          z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))
      0 < q ∧ Nat.Coprime q W ∧
        (∀ (s : Fin 1 → ℕ) (r : Fin 38 → ℕ),
          (s 0 ∈ q.divisors ∧ Squarefree (∏ j, r j) ∧
            ∀ j, r j ∈ q.divisors) ↔
          ∃! σ : P → Bool × Option (Fin 38), rootA σ = s ∧ rootR σ = r) ∧
        (∀ n : ℕ,
          V n = ∑ σ : P → Bool × Option (Fin 38),
            amplitude σ * ∏ p : P, ∏ j ∈ auxiliaryPrimeState i (σ p),
              selbergPrimePsi (p : ℕ) h j n) ∧
        mean = tensorK ∧ tensorD = harmonic ∧
        (∀ n : ℕ, L (n + q) = L n) ∧
        (∀ n : ℕ, C (n + q) = C n) ∧
        (∀ b : ℕ,
          Function.Bijective (fun t : ZMod q => (b : ZMod q) + (W : ZMod q) * t)) ∧
        (∀ b : ℕ,
          (1 / (q : ℝ)) * (∑ n ∈ Finset.range q, V (b + W * n) ^ 2) = mean) := by
  refine (fun (_ : 1 < x) (_ : 0 < κ) => ?_) hx hκ
  classical
  intro ρ h W R P q rootA rootR u z hu hz Du Dz L C V amplitude mean tensorK tensorD harmonic
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hpW (p : ℕ) (hp : p ∈ P) : ¬ p ∣ W := (Finset.mem_filter.mp hp).2
  have hq : 0 < q := Finset.prod_pos fun p hp => (hP p hp).pos
  have hcop : Nat.Coprime q W :=
    Nat.Coprime.prod_left fun p hp => (hP p hp).coprime_iff_not_dvd.mpr (hpW p hp)
  have hexp : ∀ n : ℕ,
      V n = ∑ σ : P → Bool × Option (Fin 38),
        amplitude σ * ∏ p : P, ∏ j ∈ auxiliaryPrimeState i (σ p),
          selbergPrimePsi (p : ℕ) h j n :=
    auxiliary_pointwise_expansion P hP h i u z hu hz
  have huq : ∀ s ∈ u.support, ∀ j : Fin 1, s j ∣ q := by
    intro s hs j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj] using (Nat.mem_divisors.mp (hu s hs)).1
  have hzq : ∀ r ∈ z.support, ∀ j : Fin 38, r j ∣ q :=
    fun r hr j => (Nat.mem_divisors.mp ((hz r hr).2 j)).1
  have hL : Function.Periodic L q := by
    simpa only [L, Du, Nat.add_zero, Fin.forall_fin_one] using
      selberg_sum_periodic q u (fun _ : Fin 1 => 0) huq
  have hC : Function.Periodic C q := by
    have hperiod := selberg_sum_periodic q z (fun j => h (i.succAbove j)) hzq
    intro n
    refine Eq.trans ?_ (Eq.trans (hperiod n) ?_)
    · apply Finset.sum_congr rfl
      intro d _
      by_cases hdt : ∀ j : Fin 38, d j ∣ n + q + h (i.succAbove j) <;> simp [hdt]
    · apply Finset.sum_congr rfl
      intro d _
      by_cases hdt : ∀ j : Fin 38, d j ∣ n + h (i.succAbove j) <;> simp [hdt]
  have hV : Function.Periodic V q := (hL.add_const (h i)).mul hC
  refine ⟨hq, hcop, auxiliary_root_configuration P hP, hexp, ?_, ?_, hL, hC, ?_, ?_⟩
  · exact auxiliary_categorical_tensor P hP h i amplitude V hexp
  · exact auxiliary_independent_harmonic P hP i u z hu hz
  · intro b
    exact auxiliary_affine_bijective q W hcop b
  · intro b
    exact auxiliary_affine_period_average q W hq hcop V hV b

end

section
open Real Finset Filter Asymptotics Topology

open ArithmeticFunction hiding log

theorem auxiliary_abs_prod_sub_prod_le {ι : Type*} (S : Finset ι)
    (k d : ι → ℝ) (hd : ∀ p ∈ S, 0 ≤ d p) :
    |(∏ p ∈ S, k p) - ∏ p ∈ S, d p| ≤
      (∏ p ∈ S, (d p + |k p - d p|)) - ∏ p ∈ S, d p := by
  classical
  revert hd
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
      intro hd
      have hda : 0 ≤ d a := hd a (Finset.mem_insert_self a S)
      have hdS : ∀ p ∈ S, 0 ≤ d p :=
        fun p hp => hd p (Finset.mem_insert_of_mem hp)
      have hk : |∏ p ∈ S, k p| ≤ ∏ p ∈ S, (d p + |k p - d p|) := by
        rw [Finset.abs_prod]
        refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
        intro p hp
        calc
          |k p| = |k p - d p + d p| := by rw [sub_add_cancel]
          _ ≤ |k p - d p| + |d p| := abs_add_le _ _
          _ = d p + |k p - d p| := by rw [abs_of_nonneg (hdS p hp), add_comm]
      simp only [Finset.prod_insert ha]
      calc
        |k a * (∏ p ∈ S, k p) - d a * ∏ p ∈ S, d p| =
            |(k a - d a) * (∏ p ∈ S, k p) +
              d a * ((∏ p ∈ S, k p) - ∏ p ∈ S, d p)| := by
          congr 1
          ring
        _ ≤ |(k a - d a) * (∏ p ∈ S, k p)| +
            |d a * ((∏ p ∈ S, k p) - ∏ p ∈ S, d p)| := abs_add_le _ _
        _ = |k a - d a| * |∏ p ∈ S, k p| +
            d a * |(∏ p ∈ S, k p) - ∏ p ∈ S, d p| := by
          simp only [abs_mul, abs_of_nonneg hda]
        _ ≤ |k a - d a| * (∏ p ∈ S, (d p + |k p - d p|)) +
            d a * ((∏ p ∈ S, (d p + |k p - d p|)) - ∏ p ∈ S, d p) :=
          add_le_add (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (ih hdS) hda)
        _ = (d a + |k a - d a|) * (∏ p ∈ S, (d p + |k p - d p|)) -
            d a * ∏ p ∈ S, d p := by ring

theorem auxiliary_tensor_perturbation {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (K D : ι → α → α → ℝ) (e : ι → ℝ)
    (hD : ∀ p s t, 0 ≤ D p s t) (he : ∀ p, 0 ≤ e p)
    (hd : ∀ p, 1 ≤ ∑ s : α, ∑ t : α, D p s t)
    (hδ : ∀ p, (∑ s : α, ∑ t : α, |K p s t - D p s t|) ≤ e p) :
    (∑ σ : ι → α, ∑ τ : ι → α,
      |(∏ p, K p (σ p) (τ p)) - ∏ p, D p (σ p) (τ p)|) ≤
      (∏ p, ∑ s : α, ∑ t : α, D p s t) * (Real.exp (∑ p, e p) - 1) := by
  classical
  let d : ι → ℝ := fun p => ∑ s : α, ∑ t : α, D p s t
  let δ : ι → ℝ := fun p => ∑ s : α, ∑ t : α, |K p s t - D p s t|
  have hd₀ (p : ι) : 0 ≤ d p := zero_le_one.trans (hd p)
  have hδ₀ (p : ι) : 0 ≤ δ p :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum (F : ι → α → α → ℝ) :
      (∑ σ : ι → α, ∑ τ : ι → α, ∏ p, F p (σ p) (τ p)) =
        ∏ p, ∑ s : α, ∑ t : α, F p s t := by
    simpa only [← Fintype.prod_sum] using
      (Fintype.prod_sum (fun p s => ∑ t : α, F p s t)).symm
  have hde (p : ι) : d p + δ p ≤ d p * (1 + e p) := by
    calc
      d p + δ p ≤ d p + e p := add_le_add le_rfl (hδ p)
      _ ≤ d p + d p * e p := by
        apply add_le_add le_rfl
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hd p) (he p)
      _ = d p * (1 + e p) := by ring
  calc
    _ ≤ ∑ σ : ι → α, ∑ τ : ι → α,
        ((∏ p, (D p (σ p) (τ p) + |K p (σ p) (τ p) - D p (σ p) (τ p)|)) -
          ∏ p, D p (σ p) (τ p)) := by
      refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => ?_
      exact auxiliary_abs_prod_sub_prod_le Finset.univ
        (fun p => K p (σ p) (τ p)) (fun p => D p (σ p) (τ p))
        (fun p _ => hD p (σ p) (τ p))
    _ = (∏ p, (d p + δ p)) - ∏ p, d p := by
      simp_rw [Finset.sum_sub_distrib]
      rw [hsum (fun p s t => D p s t + |K p s t - D p s t|), hsum D]
      congr 1
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [d, δ, Finset.sum_add_distrib]
    _ ≤ (∏ p, d p * (1 + e p)) - ∏ p, d p :=
      sub_le_sub_right
        (Finset.prod_le_prod (fun p _ => add_nonneg (hd₀ p) (hδ₀ p))
          (fun p _ => hde p)) _
    _ = (∏ p, d p) * ((∏ p, (1 + e p)) - 1) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ ≤ (∏ p, d p) * (Real.exp (∑ p, e p) - 1) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_right (Real.prod_one_add_le_exp_sum Finset.univ he) 1)
        (Finset.prod_nonneg fun p _ => hd₀ p)

theorem auxiliary_weighted_tensor_error
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (x : ℝ) (i : Fin 39) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hpW : ∀ p ∈ P, ¬ p ∣ presievingModulus 𝓗 x)
    (a : (P → Bool × Option (Fin 38)) → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (ha : ∀ σ, |a σ| ≤ A) :
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    |(∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        a σ * a τ * ∏ p : P, auxiliaryCategoricalGram (p : ℕ) h i (σ p) (τ p)) -
      (∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        a σ * a τ * ∏ p : P, auxiliaryIndependentGram (p : ℕ) i (σ p) (τ p))| ≤
      A ^ 2 * (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) ^ 39 *
        (Real.exp (48672 * (∑' p : ℕ,
          if p.Prime ∧ ¬ p ∣ presievingModulus 𝓗 x
          then 1 / (p : ℝ) ^ 2 else 0)) - 1) := by
  classical
  dsimp only
  let h : Fin 39 → ℕ :=
    𝓗.orderEmbOfFin h𝓗_card
  let K : P → (Bool × Option (Fin 38)) → (Bool × Option (Fin 38)) → ℝ :=
    fun p s t => auxiliaryCategoricalGram (p : ℕ) h i s t
  let D : P → (Bool × Option (Fin 38)) → (Bool × Option (Fin 38)) → ℝ :=
    fun p s t => auxiliaryIndependentGram (p : ℕ) i s t
  let e : P → ℝ := fun p => 48672 / ((p : ℕ) : ℝ) ^ 2
  have hlocal (p : P) :
      (∀ s t, 0 ≤ D p s t) ∧
      (∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38),
        |K p s t - D p s t|) ≤ e p ∧
      1 ≤ (∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38), D p s t) ∧
      (∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38), D p s t) ≤
        (1 + 1 / (((p : ℕ) : ℝ) - 1)) ^ 39 := by
    have hm := selberg39_auxiliary_local_gram
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) x i p (hP p p.property) (hpW p p.property)
    dsimp only at hm
    refine ⟨?_, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2⟩
    intro s t
    change 0 ≤ auxiliaryIndependentGram (p : ℕ) i s t
    rw [(hm.2.2.2.2.1 s t).2.1]
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hP p p.property).two_le
    have hp1 : 0 < ((p : ℕ) : ℝ) - 1 := by linarith
    split_ifs <;> positivity
  have he (p : P) : 0 ≤ e p := by dsimp only [e]; positivity
  have hT := auxiliary_tensor_perturbation K D e
    (fun p => (hlocal p).1) he
    (fun p => (hlocal p).2.2.1) (fun p => (hlocal p).2.1)
  have hd0 : 0 ≤ ∏ p : P,
      ∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38), D p s t :=
    Finset.prod_nonneg fun p _ => zero_le_one.trans (hlocal p).2.2.1
  have hmass : (∏ p : P,
      ∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38), D p s t) ≤
      (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) ^ 39 := by
    calc
      _ ≤ ∏ p : P, (1 + 1 / (((p : ℕ) : ℝ) - 1)) ^ 39 :=
        Finset.prod_le_prod (fun p _ => zero_le_one.trans (hlocal p).2.2.1)
          (fun p _ => (hlocal p).2.2.2)
      _ = _ := by
        rw [Finset.prod_pow]
        congr 1
        exact Finset.prod_coe_sort P (fun p : ℕ => (1 : ℝ) + 1 / ((p : ℝ) - 1))
  let f : ℕ → ℝ := fun p =>
    if p.Prime ∧ ¬ p ∣ presievingModulus 𝓗 x
    then 1 / (p : ℝ) ^ 2 else 0
  have hf0 (p : ℕ) : 0 ≤ f p := by dsimp only [f]; split_ifs <;> positivity
  have hf : Summable f :=
    Summable.of_nonneg_of_le hf0 (fun p => by
      dsimp only [f]
      split_ifs
      · exact le_rfl
      · positivity) (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have htail : (∑ p : P, e p) ≤ 48672 * ∑' p, f p := by
    calc
      _ = 48672 * ∑ p ∈ P, f p := by
        rw [← Finset.sum_coe_sort P f, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        dsimp only [e, f]
        rw [ite_eq_left ⟨hP p p.property, hpW p p.property⟩]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hf.sum_le_tsum P fun p _ => hf0 p) (by norm_num)
  have hexp : Real.exp (∑ p : P, e p) - 1 ≤
      Real.exp (48672 * ∑' p, f p) - 1 :=
    sub_le_sub_right (Real.exp_le_exp.mpr htail) 1
  have hexp0 : 0 ≤ Real.exp (∑ p : P, e p) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (Finset.sum_nonneg fun p _ => he p))
  have hweighted :
      |(∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
          a σ * a τ * ∏ p : P, K p (σ p) (τ p)) -
        (∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
          a σ * a τ * ∏ p : P, D p (σ p) (τ p))| ≤
        A ^ 2 * (∑ σ : P → Bool × Option (Fin 38),
          ∑ τ : P → Bool × Option (Fin 38),
            |(∏ p : P, K p (σ p) (τ p)) - ∏ p : P, D p (σ p) (τ p)|) := by
    calc
      _ = |∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
          a σ * a τ * ((∏ p : P, K p (σ p) (τ p)) -
            ∏ p : P, D p (σ p) (τ p))| := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ σ : P → Bool × Option (Fin 38),
          |∑ τ : P → Bool × Option (Fin 38),
            a σ * a τ * ((∏ p : P, K p (σ p) (τ p)) -
              ∏ p : P, D p (σ p) (τ p))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
          |a σ * a τ * ((∏ p : P, K p (σ p) (τ p)) -
            ∏ p : P, D p (σ p) (τ p))| := by
        apply Finset.sum_le_sum
        intro σ _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
          A ^ 2 * |(∏ p : P, K p (σ p) (τ p)) -
            ∏ p : P, D p (σ p) (τ p)| := by
        apply Finset.sum_le_sum
        intro σ _
        apply Finset.sum_le_sum
        intro τ _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [abs_mul, pow_two]
        exact mul_le_mul (ha σ) (ha τ) (abs_nonneg _) hA
      _ = _ := by simp only [Finset.mul_sum]
  have hmass0 : 0 ≤ (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) ^ 39 :=
    le_trans hd0 hmass
  change
    |(∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        a σ * a τ * ∏ p : P, K p (σ p) (τ p)) -
      (∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        a σ * a τ * ∏ p : P, D p (σ p) (τ p))| ≤
      A ^ 2 * (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) ^ 39 *
        (Real.exp (48672 * ∑' p, f p) - 1)
  calc
    _ ≤ A ^ 2 * (∑ σ : P → Bool × Option (Fin 38),
        ∑ τ : P → Bool × Option (Fin 38),
          |(∏ p : P, K p (σ p) (τ p)) - ∏ p : P, D p (σ p) (τ p)|) :=
      hweighted
    _ ≤ A ^ 2 * ((∏ p : P,
        ∑ s : Bool × Option (Fin 38), ∑ t : Bool × Option (Fin 38), D p s t) *
          (Real.exp (∑ p : P, e p) - 1)) :=
      mul_le_mul_of_nonneg_left hT (sq_nonneg A)
    _ ≤ A ^ 2 * ((∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) ^ 39 *
        (Real.exp (48672 * ∑' p, f p) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      exact mul_le_mul hmass hexp hexp0 hmass0
    _ = _ := by ring

theorem auxiliary_exp_sub_one_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t - 1 ≤ Real.exp 1 * t := by
  have h := Real.abs_exp_sub_one_le (x := t) (by rwa [abs_of_nonneg ht0])
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [abs_of_nonneg ht0] at h
  exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_right htwo ht0))

open Classical in
theorem selberg39_auxiliary_period_comparison
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ M N : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop,
        let ρ : ℝ := 2624989 / 10000000
        let h : Fin 39 → ℕ :=
          𝓗.orderEmbOfFin h𝓗_card
        let W := presievingModulus 𝓗 x
        let R := x ^ ρ
        let B := fragmentNormalization W R
        let P := fragmentPrimes W R κ
        let q : ℕ := ∏ p ∈ P, p
        let mass := harmonicFragmentMass W R κ
        let tail : ℝ := ∑' p : ℕ,
          if Nat.Prime p ∧ ¬ p ∣ W then 1 / (p : ℝ) ^ 2 else 0
        0 < B ∧
          ∀ (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ),
            (∀ s ∈ u.support, s 0 ∈ q.divisors) →
            (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
            (∀ s, |u s| ≤ N / B) →
            (∀ r, |z r| ≤ M / B ^ 38) →
            let Du := u.support.biUnion
              (fun s => Fintype.piFinset (fun j => (s j).divisors))
            let Dz := z.support.biUnion
              (fun r => Fintype.piFinset (fun j => (r j).divisors))
            let L : ℕ → ℝ := fun t =>
              ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
            let C : ℕ → ℝ := fun n =>
              ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
                selbergCoefficient z d else 0
            let harmonic : ℝ :=
              u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) *
                z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))
            ∀ b : ℕ,
              let error : ℝ :=
                |(1 / (q : ℝ)) * (∑ n ∈ Finset.range q,
                  (L (b + W * n + h i) * C (b + W * n)) ^ 2) - harmonic|
              error ≤ M ^ 2 * N ^ 2 / B ^ 78 * mass ^ 39 *
                  (Real.exp (48672 * tail) - 1) ∧
                error ≤ (48672 * Real.exp 1) *
                    (M ^ 2 * N ^ 2 / B ^ 78 * mass ^ 39) * tail ∧
                error ≤ ε / B ^ 39 := by
  intro ε hε
  let ρ : ℝ := 2624989 / 10000000
  have hρ : 0 < ρ := by norm_num [ρ]
  have hm := harmonic_fragment_normalizer_tendsto 𝓗 ρ κ hρ hκ
  have ht := presieved_prime_square_tail_tendsto 𝓗
  have htSmall : Tendsto
      (fun x : ℝ => 48672 * (∑' p : ℕ,
        if Nat.Prime p ∧ ¬ p ∣ presievingModulus 𝓗 x
        then 1 / (p : ℝ) ^ 2 else 0)) atTop (nhds 0) := by
    simpa only [mul_zero] using ht.const_mul (48672 : ℝ)
  have heSmall : Tendsto
      (fun x : ℝ => (48672 * Real.exp 1) * (M ^ 2 * N ^ 2) *
        (harmonicFragmentMass (presievingModulus 𝓗 x) (x ^ ρ) κ /
          fragmentNormalization (presievingModulus 𝓗 x) (x ^ ρ)) ^ 39 *
        (∑' p : ℕ, if Nat.Prime p ∧ ¬ p ∣ presievingModulus 𝓗 x
          then 1 / (p : ℝ) ^ 2 else 0)) atTop (nhds 0) := by
    have h := ((hm.pow 39).mul ht).const_mul
      ((48672 * Real.exp 1) * (M ^ 2 * N ^ 2))
    simpa only [mul_zero, mul_assoc] using h
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    htSmall.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    heSmall.eventually_le_const hε] with x hx htSmall heSmall
  intro ρ' h W R B P q mass tail
  have hW : 0 < W := presieving_pos 𝓗 x
  have hB : 0 < B := by
    apply mul_pos
    · exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
    · exact Real.log_pos (Real.one_lt_rpow hx hρ)
  refine ⟨hB, ?_⟩
  intro u z hu hz huBound hzBound Du Dz L C harmonic b error
  let rootA : (P → Bool × Option (Fin 38)) → (Fin 1 → ℕ) :=
    fun σ _ => ∏ p : P, if (σ p).1 then (p : ℕ) else 1
  let rootR : (P → Bool × Option (Fin 38)) → (Fin 38 → ℕ) :=
    fun σ j => ∏ p : P, if (σ p).2 = some j then (p : ℕ) else 1
  let amplitude : (P → Bool × Option (Fin 38)) → ℝ :=
    fun σ => u (rootA σ) * z (rootR σ)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hpW (p : ℕ) (hp : p ∈ P) : ¬ p ∣ W := (Finset.mem_filter.mp hp).2
  have hA : 0 ≤ M * N / B ^ 39 :=
    div_nonneg (mul_nonneg hM hN) (pow_nonneg hB.le _)
  have hamp (σ : P → Bool × Option (Fin 38)) :
      |amplitude σ| ≤ M * N / B ^ 39 := by
    dsimp only [amplitude]
    rw [abs_mul]
    calc
      _ ≤ (N / B) * (M / B ^ 38) :=
        mul_le_mul (huBound (rootA σ)) (hzBound (rootR σ))
          (abs_nonneg _) (div_nonneg hN hB.le)
      _ = M * N / B ^ 39 := by
        field_simp [ne_of_gt hB]
  have hbridge := selberg39_auxiliary_exact_period_bridge
    (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ u z hu hz
  rcases hbridge with ⟨_, _, _, _, hmean, hdiag, _, _, _, haffine⟩
  have hmean' :
      (1 / (q : ℝ)) * (∑ n ∈ Finset.range q,
        (L (b + W * n + h i) * C (b + W * n)) ^ 2) =
      ∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        amplitude σ * amplitude τ *
          ∏ p : P, auxiliaryCategoricalGram (p : ℕ) h i (σ p) (τ p) :=
    (haffine b).trans hmean
  have hdiag' :
      (∑ σ : P → Bool × Option (Fin 38), ∑ τ : P → Bool × Option (Fin 38),
        amplitude σ * amplitude τ *
          ∏ p : P, auxiliaryIndependentGram (p : ℕ) i (σ p) (τ p)) = harmonic :=
    hdiag
  have hexponential :
      error ≤ M ^ 2 * N ^ 2 / B ^ 78 * mass ^ 39 *
        (Real.exp (48672 * tail) - 1) := by
    have hf := auxiliary_weighted_tensor_error (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) x i P hP hpW amplitude
      (M * N / B ^ 39) hA hamp
    have hpow : (M * N / B ^ 39) ^ 2 = M ^ 2 * N ^ 2 / B ^ 78 := by
      rw [div_pow, mul_pow, ← pow_mul]
    have hmass :
        (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) = mass :=
      (harmonic_fragment_mass_eq_product W R κ).symm
    rw [hpow, hmass] at hf
    change |(1 / (q : ℝ)) * (∑ n ∈ Finset.range q,
      (L (b + W * n + h i) * C (b + W * n)) ^ 2) - harmonic| ≤ _
    rw [hmean', ← hdiag']
    exact hf
  have ht0 : 0 ≤ tail := tsum_nonneg fun p : ℕ =>
    ite_nonneg (one_div_nonneg.mpr (sq_nonneg (p : ℝ))) le_rfl
  have ht1 : 48672 * tail ≤ 1 := htSmall
  have hfactor : 0 ≤ M ^ 2 * N ^ 2 / B ^ 78 * mass ^ 39 := by
    have hmass0 : 0 ≤ mass := by
      change 0 ≤ harmonicFragmentMass W R κ
      unfold harmonicFragmentMass
      positivity
    positivity
  have hlinear :
      error ≤ (48672 * Real.exp 1) *
        (M ^ 2 * N ^ 2 / B ^ 78 * mass ^ 39) * tail := by
    calc
      error ≤ M ^ 2 * N ^ 2 / B ^ 78 * mass ^ 39 *
          (Real.exp 1 * (48672 * tail)) :=
        hexponential.trans (mul_le_mul_of_nonneg_left
          (auxiliary_exp_sub_one_le (48672 * tail)
            (mul_nonneg (by norm_num) ht0) ht1) hfactor)
      _ = _ := by ring
  have heBound :
      (48672 * Real.exp 1) * (M ^ 2 * N ^ 2) * (mass / B) ^ 39 * tail ≤ ε :=
    heSmall
  refine ⟨hexponential, hlinear, ?_⟩
  calc
    error ≤ (48672 * Real.exp 1) *
        (M ^ 2 * N ^ 2 / B ^ 78 * mass ^ 39) * tail := hlinear
    _ = ((48672 * Real.exp 1) * (M ^ 2 * N ^ 2) * (mass / B) ^ 39 * tail) /
        B ^ 39 := by
      field_simp [ne_of_gt hB]
    _ ≤ ε / B ^ 39 := div_le_div_of_nonneg_right heBound (pow_nonneg hB.le _)

open Classical in
theorem selberg_square_period_mean
    {ι : Type*} [Fintype ι] (h : ι → ℕ) (hinj : Function.Injective h)
    (D : Finset (ι → ℕ)) (lam : (ι → ℕ) → ℝ) (W q : ℕ) (hq : 0 < q)
    (hD : ∀ d ∈ D,
      Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W ∧ ∀ i, d i ∣ q)
    (hcover : ∀ a b : ι, h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W) :
    (1 / (q : ℝ)) * (∑ n ∈ Finset.range q,
      (∑ d ∈ D, if ∀ i, d i ∣ n + h i then lam d else 0) ^ 2) =
      ∑ d ∈ D, ∑ e ∈ D,
        if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
          lam d * lam e / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) else 0 := by
  have hcoordW (d : ι → ℕ) (hd : d ∈ D) (i : ι) : Nat.Coprime (d i) W :=
    Nat.coprime_fintype_prod_left_iff.mp (hD d hd).2.1 i
  have hcoord0 (d : ι → ℕ) (hd : d ∈ D) (i : ι) : d i ≠ 0 :=
    ((hD d hd).1.squarefree_of_dvd
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).ne_zero
  have hcross (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ) (n : ℕ)
      (hnd : ∀ i, d i ∣ n + h i) (hne : ∀ i, e i ∣ n + h i) :
      ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) := by
    intro a b hab
    by_contra hc
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpa' := dvd_trans hpa (hnd a)
    have hpb' := dvd_trans hpb (hne b)
    have hdist : p ∣ Nat.dist (h a) (h b) := by
      rw [← Nat.dist_add_add_left n, Nat.dist]
      exact dvd_add (Nat.dvd_sub hpa' hpb') (Nat.dvd_sub hpb' hpa')
    have hpW := hcover a b (fun hh => hab (hinj hh)) p hp hdist
    exact (hp.coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd_left hpa (hcoordW d hd a))) hpW
  have hneg (m t n : ℕ) (hm : 0 < m) :
      Nat.ModEq m n (m - t % m) ↔ m ∣ n + t := by
    have hres : Nat.ModEq m (m - t % m + t) 0 := by
      have ht := (Nat.mod_modEq t m).add_left (m - t % m)
      rw [Nat.sub_add_cancel (Nat.mod_lt t hm).le] at ht
      exact ht.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl m))
    constructor
    · intro hn
      exact Nat.modEq_zero_iff_dvd.mp ((hn.add_right t).trans hres)
    · intro hn
      exact Nat.ModEq.add_right_cancel' t
        ((Nat.modEq_zero_iff_dvd.mpr hn).trans hres.symm)
  have hcrt (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ) (he : e ∈ D)
      (hc : ∀ i j : ι, i ≠ j → Nat.Coprime (d i) (e j)) :
      (∏ i, Nat.lcm (d i) (e i)) ∣ q ∧
        ∃ c : ℕ, ∀ n : ℕ,
          Nat.ModEq (∏ i, Nat.lcm (d i) (e i)) n c ↔
            (∀ i, d i ∣ n + h i) ∧ (∀ i, e i ∣ n + h i) := by
    let m : ι → ℕ := fun i => Nat.lcm (d i) (e i)
    let a : ι → ℕ := fun i => m i - h i % m i
    let l := (Finset.univ : Finset ι).toList
    have hpos (i : ι) : 0 < m i :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hcoord0 d hd i) (hcoord0 e he i))
    have hss (i j : ι) (hij : i ≠ j) : Nat.Coprime (m i) (m j) := by
      have h₁ : Nat.Coprime (d i) (d j * e j) :=
        (coprime_of_squarefree_fintype_prod d (hD d hd).1 hij).mul_right (hc i j hij)
      have h₂ : Nat.Coprime (e i) (d j * e j) :=
        ((hc j i hij.symm).symm).mul_right
          (coprime_of_squarefree_fintype_prod e (hD e he).1 hij)
      exact Nat.Coprime.of_dvd (Nat.lcm_dvd_mul _ _) (Nat.lcm_dvd_mul _ _)
        (h₁.mul_left h₂)
    have hmq : (∏ i, m i) ∣ q :=
      Fintype.prod_dvd_of_isRelPrime
        (fun i j hij => Nat.coprime_iff_isRelPrime.mp (hss i j hij))
        (fun i => Nat.lcm_dvd ((hD d hd).2.2 i) ((hD e he).2.2 i))
    have co : l.Pairwise (fun i j => Nat.Coprime (m i) (m j)) := by
      refine ((Finset.univ : Finset ι).nodup_toList).pairwise_of_forall_ne ?_
      intro i _ j _ hij
      exact hss i j hij
    let c : ℕ := Nat.chineseRemainderOfList a m l co
    have hprod : (l.map m).prod = ∏ i, Nat.lcm (d i) (e i) :=
      Finset.prod_map_toList Finset.univ m
    have hclass (n : ℕ) :
        Nat.ModEq (∏ i, Nat.lcm (d i) (e i)) n c ↔
          ∀ i, Nat.ModEq (m i) n (a i) := by
      rw [← hprod]
      change Nat.ModEq (l.map m).prod n
        (Nat.chineseRemainderOfList a m l co : ℕ) ↔ _
      constructor
      · intro hn i
        have hi : i ∈ l := by simp [l]
        exact ((Nat.modEq_list_map_prod_iff co).mp hn i hi).trans
          ((Nat.chineseRemainderOfList a m l co).property i hi)
      · intro hn
        exact Nat.chineseRemainderOfList_modEq_unique a m l co (fun i _ => hn i)
    refine ⟨hmq, c, ?_⟩
    intro n
    rw [hclass]
    constructor
    · intro hn
      constructor
      · intro i
        exact (Nat.lcm_dvd_iff.mp ((hneg _ _ _ (hpos i)).mp (hn i))).1
      · intro i
        exact (Nat.lcm_dvd_iff.mp ((hneg _ _ _ (hpos i)).mp (hn i))).2
    · rintro ⟨hdn, hen⟩ i
      exact (hneg _ _ _ (hpos i)).mpr (Nat.lcm_dvd (hdn i) (hen i))
  let C (d e : ι → ℕ) :=
    {n ∈ Finset.range q | (∀ i, d i ∣ n + h i) ∧ (∀ i, e i ∣ n + h i)}.card
  have hcount (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ) (he : e ∈ D)
      (hc : ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) :
      (C d e : ℝ) = (q : ℝ) / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) := by
    obtain ⟨hmq, c, hclass⟩ := hcrt d hd e he hc
    have hm : 0 < ∏ i, Nat.lcm (d i) (e i) :=
      Finset.prod_pos fun i _ =>
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hcoord0 d hd i) (hcoord0 e he i))
    have hcard : C d e = q / (∏ i, Nat.lcm (d i) (e i)) := by
      dsimp only [C]
      simp_rw [← hclass]
      rw [← Nat.count_eq_card_filter_range]
      simpa only [Nat.mod_eq_zero_of_dvd hmq, Nat.not_lt_zero, ite_false, add_zero] using
        Nat.count_modEq_card q hm c
    rw [hcard, Nat.cast_div_charZero hmq, Nat.cast_prod]
  have hexpand :
      (∑ n ∈ Finset.range q,
        (∑ d ∈ D, if ∀ i, d i ∣ n + h i then lam d else 0) ^ 2) =
        ∑ d ∈ D, ∑ e ∈ D, (C d e : ℝ) * (lam d * lam e) := by
    calc
      _ = ∑ n ∈ Finset.range q, ∑ d ∈ D, ∑ e ∈ D,
          if (∀ i, d i ∣ n + h i) ∧ (∀ i, e i ∣ n + h i)
          then lam d * lam e else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        simp only [pow_two, Finset.sum_mul_sum, ite_mul, mul_ite, mul_zero, zero_mul,
          ← ite_and, and_comm]
      _ = ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ Finset.range q,
          if (∀ i, d i ∣ n + h i) ∧ (∀ i, e i ∣ n + h i)
          then lam d * lam e else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)
  · rw [ite_eq_left hc, hcount d hd e he hc]
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
    calc
      _ = ((1 / (q : ℝ)) * (q : ℝ)) *
          (lam d * lam e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))) := by ring
      _ = _ := by rw [one_div, inv_mul_cancel₀ hqR, one_mul]
  · have hz : C d e = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
        (fun n _ hn => hc (hcross d hd e n hn.1 hn.2)))
    simp [hc, hz]

end

section
open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

open Classical in
theorem selbergCoefficient_l1_le
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ) (L : ℕ) (B : ℝ)
    (hy : ∀ r ∈ y.support,
      Squarefree (∏ i, r i) ∧ (∏ i, r i) ≤ L)
    (hB : ∀ r, |y r| ≤ B) :
    let D := y.support.biUnion
      (fun r => Fintype.piFinset (fun i => (r i).divisors))
    (∑ d ∈ D, |selbergCoefficient y d|) ≤
      B * (L : ℝ) *
        (1 + Real.log (L : ℝ)) ^ (2 ^ (Fintype.card ι + 2) - 1) := by
  dsimp only
  let D := y.support.biUnion
    (fun r => Fintype.piFinset (fun i => (r i).divisors))
  let P (r : ι → ℕ) := ∏ i, r i
  have hB0 : 0 ≤ B := (abs_nonneg (y (fun _ => 0))).trans (hB _)
  have hprod (r : ι → ℕ) (s : Finset ι) :
      Squarefree (∏ i ∈ s, r i) →
        (∏ i ∈ s, r i).divisors.card = ∏ i ∈ s, (r i).divisors.card ∧
        (∏ i ∈ s, r i).totient = ∏ i ∈ s, (r i).totient := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      intro hs
      rw [Finset.prod_insert hi] at hs
      obtain ⟨hc, _, hs⟩ := Nat.squarefree_mul_iff.mp hs
      simp only [Finset.prod_insert hi, hc.card_divisors_mul, Nat.totient_mul hc,
        (ih hs).1, (ih hs).2, and_self]
  have hpos (r : ι → ℕ) (hr : r ∈ y.support) : 0 < P r :=
    Nat.pos_of_ne_zero (hy r hr).1.ne_zero
  have hphi (r : ι → ℕ) (hr : r ∈ y.support) :
      (∏ i, ((r i).totient : ℝ)) = ((P r).totient : ℝ) := by
    exact_mod_cast (hprod r Finset.univ (hy r hr).1).2.symm
  have hcoeff (d : ι → ℕ) :
      |selbergCoefficient y d| ≤
        ∑ r ∈ y.support, if ∀ i, d i ∣ r i then
          B * (P r : ℝ) / ((P r).totient : ℝ) else 0 := by
    unfold selbergCoefficient Finsupp.sum
    rw [Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro r hr
    by_cases hdr : ∀ i, d i ∣ r i
    · simp only [ite_eq_left hdr]
      rw [← mul_div_assoc, abs_div, abs_mul, abs_mul,
        hphi r hr, Nat.abs_cast]
      have hmu : |(ArithmeticFunction.moebius (P d) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := P d))
      have hpd : P d ≤ P r :=
        Nat.le_of_dvd (hpos r hr) (Finset.prod_dvd_prod_of_dvd d r (fun i _ => hdr i))
      rw [← Nat.cast_prod, Nat.abs_cast]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      calc
        _ ≤ 1 * (P d : ℝ) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _))
            (hB r) (abs_nonneg _) (by positivity)
        _ ≤ 1 * (P r : ℝ) * B :=
          mul_le_mul_of_nonneg_right
            (by simpa only [one_mul] using (Nat.cast_le (α := ℝ)).mpr hpd) hB0
        _ = _ := by ring
    · simp [hdr]
  have hroot (r : ι → ℕ) (hr : r ∈ y.support) :
      (∑ d ∈ D, if ∀ i, d i ∣ r i then
        B * (P r : ℝ) / ((P r).totient : ℝ) else 0) ≤
        B * ((P r).divisors.card : ℝ) ^ 2 := by
    have hf : D.filter (fun d => ∀ i, d i ∣ r i) =
        Fintype.piFinset (fun i => (r i).divisors) := by
      ext d
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hd⟩ i
        exact ⟨hd i, (ne_zero_of_dvd_ne_zero (hpos r hr).ne'
          (Finset.dvd_prod_of_mem r (Finset.mem_univ i)))⟩
      · intro hd
        refine ⟨Finset.mem_biUnion.mpr
          ⟨r, hr, Fintype.mem_piFinset.mpr (fun i => Nat.mem_divisors.mpr (hd i))⟩,
          fun i => (hd i).1⟩
    rw [← Finset.sum_filter, hf, Finset.sum_const, nsmul_eq_mul,
      Fintype.card_piFinset, ← (hprod r Finset.univ (hy r hr).1).1]
    calc
      _ = B * ((P r : ℝ) / ((P r).totient : ℝ)) *
          ((P r).divisors.card : ℝ) := by ring
      _ ≤ B * ((P r).divisors.card : ℝ) * ((P r).divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (div_totient_le_card_divisors (P r)) hB0)
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have hfiber :
      (∑ r ∈ y.support, ((P r).divisors.card : ℝ) ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 L, (n.divisors.card : ℝ) ^ (Fintype.card ι + 2) := by
    have hmap : ∀ r ∈ y.support, P r ∈ Finset.Icc 1 L :=
      fun r hr => Finset.mem_Icc.mpr ⟨hpos r hr, (hy r hr).2⟩
    rw [← Finset.sum_fiberwise_of_maps_to' hmap (fun n => (n.divisors.card : ℝ) ^ 2)]
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    have hsub : {r ∈ y.support | P r = n} ⊆
        Fintype.piFinset (fun _ : ι => n.divisors) := by
      intro r hr
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hn0⟩
      rw [← (Finset.mem_filter.mp hr).2]
      exact Finset.dvd_prod_of_mem r (Finset.mem_univ i)
    have hcard :
        ({r ∈ y.support | P r = n}.card : ℝ) ≤
          (n.divisors.card : ℝ) ^ Fintype.card ι := by
      have hh := Finset.card_le_card hsub
      simpa only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr hh
    calc
      _ = ({r ∈ y.support | P r = n}.card : ℝ) * (n.divisors.card : ℝ) ^ 2 := by
        simp
      _ ≤ (n.divisors.card : ℝ) ^ Fintype.card ι * (n.divisors.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = _ := (pow_add _ _ _).symm
  calc
    _ ≤ ∑ d ∈ D, ∑ r ∈ y.support, if ∀ i, d i ∣ r i then
        B * (P r : ℝ) / ((P r).totient : ℝ) else 0 :=
      Finset.sum_le_sum fun d _ => hcoeff d
    _ = ∑ r ∈ y.support, ∑ d ∈ D, if ∀ i, d i ∣ r i then
        B * (P r : ℝ) / ((P r).totient : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ r ∈ y.support, B * ((P r).divisors.card : ℝ) ^ 2 :=
      Finset.sum_le_sum hroot
    _ = B * ∑ r ∈ y.support, ((P r).divisors.card : ℝ) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ B * ∑ n ∈ Finset.Icc 1 L,
        (n.divisors.card : ℝ) ^ (Fintype.card ι + 2) :=
      mul_le_mul_of_nonneg_left hfiber hB0
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (sum_card_divisors_pow_le_mul_log_pow
          (Fintype.card ι + 2) L) hB0

open Classical in
theorem selberg_forward_inverse
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ)
    (hy : ∀ r ∈ y.support, Squarefree (∏ i, r i)) (r : ι → ℕ) :
    let D := y.support.biUnion
      (fun s => Fintype.piFinset (fun i => (s i).divisors))
    (ArithmeticFunction.moebius (∏ i, r i) : ℝ) *
        (∏ i, ((r i).totient : ℝ)) *
        (∑ d ∈ D, if ∀ i, r i ∣ d i then
          selbergCoefficient y d / (∏ i, (d i : ℝ)) else 0) = y r := by
  intro D
  have hmuSum (n : ℕ) :
      (∑ a ∈ n.divisors, (ArithmeticFunction.moebius a : ℝ)) =
        if n = 1 then 1 else 0 := by
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
      ArithmeticFunction.intCoe_apply] using
      congrArg (fun f : ArithmeticFunction ℝ => f n)
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  have hscalar (e : ℕ) (he : Squarefree e) (a : ℕ) :
      (∑ d ∈ e.divisors, if a ∣ d then (ArithmeticFunction.moebius d : ℝ) else 0) =
        if a = e then (ArithmeticFunction.moebius a : ℝ) else 0 := by
    by_cases hae : a ∣ e
    · have ha0 : a ≠ 0 := ne_zero_of_dvd_ne_zero he.ne_zero hae
      have hq0 : e / a ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd he.ne_zero.bot_lt hae) ha0.bot_lt).ne'
      have hset : e.divisors.filter (a ∣ ·) = (e / a).divisors.image (a * ·) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
        constructor
        · rintro ⟨⟨hde, _⟩, had⟩
          exact ⟨d / a, ⟨Nat.div_dvd_div had hde, hq0⟩, Nat.mul_div_cancel' had⟩
        · rintro ⟨b, ⟨hb, _⟩, rfl⟩
          refine ⟨⟨?_, he.ne_zero⟩, dvd_mul_right a b⟩
          rw [← Nat.mul_div_cancel' hae]
          exact Nat.mul_dvd_mul_left a hb
      have hcop : Nat.Coprime a (e / a) := by
        apply Nat.coprime_of_squarefree_mul
        rwa [Nat.mul_div_cancel' hae]
      rw [← Finset.sum_filter, hset, Finset.sum_image]
      · calc
          (∑ b ∈ (e / a).divisors, (ArithmeticFunction.moebius (a * b) : ℝ)) =
              ∑ b ∈ (e / a).divisors,
                (ArithmeticFunction.moebius a : ℝ) * ArithmeticFunction.moebius b := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
              (hcop.of_dvd_right (Nat.dvd_of_mem_divisors hb)), Int.cast_mul]
          _ = (ArithmeticFunction.moebius a : ℝ) * (if e / a = 1 then 1 else 0) := by
            rw [← Finset.mul_sum, hmuSum]
          _ = if a = e then (ArithmeticFunction.moebius a : ℝ) else 0 := by
            by_cases h : a = e
            · subst e
              simp [Nat.div_self ha0.bot_lt]
            · have hq : e / a ≠ 1 := fun hq => h (Nat.eq_of_dvd_of_div_eq_one hae hq)
              simp [h, hq]
      · exact fun _ _ _ _ => mul_left_cancel₀ ha0
    · have hne : a ≠ e := by
        rintro rfl
        exact hae dvd_rfl
      rw [ite_eq_right hne]
      apply Finset.sum_eq_zero
      intro d hd
      exact ite_eq_right (fun had => hae (had.trans (Nat.dvd_of_mem_divisors hd)))
  have hmuProd (d : ι → ℕ) (hd : Squarefree (∏ i, d i)) :
      (ArithmeticFunction.moebius (∏ i, d i) : ℝ) =
        ∏ i, (ArithmeticFunction.moebius (d i) : ℝ) := by
    exact_mod_cast ArithmeticFunction.IsMultiplicative.map_prod d
      ArithmeticFunction.isMultiplicative_moebius Finset.univ
      (fun i _ j _ hij => coprime_of_squarefree_fintype_prod d hd hij)
  have hbox (s : ι → ℕ) (hs : Squarefree (∏ i, s i)) :
      (∑ d ∈ Fintype.piFinset (fun i => (s i).divisors),
        if ∀ i, r i ∣ d i then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) else 0) =
          if r = s then (ArithmeticFunction.moebius (∏ i, r i) : ℝ) else 0 := by
    calc
      _ = ∑ d ∈ Fintype.piFinset (fun i => (s i).divisors),
          ∏ i, if r i ∣ d i then (ArithmeticFunction.moebius (d i) : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hds : ∀ i, d i ∣ s i := fun i =>
          Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hd i)
        rw [hmuProd d (hs.squarefree_of_dvd (Finset.prod_dvd_prod_of_dvd d s
          (fun i _ => hds i))), Fintype.prod_ite_zero]
      _ = ∏ i, ∑ d ∈ (s i).divisors,
          if r i ∣ d then (ArithmeticFunction.moebius d : ℝ) else 0 :=
        (Finset.prod_univ_sum (fun i => (s i).divisors)
          (fun i d => if r i ∣ d then (ArithmeticFunction.moebius d : ℝ) else 0)).symm
      _ = ∏ i, if r i = s i then (ArithmeticFunction.moebius (r i) : ℝ) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hscalar (s i) (hs.squarefree_of_dvd
          (Finset.dvd_prod_of_mem s (Finset.mem_univ i))) (r i)
      _ = if r = s then (ArithmeticFunction.moebius (∏ i, r i) : ℝ) else 0 := by
        simp only [Fintype.prod_ite_zero, ← funext_iff]
        split_ifs with hrs
        · subst s
          exact (hmuProd r hs).symm
        · rfl
  have hforward :
      (∑ d ∈ D, if ∀ i, r i ∣ d i then
        selbergCoefficient y d / (∏ i, (d i : ℝ)) else 0) =
      (ArithmeticFunction.moebius (∏ i, r i) : ℝ) * y r /
        (∏ i, ((r i).totient : ℝ)) := by
    calc
      _ = ∑ d ∈ D, ∑ s ∈ y.support,
          (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ s i) then
            (ArithmeticFunction.moebius (∏ i, d i) : ℝ) else 0) *
              (y s / (∏ i, ((s i).totient : ℝ))) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hprod : (∏ i, (d i : ℝ)) ≠ 0 := by
          obtain ⟨s, hs, hds⟩ := Finset.mem_biUnion.mp hd
          exact_mod_cast ((hy s hs).squarefree_of_dvd (Finset.prod_dvd_prod_of_dvd d s
            (fun i _ => Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hds i)))).ne_zero
        rw [selbergCoefficient, mul_right_comm, mul_div_cancel_right₀ _ hprod, Finsupp.sum]
        by_cases hrd : ∀ i, r i ∣ d i <;>
          simp [hrd, Finset.mul_sum, mul_ite, ite_mul]
      _ = ∑ s ∈ y.support, ∑ d ∈ D,
          (if (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ s i) then
            (ArithmeticFunction.moebius (∏ i, d i) : ℝ) else 0) *
              (y s / (∏ i, ((s i).totient : ℝ))) := Finset.sum_comm
      _ = ∑ s ∈ y.support,
          (if r = s then (ArithmeticFunction.moebius (∏ i, r i) : ℝ) else 0) *
            (y s / (∏ i, ((s i).totient : ℝ))) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [← Finset.sum_mul]
        congr 1
        have hset : D.filter (fun d => ∀ i, d i ∣ s i) =
            Fintype.piFinset (fun i => (s i).divisors) := by
          ext d
          simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
          constructor
          · rintro ⟨_, hds⟩ i
            exact ⟨hds i, ((hy s hs).squarefree_of_dvd
              (Finset.dvd_prod_of_mem s (Finset.mem_univ i))).ne_zero⟩
          · intro hds
            refine ⟨Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩, fun i => (hds i).1⟩
            exact Fintype.mem_piFinset.mpr fun i => Nat.mem_divisors.mpr (hds i)
        calc
          _ = ∑ d ∈ Fintype.piFinset (fun i => (s i).divisors),
              if ∀ i, r i ∣ d i then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) else 0 := by
            rw [← hset, Finset.sum_filter]
            simp only [← ite_and, and_comm]
          _ = _ := hbox s (hy s hs)
      _ = _ := by
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq]
        split_ifs with hr
        · ring
        · simp [Finsupp.notMem_support_iff.mp hr]
  rw [hforward]
  by_cases hyr : y r = 0
  · simp [hyr]
  have hsr := hy r (Finsupp.mem_support_iff.mpr hyr)
  have hphi : (∏ i, ((r i).totient : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hri := (hsr.squarefree_of_dvd (Finset.dvd_prod_of_mem r hi)).ne_zero
    exact_mod_cast (Nat.totient_pos.mpr hri.bot_lt).ne'
  have hmu : (ArithmeticFunction.moebius (∏ i, r i) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsr
  calc
    _ = (ArithmeticFunction.moebius (∏ i, r i) : ℝ) ^ 2 * y r := by
      field_simp
    _ = y r := by rw [hmu, one_mul]

open Classical in
theorem selberg_square_real_interval_crt
    {ι : Type*} [Fintype ι] (h : ι → ℕ) (hinj : Function.Injective h)
    (D : Finset (ι → ℕ)) (lam : (ι → ℕ) → ℝ)
    (W v : ℕ) (hW : 0 < W)
    (hD : ∀ d ∈ D,
      Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W)
    (hcover : ∀ a b : ι, h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (x : ℝ) (hx : 0 ≤ x) :
    |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq W n v then
          (∑ d ∈ D, if ∀ i, d i ∣ n + h i then lam d else 0) ^ 2
        else 0) -
      x / (W : ℝ) *
        (∑ d ∈ D, ∑ e ∈ D,
          if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
            lam d * lam e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))
          else 0)| ≤
      2 * (∑ d ∈ D, ∑ e ∈ D,
        if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
          |lam d * lam e| else 0) := by
  let I := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  have hinterval (a b q c : ℕ) (hab : a ≤ b) (hq : 0 < q) :
      |({n ∈ Finset.Ico a b | Nat.ModEq q n c}.card : ℝ) -
        ((b : ℝ) - a) / q| ≤ 1 := by
    let u : ℚ := ((b : ℚ) - c) / q
    let v : ℚ := ((a : ℚ) - c) / q
    have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
    have hvu : v ≤ u := by
      dsimp [u, v]
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right (by exact_mod_cast hab) _) hqQ.le
    have hdiff : 0 ≤ (⌈u⌉ : ℤ) - ⌈v⌉ := sub_nonneg.mpr (Int.ceil_mono hvu)
    have hcardZ :
        ({n ∈ Finset.Ico a b | Nat.ModEq q n c}.card : ℤ) =
          (⌈u⌉ : ℤ) - ⌈v⌉ := by
      simpa [u, v, max_eq_left hdiff] using Nat.Ico_filter_modEq_card a b hq c
    have hcardR :
        ({n ∈ Finset.Ico a b | Nat.ModEq q n c}.card : ℝ) =
          (((⌈u⌉ : ℤ) - ⌈v⌉ : ℤ) : ℝ) := by exact_mod_cast hcardZ
    have herr : |((⌈u⌉ : ℚ) - ⌈v⌉) - (u - v)| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        linarith [Int.le_ceil u, Int.ceil_lt_add_one u, Int.le_ceil v, Int.ceil_lt_add_one v]
    have herrR :
        |(((⌈u⌉ : ℤ) - ⌈v⌉ : ℤ) : ℝ) - ((u - v : ℚ) : ℝ)| ≤ 1 := by
      exact_mod_cast herr
    have huv : ((u - v : ℚ) : ℝ) = ((b : ℝ) - a) / q := by
      dsimp [u, v]
      push_cast
      ring
    rw [hcardR, ← huv]
    exact herrR
  have hrealcount (q c : ℕ) (hq : 0 < q) :
      |({n ∈ I | Nat.ModEq q n c}.card : ℝ) - x / q| ≤ 2 := by
    let a := ⌈x⌉₊
    let b := ⌊2 * x⌋₊ + 1
    have hab : a ≤ b :=
      (Nat.ceil_le_floor_add_one x).trans
        (Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1)
    have hlen : |((b : ℝ) - a) - x| ≤ 1 := by
      have hfl := Nat.floor_le (show 0 ≤ 2 * x by linarith)
      have hfu := Nat.lt_floor_add_one (2 * x)
      have hcl := Nat.le_ceil x
      have hcu := Nat.ceil_lt_add_one hx
      dsimp [a, b]
      push_cast
      rw [abs_le]
      constructor <;> linarith
    have hc : |({n ∈ I | Nat.ModEq q n c}.card : ℝ) -
        ((b : ℝ) - a) / q| ≤ 1 := by
      simpa [a, b, I, Finset.Ico_add_one_right_eq_Icc] using hinterval a b q c hab hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    calc
      _ = |(({n ∈ I | Nat.ModEq q n c}.card : ℝ) - ((b : ℝ) - a) / q) +
          (((b : ℝ) - a) - x) / q| := congrArg abs (by ring)
      _ ≤ |({n ∈ I | Nat.ModEq q n c}.card : ℝ) - ((b : ℝ) - a) / q| +
          |(((b : ℝ) - a) - x) / q| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add hc (by
        rw [abs_div, abs_of_pos hqR]
        exact (div_le_one hqR).mpr
          (hlen.trans (by exact_mod_cast (show 1 ≤ q from hq))))
      _ = 2 := by norm_num
  have hcoordW (d : ι → ℕ) (hd : d ∈ D) (i : ι) :
      Nat.Coprime (d i) W :=
    Nat.coprime_fintype_prod_left_iff.mp (hD d hd).2 i
  have hcross (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ)
      (n : ℕ) (hnd : ∀ i, d i ∣ n + h i) (hne : ∀ i, e i ∣ n + h i) :
      ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) := by
    intro a b hab
    by_contra hc
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpa' := dvd_trans hpa (hnd a)
    have hpb' := dvd_trans hpb (hne b)
    have hdist : p ∣ Nat.dist (h a) (h b) := by
      rw [← Nat.dist_add_add_left n, Nat.dist]
      exact dvd_add (Nat.dvd_sub hpa' hpb') (Nat.dvd_sub hpb' hpa')
    have hpW := hcover a b (fun hh => hab (hinj hh)) p hp hdist
    exact (hp.coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd_left hpa (hcoordW d hd a))) hpW
  have hcoord0 (d : ι → ℕ) (hd : d ∈ D) (i : ι) : d i ≠ 0 :=
    ((hD d hd).1.squarefree_of_dvd
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).ne_zero
  have hneg (m t n : ℕ) (hm : 0 < m) :
      Nat.ModEq m n (m - t % m) ↔ m ∣ n + t := by
    have hres : Nat.ModEq m (m - t % m + t) 0 := by
      have ht := (Nat.mod_modEq t m).add_left (m - t % m)
      rw [Nat.sub_add_cancel (Nat.mod_lt t hm).le] at ht
      exact ht.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl m))
    constructor
    · intro hn
      exact Nat.modEq_zero_iff_dvd.mp ((hn.add_right t).trans hres)
    · intro hn
      exact Nat.ModEq.add_right_cancel' t
        ((Nat.modEq_zero_iff_dvd.mpr hn).trans hres.symm)
  have hcrt (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ) (he : e ∈ D)
      (hc : ∀ i j : ι, i ≠ j → Nat.Coprime (d i) (e j)) :
      ∃ c : ℕ, ∀ n : ℕ,
        Nat.ModEq (W * ∏ i, Nat.lcm (d i) (e i)) n c ↔
          Nat.ModEq W n v ∧ (∀ i, d i ∣ n + h i) ∧
            (∀ i, e i ∣ n + h i) := by
    let s : Option ι → ℕ
      | none => W
      | some i => Nat.lcm (d i) (e i)
    let a : Option ι → ℕ
      | none => v
      | some i => Nat.lcm (d i) (e i) - h i % Nat.lcm (d i) (e i)
    let l := (Finset.univ : Finset (Option ι)).toList
    have hpos (i : ι) : 0 < Nat.lcm (d i) (e i) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hcoord0 d hd i) (hcoord0 e he i))
    have hWs (i : ι) : Nat.Coprime W (s (some i)) := by
      change Nat.Coprime W (Nat.lcm (d i) (e i))
      exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul _ _)
        ((hcoordW d hd i).symm.mul_right (hcoordW e he i).symm)
    have hss (i j : ι) (hij : i ≠ j) :
        Nat.Coprime (s (some i)) (s (some j)) := by
      have h₁ : Nat.Coprime (d i) (d j * e j) :=
        (coprime_of_squarefree_fintype_prod d (hD d hd).1 hij).mul_right (hc i j hij)
      have h₂ : Nat.Coprime (e i) (d j * e j) :=
        ((hc j i hij.symm).symm).mul_right
          (coprime_of_squarefree_fintype_prod e (hD e he).1 hij)
      exact Nat.Coprime.of_dvd (Nat.lcm_dvd_mul _ _) (Nat.lcm_dvd_mul _ _)
        (h₁.mul_left h₂)
    have co : l.Pairwise (fun u z => Nat.Coprime (s u) (s z)) := by
      change ((Finset.univ : Finset (Option ι)).toList).Pairwise _
      refine ((Finset.univ : Finset (Option ι)).nodup_toList).pairwise_of_forall_ne ?_
      intro u hu z hz huz
      cases u with
      | none =>
        cases z with
        | none => exact (huz rfl).elim
        | some j => exact hWs j
      | some i =>
        cases z with
        | none => exact (hWs i).symm
        | some j => exact hss i j (by simpa using huz)
    let c : ℕ := Nat.chineseRemainderOfList a s l co
    have hprod : (l.map s).prod = W * ∏ i, Nat.lcm (d i) (e i) := by
      dsimp [l]
      rw [Finset.prod_map_toList, Fintype.prod_option]
    have hcrtOption (n : ℕ) :
        Nat.ModEq (W * ∏ i, Nat.lcm (d i) (e i)) n c ↔
          ∀ o : Option ι, Nat.ModEq (s o) n (a o) := by
      rw [← hprod]
      change Nat.ModEq (l.map s).prod n
        (Nat.chineseRemainderOfList a s l co : ℕ) ↔ _
      constructor
      · intro hn o
        have ho : o ∈ l := by simp [l]
        exact ((Nat.modEq_list_map_prod_iff co).mp hn o ho).trans
          ((Nat.chineseRemainderOfList a s l co).property o ho)
      · intro hn
        exact Nat.chineseRemainderOfList_modEq_unique a s l co
          (fun o _ => hn o)
    refine ⟨c, ?_⟩
    intro n
    rw [hcrtOption]
    constructor
    · intro hn
      refine ⟨hn none, ?_, ?_⟩
      · intro i
        exact (Nat.lcm_dvd_iff.mp ((hneg _ _ _ (hpos i)).mp (hn (some i)))).1
      · intro i
        exact (Nat.lcm_dvd_iff.mp ((hneg _ _ _ (hpos i)).mp (hn (some i)))).2
    · rintro ⟨hn, hdn, hen⟩ o
      cases o with
      | none => exact hn
      | some i =>
        exact (hneg _ _ _ (hpos i)).mpr (Nat.lcm_dvd (hdn i) (hen i))
  let C (d e : ι → ℕ) :=
    {n ∈ I | Nat.ModEq W n v ∧ (∀ i, d i ∣ n + h i) ∧
      (∀ i, e i ∣ n + h i)}.card
  have hcount (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ) (he : e ∈ D)
      (hc : ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) :
      |(C d e : ℝ) - x / ((W * ∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ)| ≤ 2 := by
    obtain ⟨c, hclass⟩ := hcrt d hd e he hc
    have hq : 0 < W * ∏ i, Nat.lcm (d i) (e i) := by
      apply Nat.mul_pos hW
      exact Finset.prod_pos fun i _ =>
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hcoord0 d hd i) (hcoord0 e he i))
    simpa only [C, ← hclass] using hrealcount _ c hq
  have hexpand :
      (∑ n ∈ I, if Nat.ModEq W n v then
        (∑ d ∈ D, if ∀ i, d i ∣ n + h i then lam d else 0) ^ 2 else 0) =
      ∑ d ∈ D, ∑ e ∈ D, (C d e : ℝ) * (lam d * lam e) := by
    calc
      _ = ∑ n ∈ I, ∑ d ∈ D, ∑ e ∈ D,
          if Nat.ModEq W n v ∧ (∀ i, d i ∣ n + h i) ∧
            (∀ i, e i ∣ n + h i) then lam d * lam e else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : Nat.ModEq W n v
        · simp only [hn, ite_true, pow_two, Finset.sum_mul_sum]
          simp only [ite_mul, mul_ite, mul_zero, zero_mul, ← ite_and, true_and, and_comm]
        · simp [hn]
      _ = ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ I,
          if Nat.ModEq W n v ∧ (∀ i, d i ∣ n + h i) ∧
            (∀ i, e i ∣ n + h i) then lam d * lam e else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hpair (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ) (he : e ∈ D) :
      |(C d e : ℝ) * (lam d * lam e) - x / (W : ℝ) *
        (if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
          lam d * lam e / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) else 0)| ≤
      2 * (if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
        |lam d * lam e| else 0) := by
    by_cases hc : ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)
    · simp only [ite_eq_left hc]
      have hf :
          (C d e : ℝ) * (lam d * lam e) - x / (W : ℝ) *
            (lam d * lam e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))) =
          ((C d e : ℝ) - x / ((W * ∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ)) *
            (lam d * lam e) := by
        push_cast
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [hf, abs_mul]
      exact mul_le_mul_of_nonneg_right (hcount d hd e he hc) (abs_nonneg _)
    · have hz : C d e = 0 :=
        Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
          (fun n _ hn => hc (hcross d hd e n hn.2.1 hn.2.2)))
      simp [hc, hz]
  change |(∑ n ∈ I, if Nat.ModEq W n v then
      (∑ d ∈ D, if ∀ i, d i ∣ n + h i then lam d else 0) ^ 2 else 0) -
      x / (W : ℝ) * _| ≤ _
  rw [hexpand, Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        |(C d e : ℝ) * (lam d * lam e) - x / (W : ℝ) *
          (if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
            lam d * lam e / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) else 0)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        2 * (if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
          |lam d * lam e| else 0) :=
      Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => hpair d hd e he

open Classical in
theorem div_prod_lcm_eq_sum_totient_mul
    {ι : Type*} [Fintype ι] (E : Finset (ι → ℕ)) (d e : ι → ℕ)
    (hd : ∀ i, 0 < d i)
    (hE : ∀ u : ι → ℕ, (∀ i, u i ∣ d i) → u ∈ E)
    (a b : ℝ) :
    a * b / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) =
      ∑ u ∈ E, if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
        (∏ i, ((u i).totient : ℝ)) *
          (a / (∏ i, (d i : ℝ))) * (b / (∏ i, (e i : ℝ)))
      else 0 := by
  have hbox :
      E.filter (fun u => (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i)) =
        Fintype.piFinset (fun i => (Nat.gcd (d i) (e i)).divisors) := by
    ext u
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hud, hue⟩ i
      exact ⟨Nat.dvd_gcd (hud i) (hue i), (Nat.gcd_pos_of_pos_left (e i) (hd i)).ne'⟩
    · intro hu
      have hud : ∀ i, u i ∣ d i := fun i => (Nat.dvd_gcd_iff.mp (hu i).1).1
      exact ⟨hE u hud, hud, fun i => (Nat.dvd_gcd_iff.mp (hu i).1).2⟩
  have hphisum :
      (∑ u ∈ E, if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
        (∏ i, ((u i).totient : ℝ)) else 0) = ∏ i, (Nat.gcd (d i) (e i) : ℝ) := by
    rw [← Finset.sum_filter, hbox,
      ← Finset.prod_univ_sum (fun i => (Nat.gcd (d i) (e i)).divisors)
        (fun _ n => (n.totient : ℝ))]
    apply Finset.prod_congr rfl
    intro i hi
    exact_mod_cast Nat.sum_totient (Nat.gcd (d i) (e i))
  have hG : (∏ i, (Nat.gcd (d i) (e i) : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact_mod_cast (Nat.gcd_pos_of_pos_left (e i) (hd i)).ne'
  have hprod :
      (∏ i, (Nat.gcd (d i) (e i) : ℝ)) * (∏ i, (Nat.lcm (d i) (e i) : ℝ)) =
        (∏ i, (d i : ℝ)) * (∏ i, (e i : ℝ)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact_mod_cast Nat.gcd_mul_lcm (d i) (e i)
  calc
    _ = (∏ i, (Nat.gcd (d i) (e i) : ℝ)) * (a * b) /
        ((∏ i, (Nat.gcd (d i) (e i) : ℝ)) * (∏ i, (Nat.lcm (d i) (e i) : ℝ))) :=
      (mul_div_mul_left _ _ hG).symm
    _ = (∏ i, (Nat.gcd (d i) (e i) : ℝ)) *
        (a / (∏ i, (d i : ℝ))) * (b / (∏ i, (e i : ℝ))) := by
      rw [hprod]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by
      rw [← hphisum]
      simp only [Finset.sum_mul, ite_mul, zero_mul]

open Classical in
theorem selberg_unrestricted_lcm_diagonal
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ)
    (hy : ∀ r ∈ y.support, Squarefree (∏ i, r i)) :
    let D := y.support.biUnion
      (fun r => Fintype.piFinset (fun i => (r i).divisors))
    (∑ d ∈ D, ∑ e ∈ D,
      selbergCoefficient y d * selbergCoefficient y e /
        (∏ i, (Nat.lcm (d i) (e i) : ℝ))) =
      y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ))) := by
  intro D
  let A (d : ι → ℕ) : ℝ :=
    selbergCoefficient y d / (∏ i, (d i : ℝ))
  let Φ (u : ι → ℕ) : ℝ := ∏ i, ((u i).totient : ℝ)
  have hsf (d : ι → ℕ) (hd : d ∈ D) : Squarefree (∏ i, d i) := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    exact (hy r hr).squarefree_of_dvd
      (Finset.prod_dvd_prod_of_dvd d r fun i _ =>
        Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr i))
  have hpos (d : ι → ℕ) (hd : d ∈ D) (i : ι) : 0 < d i :=
    ((hsf d hd).squarefree_of_dvd
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).ne_zero.bot_lt
  have hdown (d : ι → ℕ) (hd : d ∈ D)
      (u : ι → ℕ) (hu : ∀ i, u i ∣ d i) : u ∈ D := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    refine Finset.mem_biUnion.mpr ⟨r, hr, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    have hri := Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hdr i)
    exact Nat.mem_divisors.mpr ⟨(hu i).trans hri.1, hri.2⟩
  have hsD : y.support ⊆ D := by
    intro r hr
    refine Finset.mem_biUnion.mpr ⟨r, hr, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    exact Nat.mem_divisors.mpr ⟨dvd_rfl,
      ((hy r hr).squarefree_of_dvd
        (Finset.dvd_prod_of_mem r (Finset.mem_univ i))).ne_zero⟩
  have hkernel (d : ι → ℕ) (hd : d ∈ D) (e : ι → ℕ) :
      selbergCoefficient y d * selbergCoefficient y e /
          (∏ i, (Nat.lcm (d i) (e i) : ℝ)) =
      ∑ u ∈ D,
        if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
          Φ u * A d * A e else 0 :=
    div_prod_lcm_eq_sum_totient_mul D d e (hpos d hd)
      (fun u hu => hdown d hd u hu) (selbergCoefficient y d) (selbergCoefficient y e)
  have hdiag (u : ι → ℕ) (hu : u ∈ D) :
      Φ u * (∑ d ∈ D, if ∀ i, u i ∣ d i then A d else 0) ^ 2 =
      y u ^ 2 / Φ u := by
    have hφ : Φ u ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact_mod_cast (Nat.totient_pos.mpr (hpos u hu i)).ne'
    have hμ : (ArithmeticFunction.moebius (∏ i, u i) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsf u hu)
    have hinv := selberg_forward_inverse y hy u
    change (ArithmeticFunction.moebius (∏ i, u i) : ℝ) * Φ u *
      (∑ d ∈ D, if ∀ i, u i ∣ d i then A d else 0) = y u at hinv
    have hsquare := congrArg (fun z : ℝ => z ^ (2 : ℕ)) hinv
    simp only [mul_pow, hμ, one_mul] at hsquare
    apply (eq_div_iff hφ).mpr
    linear_combination hsquare
  calc
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ D,
        if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
          Φ u * A d * A e else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_congr rfl (fun e _ => hkernel d hd e)
    _ = ∑ u ∈ D, ∑ d ∈ D, ∑ e ∈ D,
        if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
          Φ u * A d * A e else 0 := by
      rw [eq_comm, Finset.sum_comm,
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    _ = ∑ u ∈ D,
        Φ u * (∑ d ∈ D, if ∀ i, u i ∣ d i then A d else 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum,
        mul_ite, ite_mul, mul_zero, zero_mul, ← ite_and, and_comm, mul_assoc]
    _ = ∑ u ∈ D, y u ^ 2 / Φ u := Finset.sum_congr rfl hdiag
    _ = y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ))) := by
      rw [Finsupp.sum]
      exact (Finset.sum_subset hsD (fun r _ hnot => by
        simp [Φ, Finsupp.notMem_support_iff.mp hnot])).symm

open Classical in
theorem selberg_cross_correction_le
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ)
    (L W D₀ : ℕ) (B : ℝ) (hD₀ : 0 < D₀)
    (hsmall : _root_.primorial D₀ ∣ W)
    (hy : ∀ r ∈ y.support,
      Squarefree (∏ i, r i) ∧
        Nat.Coprime (∏ i, r i) W ∧ (∏ i, r i) ≤ L)
    (hB : ∀ r, |y r| ≤ B) :
    let D := y.support.biUnion
      (fun r => Fintype.piFinset (fun i => (r i).divisors))
    let k := Fintype.card ι
    let K := k * (k - 1)
    let M : ℝ := ∑ n ∈ Finset.Icc 1 L,
      if Squarefree n ∧ Nat.Coprime n W then 1 / (n.totient : ℝ) else 0
    |∑ d ∈ D, ∑ e ∈ D,
      if ¬ (∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) then
        selbergCoefficient y d * selbergCoefficient y e /
          (∏ i, (Nat.lcm (d i) (e i) : ℝ))
      else 0| ≤
      B ^ 2 *
        ((8 * Real.exp 8 / (D₀ : ℝ)) * (K : ℝ) *
          (Real.exp 8) ^ (K - 1)) * M ^ k := by
  intro D k K M
  let Q : ℕ := L + 1
  let J : Finset (ι × ι) := (Finset.univ : Finset ι).offDiag
  let E : Finset (ι → ℕ) := Fintype.piFinset (fun _ : ι => Finset.Icc 1 L)
  let T : Finset (J → ℕ) := Fintype.piFinset (fun _ : J => Finset.Icc 1 Q)
  let ones : J → ℕ := fun _ => 1
  let Phi (r : ι → ℕ) : ℝ := ∏ i, ((r i).totient : ℝ)
  let Psi (s : J → ℕ) : ℝ := ∏ ab : J, ((s ab).totient : ℝ)
  let crossMu (s : J → ℕ) : ℝ :=
    ∏ ab : J, (ArithmeticFunction.moebius (s ab) : ℝ)
  let A (d : ι → ℕ) : ℝ := selbergCoefficient y d / (∏ i, (d i : ℝ))
  let S (r : ι → ℕ) : ℝ :=
    ∑ d ∈ D, if ∀ i, r i ∣ d i then A d else 0
  let lower (f : J → ι) (u : ι → ℕ) (s : J → ℕ) : ι → ℕ :=
    fun i => Nat.lcm (u i) ((Finset.univ.filter (fun ab : J => f ab = i)).lcm s)
  let left := lower (fun ab : J => ab.1.1)
  let right := lower (fun ab : J => ab.1.2)
  let F (s : J → ℕ) : ℝ :=
    crossMu s * ∑ u ∈ E, Phi u * S (left u s) * S (right u s)
  have hrootmem (r : ι → ℕ) (hr : r ∈ y.support)
      (d : ι → ℕ) (hdr : ∀ i, d i ∣ r i) : d ∈ D := by
    refine Finset.mem_biUnion.mpr ⟨r, hr, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    exact Nat.mem_divisors.mpr ⟨hdr i,
      ((hy r hr).1.squarefree_of_dvd
        (Finset.dvd_prod_of_mem r (Finset.mem_univ i))).ne_zero⟩
  have hsD : y.support ⊆ D := fun r hr => hrootmem r hr r (fun _ => dvd_rfl)
  have hdown (d : ι → ℕ) (hd : d ∈ D)
      (r : ι → ℕ) (hrd : ∀ i, r i ∣ d i) : r ∈ D := by
    obtain ⟨t, ht, hdt⟩ := Finset.mem_biUnion.mp hd
    exact hrootmem t ht r fun i =>
      (hrd i).trans (Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdt i))
  have hdata (d : ι → ℕ) (hd : d ∈ D) :
      Squarefree (∏ i, d i) ∧
        Nat.Coprime (∏ i, d i) W ∧ (∏ i, d i) ≤ L := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    have hdiv : (∏ i, d i) ∣ ∏ i, r i :=
      Finset.prod_dvd_prod_of_dvd d r fun i _ =>
        Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr i)
    exact ⟨(hy r hr).1.squarefree_of_dvd hdiv,
      Nat.Coprime.of_dvd_left hdiv (hy r hr).2.1,
      (Nat.le_of_dvd (hy r hr).1.ne_zero.bot_lt hdiv).trans (hy r hr).2.2⟩
  have hDE : D ⊆ E := by
    intro d hd
    refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
    have hcoord := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
    exact ⟨((hdata d hd).1.squarefree_of_dvd hcoord).ne_zero.bot_lt,
      (Nat.le_of_dvd (hdata d hd).1.ne_zero.bot_lt hcoord).trans (hdata d hd).2.2⟩
  have hysumE (d : ι → ℕ) :
      y.sum (fun r yr => if ∀ i, d i ∣ r i then yr / Phi r else 0) =
      ∑ r ∈ E, if (∏ i, r i) ≤ L ∧ (∀ i, d i ∣ r i) then
        y r / Phi r else 0 := by
    rw [Finsupp.sum]
    calc
      _ = ∑ r ∈ y.support,
          if (∏ i, r i) ≤ L ∧ (∀ i, d i ∣ r i) then y r / Phi r else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [(hy r hr).2.2]
      _ = _ := by
        apply Finset.sum_subset (hsD.trans hDE)
        intro r hr hnot
        simp [Finsupp.notMem_support_iff.mp hnot]
  have hEsumzero (d : ι → ℕ) (hd : d ∉ D) :
      (∑ r ∈ E, if (∏ i, r i) ≤ L ∧ (∀ i, d i ∣ r i) then
        y r / Phi r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hyr : r ∈ y.support
    · exact ite_eq_right (fun h => hd (hrootmem r hyr d h.2))
    · simp [Finsupp.notMem_support_iff.mp hyr]
  have hcoef (d : ι → ℕ) :
      selbergCoefficient y d =
        if Nat.Coprime (∏ i, d i) W then
          (∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * (d i : ℝ)) *
            ∑ r ∈ E, if (∏ i, r i) ≤ L ∧ (∀ i, d i ∣ r i) then
              y r / Phi r else 0
        else 0 := by
    rw [selbergCoefficient_eq_prod y (fun r hr => (hy r hr).1) d, hysumE d]
    by_cases hd : d ∈ D
    · rw [ite_eq_left (hdata d hd).2.1]
    · simp [hEsumzero d hd]
  have hzero (d : ι → ℕ) (hd : d ∉ D) : selbergCoefficient y d = 0 := by
    rw [hcoef d]
    simp [hEsumzero d hd]
  have hS (r : ι → ℕ) :
      S r = (ArithmeticFunction.moebius (∏ i, r i) : ℝ) * y r / Phi r := by
    by_cases hr : r ∈ D
    · have hφ : Phi r ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hri := ((hdata r hr).1.squarefree_of_dvd
          (Finset.dvd_prod_of_mem r hi)).ne_zero
        exact_mod_cast (Nat.totient_pos.mpr hri.bot_lt).ne'
      have hμ : (ArithmeticFunction.moebius (∏ i, r i) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hdata r hr).1
      have hinv := selberg_forward_inverse y (fun u hu => (hy u hu).1) r
      change (ArithmeticFunction.moebius (∏ i, r i) : ℝ) * Phi r * S r = y r at hinv
      apply (eq_div_iff hφ).mpr
      calc
        S r * Phi r = (ArithmeticFunction.moebius (∏ i, r i) : ℝ) ^ 2 *
            (S r * Phi r) := by rw [hμ, one_mul]
        _ = (ArithmeticFunction.moebius (∏ i, r i) : ℝ) *
            ((ArithmeticFunction.moebius (∏ i, r i) : ℝ) * Phi r * S r) := by ring
        _ = _ := by rw [hinv]
    · have hyr : y r = 0 :=
        Finsupp.notMem_support_iff.mp (fun hrs => hr (hsD hrs))
      have hSr : S r = 0 := by
        dsimp only [S]
        apply Finset.sum_eq_zero
        intro d hd
        exact ite_eq_right (fun hrd => hr (hdown d hd r hrd))
      simp [hSr, hyr]
  have hSE (r : ι → ℕ) :
      (∑ d ∈ E, if ∀ i, r i ∣ d i then A d else 0) = S r := by
    dsimp only [S]
    symm
    apply Finset.sum_subset hDE
    intro d hd hnot
    simp [A, hzero d hnot]
  have hcoordE (d : ι → ℕ) (hd : d ∈ E) (i : ι) : 1 ≤ d i ∧ d i ≤ L :=
    Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hd i)
  let theta (d e : ι → ℕ) : ℝ :=
    selbergCoefficient y d * selbergCoefficient y e /
      (∏ i, (Nat.lcm (d i) (e i) : ℝ))
  have hkernel (d : ι → ℕ) (hd : d ∈ E) (e : ι → ℕ) :
      theta d e = ∑ u ∈ E,
        if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
          Phi u * A d * A e else 0 := by
    refine div_prod_lcm_eq_sum_totient_mul E d e (fun i => (hcoordE d hd i).1) ?_
      (selbergCoefficient y d) (selbergCoefficient y e)
    intro u hu
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr
      ⟨(ne_zero_of_dvd_ne_zero (Nat.ne_of_gt (hcoordE d hd i).1) (hu i)).bot_lt,
        (Nat.le_of_dvd (hcoordE d hd i).1 (hu i)).trans (hcoordE d hd i).2⟩
  have hcrossBox (d : ι → ℕ) (hd : d ∈ E) (e : ι → ℕ) :
      T.filter (fun s => ∀ ab : J, s ab ∣ d ab.1.1 ∧ s ab ∣ e ab.1.2) =
        Fintype.piFinset (fun ab : J => (Nat.gcd (d ab.1.1) (e ab.1.2)).divisors) := by
    ext s
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hs⟩ ab
      exact ⟨Nat.dvd_gcd (hs ab).1 (hs ab).2,
        (Nat.gcd_pos_of_pos_left (e ab.1.2) (hcoordE d hd ab.1.1).1).ne'⟩
    · intro hs
      have hdiv := fun ab => Nat.dvd_gcd_iff.mp (hs ab).1
      refine ⟨?_, hdiv⟩
      apply Fintype.mem_piFinset.mpr
      intro ab
      apply Finset.mem_Icc.mpr
      refine ⟨(ne_zero_of_dvd_ne_zero
        (Nat.ne_of_gt (hcoordE d hd ab.1.1).1) (hdiv ab).1).bot_lt, ?_⟩
      exact ((Nat.le_of_dvd (hcoordE d hd ab.1.1).1 (hdiv ab).1).trans
        (hcoordE d hd ab.1.1).2).trans (Nat.le_succ L)
  have hmuSum (a b : ℕ) :
      (∑ n ∈ (Nat.gcd a b).divisors, (ArithmeticFunction.moebius n : ℝ)) =
        if Nat.Coprime a b then 1 else 0 := by
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
      ArithmeticFunction.intCoe_apply, Nat.coprime_iff_gcd_eq_one] using
      congrArg (fun f : ArithmeticFunction ℝ => f (Nat.gcd a b))
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  have hmobius (d : ι → ℕ) (hd : d ∈ E) (e : ι → ℕ) :
      (∑ s ∈ T, if ∀ ab : J, s ab ∣ d ab.1.1 ∧ s ab ∣ e ab.1.2 then
        crossMu s else 0) =
      if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then 1 else 0 := by
    rw [← Finset.sum_filter, hcrossBox d hd e]
    dsimp only [crossMu]
    rw [← Finset.prod_univ_sum
      (fun ab : J => (Nat.gcd (d ab.1.1) (e ab.1.2)).divisors)
      (fun _ n => (ArithmeticFunction.moebius n : ℝ))]
    simp_rw [hmuSum]
    rw [Fintype.prod_ite_zero]
    simp only [Finset.prod_const_one]
    congr 1
    apply propext
    constructor
    · intro hs a b hab
      exact hs ⟨(a, b), Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hab⟩⟩
    · intro hs ab
      exact hs _ _ (Finset.mem_offDiag.mp ab.2).2.2
  have hLower (f : J → ι) (u : ι → ℕ) (s : J → ℕ) (d : ι → ℕ) :
      (∀ i, lower f u s i ∣ d i) ↔
        (∀ i, u i ∣ d i) ∧ (∀ ab : J, s ab ∣ d (f ab)) := by
    simp only [lower, Nat.lcm_dvd_iff, Finset.lcm_dvd_iff,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨fun i => (h i).1, fun ab => (h (f ab)).2 ab rfl⟩
    · rintro ⟨hu, hs⟩ i
      refine ⟨hu i, ?_⟩
      intro ab hab
      simpa only [hab] using hs ab
  have hLowerPair (u : ι → ℕ) (s : J → ℕ) (d e : ι → ℕ) :
      ((∀ i, left u s i ∣ d i) ∧ (∀ i, right u s i ∣ e i)) ↔
        (∀ ab : J, s ab ∣ d ab.1.1 ∧ s ab ∣ e ab.1.2) ∧
          ((∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i)) := by
    dsimp only [left, right]
    simp only [hLower, forall_and, and_assoc, and_left_comm, and_comm]
  let term (s : J → ℕ) (u d e : ι → ℕ) : ℝ :=
    crossMu s * Phi u *
      (if ∀ i, left u s i ∣ d i then A d else 0) *
      (if ∀ i, right u s i ∣ e i then A e else 0)
  have hterm (s : J → ℕ) (u d e : ι → ℕ) :
      term s u d e =
        (if ∀ ab : J, s ab ∣ d ab.1.1 ∧ s ab ∣ e ab.1.2 then crossMu s else 0) *
          (if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then Phi u * A d * A e else 0) := by
    have hh :
        ((∀ i, right u s i ∣ e i) ∧ (∀ i, left u s i ∣ d i)) ↔
          (((∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i)) ∧
            (∀ ab : J, s ab ∣ d ab.1.1 ∧ s ab ∣ e ab.1.2)) :=
      and_comm.trans ((hLowerPair u s d e).trans and_comm)
    simp only [term, mul_ite, ite_mul, mul_zero, zero_mul, ← ite_and, hh]
    split_ifs <;> ring
  have hpair (d : ι → ℕ) (hd : d ∈ E) (e : ι → ℕ) :
      (if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then theta d e else 0) =
        ∑ s ∈ T, ∑ u ∈ E, term s u d e := by
    simp_rw [hterm]
    simp only [← Finset.mul_sum]
    rw [← hkernel d hd e, ← Finset.sum_mul, hmobius d hd e]
    split_ifs <;> simp
  have hgood :
      (∑ d ∈ E, ∑ e ∈ E,
        if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then theta d e else 0) =
        ∑ s ∈ T, F s := by
    calc
      _ = ∑ d ∈ E, ∑ e ∈ E, ∑ s ∈ T, ∑ u ∈ E, term s u d e := by
        apply Finset.sum_congr rfl
        intro d hd
        exact Finset.sum_congr rfl (fun e _ => hpair d hd e)
      _ = ∑ s ∈ T, ∑ u ∈ E, ∑ d ∈ E, ∑ e ∈ E, term s u d e := by
        simp_rw [show ∀ d : ι → ℕ,
          (∑ e ∈ E, ∑ s ∈ T, ∑ u ∈ E, term s u d e) =
          ∑ s ∈ T, ∑ e ∈ E, ∑ u ∈ E, term s u d e from
            fun _ => Finset.sum_comm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s hs
        simp_rw [show ∀ d : ι → ℕ,
          (∑ e ∈ E, ∑ u ∈ E, term s u d e) =
          ∑ u ∈ E, ∑ e ∈ E, term s u d e from fun _ => Finset.sum_comm]
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        dsimp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        rw [← hSE (left u s), ← hSE (right u s)]
        simp only [term, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
  have hall : (∑ d ∈ E, ∑ e ∈ E, theta d e) =
      ∑ u ∈ E, Phi u * S u ^ 2 := by
    calc
      _ = ∑ d ∈ E, ∑ e ∈ E, ∑ u ∈ E,
          if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then Phi u * A d * A e else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact Finset.sum_congr rfl (fun e _ => hkernel d hd e)
      _ = ∑ u ∈ E, ∑ d ∈ E, ∑ e ∈ E,
          if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then Phi u * A d * A e else 0 := by
        rw [eq_comm, Finset.sum_comm,
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [← hSE u, pow_two, Finset.sum_mul_sum]
        simp only [Finset.mul_sum,
          mul_ite, ite_mul, mul_zero, zero_mul, ← ite_and, and_comm, mul_assoc]
  have honeT : ones ∈ T := by simp [T, ones, Q]
  have hLowerOne (f : J → ι) (u : ι → ℕ) : lower f u ones = u := by
    funext i
    have hrow : (Finset.univ.filter (fun ab : J => f ab = i)).lcm ones = 1 :=
      Nat.eq_one_of_dvd_one (Finset.lcm_dvd fun _ _ => dvd_rfl)
    simp only [lower, hrow, Nat.lcm_one_right]
  have hFone : F ones = ∑ d ∈ E, ∑ e ∈ E, theta d e := by
    rw [hall]
    dsimp only [F, left, right]
    simp only [hLowerOne, crossMu, ones, ArithmeticFunction.moebius_apply_one,
      Int.cast_one, Finset.prod_const_one, one_mul, pow_two, mul_assoc]
  have hbadE :
      (∑ d ∈ E, ∑ e ∈ E,
        if ¬ (∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) then theta d e else 0) =
        -(∑ s ∈ T.erase ones, F s) := by
    have hsplit : (∑ d ∈ E, ∑ e ∈ E, theta d e) =
        (∑ d ∈ E, ∑ e ∈ E,
          if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then theta d e else 0) +
        (∑ d ∈ E, ∑ e ∈ E,
          if ¬ (∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) then theta d e else 0) := by
      rw [← Finset.sum_add_distrib]
      simp_rw [← Finset.sum_filter, Finset.sum_filter_add_sum_filter_not]
    have ht := Finset.sum_erase_add (s := T) (f := F) honeT
    rw [hgood, ← hFone] at hsplit
    linarith
  have hbadD :
      (∑ d ∈ D, ∑ e ∈ D,
        if ¬ (∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) then theta d e else 0) =
        -(∑ s ∈ T.erase ones, F s) := by
    rw [← hbadE]
    calc
      _ = ∑ d ∈ D, ∑ e ∈ E,
          if ¬ (∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) then theta d e else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_subset hDE
        intro e he hnot
        simp [theta, hzero e hnot]
      _ = _ := by
        apply Finset.sum_subset hDE
        intro d hd hnot
        simp [theta, hzero d hnot]
  let fiber (f : J → ι) (i : ι) : Finset J := Finset.univ.filter (fun ab => f ab = i)
  have huLower (f : J → ι) (u : ι → ℕ) (s : J → ℕ) (i : ι) :
      u i ∣ lower f u s i := Nat.dvd_lcm_left _ _
  have hsLower (f : J → ι) (u : ι → ℕ) (s : J → ℕ) (ab : J) :
      s ab ∣ lower f u s (f ab) := by
    apply dvd_trans ?_ (Nat.dvd_lcm_right _ _)
    exact Finset.dvd_lcm (by simp)
  have hstar (u : ι → ℕ) (s : J → ℕ)
      (hl : y (left u s) ≠ 0) (hr : y (right u s) ≠ 0) :
      (∀ ab : J, Nat.Coprime (s ab) (u ab.1.1) ∧ Nat.Coprime (s ab) (u ab.1.2)) ∧
        (∀ ab cd : J, ab ≠ cd → (ab.1.1 = cd.1.1 ∨ ab.1.2 = cd.1.2) →
          Nat.Coprime (s ab) (s cd)) := by
    have hlSF := (hy _ (Finsupp.mem_support_iff.mpr hl)).1
    have hrSF := (hy _ (Finsupp.mem_support_iff.mpr hr)).1
    constructor
    · intro ab
      have hab : ab.1.1 ≠ ab.1.2 := (Finset.mem_offDiag.mp ab.2).2.2
      exact ⟨Nat.Coprime.of_dvd
        (hsLower (fun ab : J => ab.1.2) u s ab)
        (huLower (fun ab : J => ab.1.2) u s ab.1.1)
        (coprime_of_squarefree_fintype_prod _ hrSF hab).symm,
        Nat.Coprime.of_dvd
          (hsLower (fun ab : J => ab.1.1) u s ab)
          (huLower (fun ab : J => ab.1.1) u s ab.1.2)
          (coprime_of_squarefree_fintype_prod _ hlSF hab)⟩
    · intro ab cd habcd hshared
      rcases hshared with hfirst | hsecond
      · have hne : ab.1.2 ≠ cd.1.2 :=
          fun h => habcd (Subtype.ext (Prod.ext hfirst h))
        exact Nat.Coprime.of_dvd
          (hsLower (fun ab : J => ab.1.2) u s ab)
          (hsLower (fun ab : J => ab.1.2) u s cd)
          (coprime_of_squarefree_fintype_prod _ hrSF hne)
      · have hne : ab.1.1 ≠ cd.1.1 :=
          fun h => habcd (Subtype.ext (Prod.ext h hsecond))
        exact Nat.Coprime.of_dvd
          (hsLower (fun ab : J => ab.1.1) u s ab)
          (hsLower (fun ab : J => ab.1.1) u s cd)
          (coprime_of_squarefree_fintype_prod _ hlSF hne)
  have hphiProd (t : Finset J) (s : J → ℕ)
      (ht : Set.Pairwise (t : Set J) (Function.onFun Nat.Coprime s)) :
      (∏ ab ∈ t, s ab).totient = ∏ ab ∈ t, (s ab).totient := by
    have hφ : ArithmeticFunction.IsMultiplicative
        (⟨Nat.totient, Nat.totient_zero⟩ : ArithmeticFunction ℕ) :=
      ⟨Nat.totient_one, fun {_ _} h => Nat.totient_mul h⟩
    exact ArithmeticFunction.IsMultiplicative.map_prod s hφ t ht
  have hfactor (f : J → ι) (u : ι → ℕ) (s : J → ℕ)
      (hend : ∀ ab, Nat.Coprime (s ab) (u (f ab)))
      (hrow : ∀ ab cd, ab ≠ cd → f ab = f cd → Nat.Coprime (s ab) (s cd)) :
      Phi (lower f u s) = Phi u * Psi s := by
    have hi (i : ι) :
        (lower f u s i).totient = (u i).totient * ∏ ab ∈ fiber f i, (s ab).totient := by
      have hp : Set.Pairwise (fiber f i : Set J) (Function.onFun Nat.Coprime s) := by
        intro ab hab cd hcd hne
        exact hrow ab cd hne ((Finset.mem_filter.mp hab).2.trans
          (Finset.mem_filter.mp hcd).2.symm)
      have hc : Nat.Coprime (u i) (∏ ab ∈ fiber f i, s ab) := by
        apply Nat.Coprime.prod_right
        intro ab hab
        simpa only [(Finset.mem_filter.mp hab).2] using (hend ab).symm
      change (Nat.lcm (u i) ((fiber f i).lcm s)).totient = _
      rw [Finset.lcm_eq_prod hp, hc.lcm_eq_mul, Nat.totient_mul hc, hphiProd _ _ hp]
    have hnat : (∏ i, (lower f u s i).totient) =
        (∏ i, (u i).totient) * ∏ ab, (s ab).totient := by
      simp_rw [hi]
      rw [Finset.prod_mul_distrib]
      congr 1
      exact Finset.prod_fiberwise Finset.univ f (fun ab : J => (s ab).totient)
    dsimp only [Phi, Psi]
    exact_mod_cast hnat
  let P : Finset ℕ := (Finset.Icc (D₀ + 1) Q).filter Nat.Prime
  let V : Finset ℕ := insert 1
    ((Finset.Icc 2 Q).filter (fun n => Squarefree n ∧ n.primeFactors ⊆ P))
  let Tr : Finset (J → ℕ) := Fintype.piFinset (fun _ : J => V)
  let C : Finset (ι → ℕ) := Fintype.piFinset
    (fun _ : ι => (Finset.Icc 1 L).filter (fun n => Squarefree n ∧ Nat.Coprime n W))
  have hroughValue (n : ℕ) (hn : Squarefree n) (hc : Nat.Coprime n W)
      (hbound : n ≤ Q) : n ∈ V := by
    by_cases hn1 : n = 1
    · simp [V, hn1]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by have := hn.ne_zero; omega, hbound⟩, hn, ?_⟩
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hlarge : D₀ < p := by
      by_contra h
      have hpW : p ∣ W :=
        (hpprime.dvd_primorial_iff.mpr (Nat.le_of_not_gt h)).trans hsmall
      exact (hpprime.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpdvd hc)) hpW
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hlarge, (Nat.le_of_dvd hn.ne_zero.bot_lt hpdvd).trans hbound⟩,
        hpprime⟩
  have hTr (u : ι → ℕ) (s : J → ℕ) (hl : y (left u s) ≠ 0) : s ∈ Tr := by
    have hr := hy _ (Finsupp.mem_support_iff.mpr hl)
    apply Fintype.mem_piFinset.mpr
    intro ab
    have hdiv : s ab ∣ ∏ i, left u s i :=
      (hsLower (fun ab : J => ab.1.1) u s ab).trans
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
    exact hroughValue _ (hr.1.squarefree_of_dvd hdiv)
      (Nat.Coprime.of_dvd_left hdiv hr.2.1)
      (((Nat.le_of_dvd hr.1.ne_zero.bot_lt hdiv).trans hr.2.2).trans (Nat.le_succ L))
  have hC (u : ι → ℕ) (s : J → ℕ) (hl : y (left u s) ≠ 0) : u ∈ C := by
    have hr := hy _ (Finsupp.mem_support_iff.mpr hl)
    apply Fintype.mem_piFinset.mpr
    intro i
    have hdiv : u i ∣ ∏ i, left u s i :=
      (huLower (fun ab : J => ab.1.1) u s i).trans
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
    have hsf := hr.1.squarefree_of_dvd hdiv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hsf.ne_zero.bot_lt,
        (Nat.le_of_dvd hr.1.ne_zero.bot_lt hdiv).trans hr.2.2⟩,
        hsf, Nat.Coprime.of_dvd_left hdiv hr.2.1⟩
  have hCE : C ⊆ E := by
    intro u hu
    exact Fintype.mem_piFinset.mpr fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu i)).1
  have hTrT : Tr ⊆ T := by
    intro s hs
    apply Fintype.mem_piFinset.mpr
    intro ab
    have hv := Fintype.mem_piFinset.mp hs ab
    rcases Finset.mem_insert.mp hv with h1 | hn
    · simp [h1, Q]
    · have hq := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      exact Finset.mem_Icc.mpr ⟨by omega, hq.2⟩
  have hrestrict (s : J → ℕ) :
      F s = crossMu s * ∑ u ∈ C, Phi u * S (left u s) * S (right u s) := by
    dsimp only [F]
    congr 1
    symm
    apply Finset.sum_subset hCE
    intro u hu hnot
    have hl : y (left u s) = 0 := by
      by_contra h
      exact hnot (hC u s h)
    simp [hS, hl]
  have hrough : (∑ s ∈ T.erase ones, F s) = ∑ s ∈ Tr.erase ones, F s := by
    symm
    apply Finset.sum_subset
      (fun s hs => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hs).1,
        hTrT (Finset.mem_erase.mp hs).2⟩)
    intro s hs hnot
    have hsnot : s ∉ Tr := fun h => hnot (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hs).1, h⟩)
    have hl (u : ι → ℕ) : y (left u s) = 0 := by
      by_contra h
      exact hsnot (hTr u s h)
    simp [F, hS, hl]
  have hB0 : 0 ≤ B := (abs_nonneg (y (fun _ => 0))).trans (hB _)
  have hPhi0 (r : ι → ℕ) : 0 ≤ Phi r := by dsimp [Phi]; positivity
  have hmu (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hSbound (r : ι → ℕ) : |S r| ≤ B / Phi r := by
    rw [hS, abs_div, abs_of_nonneg (hPhi0 r), abs_mul]
    apply div_le_div_of_nonneg_right _ (hPhi0 r)
    exact (mul_le_mul_of_nonneg_right (hmu _) (abs_nonneg _)).trans (by simpa using hB r)
  have hcrossMu (s : J → ℕ) : |crossMu s| ≤ 1 := by
    dsimp only [crossMu]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun ab _ => hmu (s ab))
  have hPhiPos (u : ι → ℕ) (hu : u ∈ C) : 0 < Phi u := by
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast Nat.totient_pos.mpr (hcoordE u (hCE hu) i).1
  have hPsiPos (s : J → ℕ) (hs : s ∈ Tr) : 0 < Psi s := by
    apply Finset.prod_pos
    intro ab hab
    exact_mod_cast Nat.totient_pos.mpr
      (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (hTrT hs) ab)).1
  have hmajor (u : ι → ℕ) (hu : u ∈ C) (s : J → ℕ) (hs : s ∈ Tr) :
      |Phi u * S (left u s) * S (right u s)| ≤ B ^ 2 / (Phi u * Psi s ^ 2) := by
    by_cases hl : y (left u s) = 0
    · simp only [hS, hl, mul_zero, zero_div, zero_mul, abs_zero]
      exact div_nonneg (sq_nonneg B) (mul_nonneg (hPhi0 u) (sq_nonneg _))
    by_cases hr : y (right u s) = 0
    · simp only [hS, hr, mul_zero, zero_div, abs_zero]
      exact div_nonneg (sq_nonneg B) (mul_nonneg (hPhi0 u) (sq_nonneg _))
    have hst := hstar u s hl hr
    have hleft : Phi (left u s) = Phi u * Psi s :=
      hfactor (fun ab : J => ab.1.1) u s (fun ab => (hst.1 ab).1)
        (fun ab cd hne h => hst.2 ab cd hne (Or.inl h))
    have hright : Phi (right u s) = Phi u * Psi s :=
      hfactor (fun ab : J => ab.1.2) u s (fun ab => (hst.1 ab).2)
        (fun ab cd hne h => hst.2 ab cd hne (Or.inr h))
    calc
      _ = Phi u * |S (left u s)| * |S (right u s)| := by
        rw [abs_mul, abs_mul, abs_of_pos (hPhiPos u hu)]
      _ ≤ Phi u * (B / Phi (left u s)) * (B / Phi (right u s)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hSbound _) (hPhi0 u)) (hSbound _)
          (abs_nonneg _) (mul_nonneg (hPhi0 u) (div_nonneg hB0 (hPhi0 _)))
      _ = _ := by
        rw [hleft, hright]
        field_simp [(hPhiPos u hu).ne', (hPsiPos s hs).ne']
  have hFbound (s : J → ℕ) (hs : s ∈ Tr) :
      |F s| ≤ B ^ 2 * (1 / Psi s ^ 2) * (∑ u ∈ C, 1 / Phi u) := by
    rw [hrestrict, Finset.mul_sum]
    calc
      _ ≤ ∑ u ∈ C, |crossMu s * (Phi u * S (left u s) * S (right u s))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ C, B ^ 2 / (Phi u * Psi s ^ 2) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [abs_mul]
        exact (mul_le_mul (hcrossMu s) (hmajor u hu s hs)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        simp only [div_eq_mul_inv, mul_inv]
        ring
  have hcommonMean : (∑ u ∈ C, 1 / Phi u) = M ^ k := by
    calc
      _ = ∑ u ∈ C, ∏ i, 1 / ((u i).totient : ℝ) := by
        simp only [Phi, one_div, Finset.prod_inv_distrib]
      _ = ∏ _i : ι, ∑ n ∈ (Finset.Icc 1 L).filter
          (fun n => Squarefree n ∧ Nat.Coprime n W), 1 / (n.totient : ℝ) :=
        (Finset.prod_univ_sum
          (fun _ : ι => (Finset.Icc 1 L).filter (fun n => Squarefree n ∧ Nat.Coprime n W))
          (fun (_ : ι) n => 1 / (n.totient : ℝ))).symm
      _ = _ := by simp [Finset.sum_filter, M, k]
  let w (n : ℕ) : ℝ := 1 / (n.totient : ℝ) ^ 2
  let U : ℝ := ∑ n ∈ V, w n
  let Ap : ℝ := ∑ p ∈ P, w p
  let Euler : ℝ := ∏ p ∈ P, (1 + w p)
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have honeV : 1 ∈ V := by simp [V]
  have hVdata (n : ℕ) (hn : n ∈ V) : Squarefree n ∧ n.primeFactors ⊆ P := by
    rcases Finset.mem_insert.mp hn with h1 | hn
    · simp [h1]
    · exact (Finset.mem_filter.mp hn).2
  have hweight (n : ℕ) (hn : Squarefree n) : w n = ∏ p ∈ n.primeFactors, w p := by
    have htot : n.totient = ∏ p ∈ n.primeFactors, p.totient := by
      rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hn,
        Nat.div_self hn.ne_zero.bot_lt, one_mul]
      apply Finset.prod_congr rfl
      intro p hp
      exact (Nat.totient_prime (Nat.prime_of_mem_primeFactors hp)).symm
    dsimp only [w]
    rw [htot, Nat.cast_prod, ← Finset.prod_pow]
    simp only [one_div, Finset.prod_inv_distrib]
  have hUone : 1 ≤ U := by
    simpa [U, w] using Finset.single_le_sum (fun n _ => hw n) honeV
  have hUEuler : U ≤ Euler := by
    have hinj : Set.InjOn Nat.primeFactors (V : Set ℕ) :=
      Nat.prod_primeFactors_invOn_squarefree.2.injOn.mono (fun n hn => (hVdata n hn).1)
    calc
      _ = ∑ n ∈ V, ∏ p ∈ n.primeFactors, w p :=
        Finset.sum_congr rfl (fun n hn => hweight n (hVdata n hn).1)
      _ = ∑ t ∈ V.image Nat.primeFactors, ∏ p ∈ t, w p :=
        (Finset.sum_image (f := fun t : Finset ℕ => ∏ p ∈ t, w p) hinj).symm
      _ ≤ ∑ t ∈ P.powerset, ∏ p ∈ t, w p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
          exact Finset.mem_powerset.mpr (hVdata n hn).2
        · intro t ht hnot
          exact Finset.prod_nonneg (fun p _ => hw p)
      _ = Euler := (Finset.prod_one_add _).symm
  have hprimeWeight (p : ℕ) (hp : p.Prime) : w p ≤ 4 * ((p : ℝ) ^ 2)⁻¹ := by
    dsimp only [w]
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by positivity
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hp0)).mpr
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hD0R : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  have hAp : Ap ≤ 8 / (D₀ : ℝ) := by
    have hPsub : P ⊆ Finset.Ioo D₀ (Q + 1) := by
      intro p hp
      have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_Ioo.mpr ⟨hi.1, by omega⟩
    calc
      _ ≤ ∑ p ∈ P, 4 * ((p : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun p hp => hprimeWeight p (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p ∈ Finset.Ioo D₀ (Q + 1), 4 * ((p : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun p _ _ => by positivity)
      _ = 4 * ∑ p ∈ Finset.Ioo D₀ (Q + 1), ((p : ℝ) ^ 2)⁻¹ :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * (2 / ((D₀ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) D₀ (Q + 1)) (by norm_num)
      _ = 8 / ((D₀ : ℝ) + 1) := by ring
      _ ≤ 8 / (D₀ : ℝ) := div_le_div_of_nonneg_left (by norm_num) hD0R (by linarith)
  have hAp8 : Ap ≤ 8 := by
    apply hAp.trans
    exact (div_le_self (by norm_num : (0 : ℝ) ≤ 8) (by exact_mod_cast hD₀))
  have hEuler : Euler ≤ Real.exp 8 :=
    (Real.prod_one_add_le_exp_sum P hw).trans (Real.exp_le_exp.mpr hAp8)
  have hEulerDiff : Euler - 1 ≤ Ap * Euler := by
    dsimp only [Euler, Ap]
    nth_rw 1 [Finset.prod_one_add_ordered]
    simp only [add_sub_cancel_left]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (hw p)
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
    · intro q hq
      exact add_nonneg zero_le_one (hw q)
    · intro q hq hnot
      exact le_add_of_nonneg_right (hw q)
  have hUexp : U ≤ Real.exp 8 := hUEuler.trans hEuler
  have hUtail : U - 1 ≤ 8 * Real.exp 8 / (D₀ : ℝ) := by
    calc
      _ ≤ Euler - 1 := sub_le_sub_right hUEuler _
      _ ≤ Ap * Euler := hEulerDiff
      _ ≤ (8 / (D₀ : ℝ)) * Real.exp 8 :=
        mul_le_mul hAp hEuler (Finset.prod_nonneg (fun p _ => add_nonneg zero_le_one (hw p)))
          (div_nonneg (by norm_num) hD0R.le)
      _ = _ := by ring
  have hcardJ : Fintype.card J = K := by
    simp only [J, Fintype.card_coe, Finset.offDiag_card, Finset.card_univ]
    simp [K, k, Nat.mul_sub_left_distrib]
  have htupleMass : (∑ s ∈ Tr, 1 / Psi s ^ 2) = U ^ K := by
    calc
      _ = ∑ s ∈ Tr, ∏ ab : J, w (s ab) := by
        simp only [Psi, w, one_div, Finset.prod_inv_distrib, Finset.prod_pow]
      _ = ∏ _ab : J, U :=
        (Finset.prod_univ_sum (fun _ : J => V) (fun (_ : J) n => w n)).symm
      _ = U ^ K := by simp only [Finset.prod_const, Finset.card_univ, hcardJ]
  have honeTr : ones ∈ Tr := Fintype.mem_piFinset.mpr (fun _ => honeV)
  have heraseMass : (∑ s ∈ Tr.erase ones, 1 / Psi s ^ 2) = U ^ K - 1 := by
    rw [Finset.sum_erase_eq_sub honeTr, htupleMass]
    simp [Psi, ones]
  have htupleTail : (∑ s ∈ Tr.erase ones, 1 / Psi s ^ 2) ≤
      (8 * Real.exp 8 / (D₀ : ℝ)) * (K : ℝ) * (Real.exp 8) ^ (K - 1) := by
    rw [heraseMass]
    have hU0 : 0 ≤ U := zero_le_one.trans hUone
    have hpow := abs_pow_sub_pow_le (a := U) (b := (1 : ℝ)) (n := K)
    have hUpow : 1 ≤ U ^ K := one_le_pow₀ hUone
    norm_num only [one_pow] at hpow
    rw [abs_of_nonneg (sub_nonneg.mpr hUpow),
      abs_of_nonneg (sub_nonneg.mpr hUone), abs_of_nonneg hU0,
      max_eq_left hUone] at hpow
    exact hpow.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hUtail (Nat.cast_nonneg K))
      (pow_le_pow_left₀ hU0 hUexp (K - 1)) (pow_nonneg hU0 _)
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hD0R.le)
        (Nat.cast_nonneg K)))
  change |∑ d ∈ D, ∑ e ∈ D,
    if ¬ (∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) then theta d e else 0| ≤ _
  rw [hbadD, abs_neg, hrough]
  calc
    _ ≤ ∑ s ∈ Tr.erase ones, |F s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Tr.erase ones,
        B ^ 2 * (1 / Psi s ^ 2) * (∑ u ∈ C, 1 / Phi u) :=
      Finset.sum_le_sum (fun s hs => hFbound s (Finset.mem_of_mem_erase hs))
    _ = B ^ 2 * (∑ s ∈ Tr.erase ones, 1 / Psi s ^ 2) * (∑ u ∈ C, 1 / Phi u) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ B ^ 2 *
        ((8 * Real.exp 8 / (D₀ : ℝ)) * (K : ℝ) * (Real.exp 8) ^ (K - 1)) *
          (∑ u ∈ C, 1 / Phi u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htupleTail (sq_nonneg B))
        (Finset.sum_nonneg (fun u _ => div_nonneg zero_le_one (hPhi0 u)))
    _ = _ := by rw [hcommonMean]

open Classical in
theorem selberg_square_real_interval_two_error
    {ι : Type*} [Fintype ι] (h : ι → ℕ) (hinj : Function.Injective h)
    (y : (ι → ℕ) →₀ ℝ) (L W v D₀ : ℕ) (B : ℝ)
    (hW : 0 < W) (hD₀ : 0 < D₀)
    (hsmall : _root_.primorial D₀ ∣ W)
    (hy : ∀ r ∈ y.support,
      Squarefree (∏ i, r i) ∧
        Nat.Coprime (∏ i, r i) W ∧ (∏ i, r i) ≤ L)
    (hB : ∀ r, |y r| ≤ B)
    (hcover : ∀ a b : ι, h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (x : ℝ) (hx : 0 ≤ x) :
    let D := y.support.biUnion
      (fun r => Fintype.piFinset (fun i => (r i).divisors))
    let k := Fintype.card ι
    let K := k * (k - 1)
    let M : ℝ := ∑ n ∈ Finset.Icc 1 L,
      if Squarefree n ∧ Nat.Coprime n W then 1 / (n.totient : ℝ) else 0
    |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq W n v then
          (∑ d ∈ D, if ∀ i, d i ∣ n + h i then selbergCoefficient y d else 0) ^ 2
        else 0) -
      x / (W : ℝ) *
        y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ)))| ≤
      2 * (∑ d ∈ D, |selbergCoefficient y d|) ^ 2 +
        x / (W : ℝ) *
          (B ^ 2 *
            ((8 * Real.exp 8 / (D₀ : ℝ)) * (K : ℝ) *
              (Real.exp 8) ^ (K - 1)) * M ^ k) := by
  intro D k K M
  let Nsum : ℝ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if Nat.ModEq W n v then
      (∑ d ∈ D, if ∀ i, d i ∣ n + h i then selbergCoefficient y d else 0) ^ 2
    else 0
  let theta (d e : ι → ℕ) : ℝ :=
    selbergCoefficient y d * selbergCoefficient y e /
      (∏ i, (Nat.lcm (d i) (e i) : ℝ))
  let Qall : ℝ := ∑ d ∈ D, ∑ e ∈ D, theta d e
  let Qgood : ℝ := ∑ d ∈ D, ∑ e ∈ D,
    if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then theta d e else 0
  let Qbad : ℝ := ∑ d ∈ D, ∑ e ∈ D,
    if ¬ (∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b)) then theta d e else 0
  let Cabs : ℝ := ∑ d ∈ D, ∑ e ∈ D,
    if ∀ a b : ι, a ≠ b → Nat.Coprime (d a) (e b) then
      |selbergCoefficient y d * selbergCoefficient y e| else 0
  let error : ℝ := B ^ 2 *
    ((8 * Real.exp 8 / (D₀ : ℝ)) * (K : ℝ) * (Real.exp 8) ^ (K - 1)) * M ^ k
  have hD (d : ι → ℕ) (hd : d ∈ D) :
      Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    have hdiv : (∏ i, d i) ∣ ∏ i, r i :=
      Finset.prod_dvd_prod_of_dvd d r fun i _ =>
        Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr i)
    exact ⟨(hy r hr).1.squarefree_of_dvd hdiv,
      Nat.Coprime.of_dvd_left hdiv (hy r hr).2.1⟩
  have hcrt := selberg_square_real_interval_crt h hinj D (selbergCoefficient y)
    W v hW hD hcover x hx
  change |Nsum - x / (W : ℝ) * Qgood| ≤ 2 * Cabs at hcrt
  have hdiagonal := selberg_unrestricted_lcm_diagonal y (fun r hr => (hy r hr).1)
  change Qall = y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ))) at hdiagonal
  have hcross := selberg_cross_correction_le y L W D₀ B hD₀ hsmall hy hB
  change |Qbad| ≤ error at hcross
  have hpartition : Qall = Qgood + Qbad := by
    dsimp only [Qall, Qgood, Qbad]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_filter, Finset.sum_filter_add_sum_filter_not]
  have hCabs : Cabs ≤ (∑ d ∈ D, |selbergCoefficient y d|) ^ 2 := by
    calc
      _ ≤ ∑ d ∈ D, ∑ e ∈ D, |selbergCoefficient y d * selbergCoefficient y e| := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        split_ifs
        · exact le_rfl
        · exact abs_nonneg _
      _ = _ := by
        rw [pow_two, Finset.sum_mul_sum]
        simp only [abs_mul]
  have hxW : 0 ≤ x / (W : ℝ) := div_nonneg hx (Nat.cast_nonneg W)
  change |Nsum - x / (W : ℝ) *
    y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ)))| ≤
      2 * (∑ d ∈ D, |selbergCoefficient y d|) ^ 2 + x / (W : ℝ) * error
  rw [← hdiagonal]
  calc
    _ = |(Nsum - x / (W : ℝ) * Qgood) - x / (W : ℝ) * Qbad| :=
      congrArg abs (by rw [hpartition]; ring)
    _ ≤ |Nsum - x / (W : ℝ) * Qgood| + |x / (W : ℝ) * Qbad| := by
      simpa using abs_sub_le (Nsum - x / (W : ℝ) * Qgood) 0 (x / (W : ℝ) * Qbad)
    _ ≤ 2 * Cabs + x / (W : ℝ) * error :=
      add_le_add hcrt (by
        rw [abs_mul, abs_of_nonneg hxW]
        exact mul_le_mul_of_nonneg_left hcross hxW)
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hCabs (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl

theorem presieving_le_mul_log_eventually
    (H : Finset ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      (presievingModulus H x : ℝ) ≤ c * Real.log x := by
  classical
  let P : Finset ℕ :=
    H.biUnion (fun h => H.biUnion (fun k => (Nat.dist h k).primeFactors))
  have hP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    obtain ⟨h, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k, _, hp⟩ := Finset.mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hp
  have hlog2 : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlog3 : Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x)))
      atTop atTop := Real.tendsto_log_atTop.comp hlog2
  have hsub : ∀ᶠ x : ℝ in atTop,
      P ⊆ Nat.primesLE ⌊Real.log (Real.log (Real.log x))⌋₊ := by
    apply (Filter.eventually_all_finset P).mpr
    intro p hp
    filter_upwards [hlog3.eventually_ge_atTop (p : ℝ)] with x hx
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff' (hP p hp).ne_zero).mpr hx, hP p hp⟩
  have hsmall : ∀ᶠ x : ℝ in atTop,
      ‖Real.log (Real.log x) ^ Real.log 4‖ ≤
        c * ‖Real.log x ^ (1 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_rpow_atTop (Real.log 4)
        (show (0 : ℝ) < 1 by norm_num)).bound hc)
  filter_upwards [hsub, hsmall,
    Real.tendsto_log_atTop.eventually_gt_atTop 0,
    hlog2.eventually_gt_atTop 0, hlog3.eventually_ge_atTop 0]
    with x hxsub hxsmall hl hll hlll
  have hW : presievingModulus H x =
      primorial ⌊Real.log (Real.log (Real.log x))⌋₊ := by
    change (∏ p ∈ Nat.primesLE ⌊Real.log (Real.log (Real.log x))⌋₊ ∪ P, p) = _
    rw [Finset.union_eq_left.mpr hxsub, primorial_eq_prod_primesLE]
  calc
    (presievingModulus H x : ℝ) ≤
        (4 : ℝ) ^ ⌊Real.log (Real.log (Real.log x))⌋₊ := by
      rw [hW]
      exact_mod_cast primorial_le_four_pow ⌊Real.log (Real.log (Real.log x))⌋₊
    _ = (4 : ℝ) ^ ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ (4 : ℝ) ^ Real.log (Real.log (Real.log x)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlll)
    _ = Real.log (Real.log x) ^ Real.log 4 := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < 4 by norm_num),
        Real.rpow_def_of_pos hll]
      congr 1
      ring
    _ ≤ c * Real.log x := by
      simpa only [Real.rpow_one,
        Real.norm_of_nonneg (Real.rpow_nonneg hll.le _),
        Real.norm_of_nonneg hl.le] using hxsmall

theorem floor_rpow_log_envelope (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ ⌊x ^ a⌋₊ ∧
      0 ≤ 1 + Real.log (⌊x ^ a⌋₊ : ℝ) ∧
      1 + Real.log (⌊x ^ a⌋₊ : ℝ) ≤ Real.log x := by
  filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / (1 - a)),
    eventually_gt_atTop (0 : ℝ)] with x hpow hlarge hx
  have hL : 1 ≤ ⌊x ^ a⌋₊ := (Nat.one_le_floor_iff _).mpr hpow
  have hLreal : (1 : ℝ) ≤ (⌊x ^ a⌋₊ : ℝ) := by exact_mod_cast hL
  have hlog0 : 0 ≤ Real.log (⌊x ^ a⌋₊ : ℝ) := Real.log_nonneg hLreal
  have hlog : Real.log (⌊x ^ a⌋₊ : ℝ) ≤ a * Real.log x := by
    calc
      _ ≤ Real.log (x ^ a) :=
        Real.log_le_log (zero_lt_one.trans_le hLreal)
          (Nat.floor_le (Real.rpow_nonneg hx.le a))
      _ = _ := Real.log_rpow hx a
  have hlarge' := (div_le_iff₀ (sub_pos.mpr ha1)).mp hlarge
  refine ⟨hL, add_nonneg zero_le_one hlog0, ?_⟩
  nlinarith

theorem primorial_dvd_presieving (H : Finset ℕ) (x : ℝ) :
    _root_.primorial ⌊Real.log (Real.log (Real.log x))⌋₊ ∣
      presievingModulus H x := by
  classical
  rw [primorial_eq_prod_primesLE, presievingModulus]
  exact Finset.prod_dvd_prod_of_subset _ _ id Finset.subset_union_left

theorem finite_mean_le_fragment_mass (W : ℕ) (R ζ : ℝ)
    (hcap : 1 ≤ R ^ ζ) :
    (∑ n ∈ Finset.Icc 1 ⌊R ^ ζ⌋₊,
      if Squarefree n ∧ Nat.Coprime n W then 1 / (n.totient : ℝ) else 0) ≤
      harmonicFragmentMass W R ζ := by
  classical
  rw [← Finset.sum_filter]
  unfold harmonicFragmentMass
  simp only [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hn, hsq, hcop⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnL⟩ := Finset.mem_Icc.mp hn
    apply (mem_fragment_divisors_iff W R ζ hcap n).mpr
    refine ⟨hsq, hcop, ?_⟩
    have hs : n.primeFactors.sup id ≤ n := by
      apply Finset.sup_le_iff.mpr
      intro p hp
      exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    have hnR : (n : ℝ) ≤ R ^ ζ :=
      (Nat.cast_le.mpr hnL).trans (Nat.floor_le (zero_le_one.trans hcap))
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hcap ((Nat.cast_le.mpr hs).trans hnR)
  · intro n _ _
    positivity

theorem normalized_square_le (M B L Q x W : ℝ)
    (hB : 1 ≤ B) (hx : 0 < x) (hW : 0 < W) :
    2 * (M / B ^ 39 * L * Q) ^ 2 / (x / W / B ^ 39) ≤
      2 * M ^ 2 * W * L ^ 2 * Q ^ 2 / x := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have heq :
      2 * (M / B ^ 39 * L * Q) ^ 2 / (x / W / B ^ 39) =
        (2 * M ^ 2 * W * L ^ 2 * Q ^ 2 / x) / B ^ 39 := by
    field_simp [hB0.ne', hx.ne', hW.ne']
  rw [heq]
  exact div_le_self (by positivity) (one_le_pow₀ hB)

theorem normalized_cross_eq (M B F C D x W : ℝ) (k : ℕ)
    (hB : 0 < B) (hD : 0 < D) (hx : 0 < x) (hW : 0 < W) :
    (x / W * ((M / B ^ k) ^ 2 * (C / D) * F ^ k)) /
        (x / W / B ^ k) = M ^ 2 * C * (F / B) ^ k / D := by
  simp only [div_pow]
  field_simp [hB.ne', hD.ne', hx.ne', hW.ne']

theorem crt_power_identity (M x a : ℝ) (J : ℕ) (hx : 0 < x) :
    2 * M ^ 2 * Real.log x * (x ^ a) ^ 2 * (Real.log x ^ J) ^ 2 / x =
      2 * M ^ 2 * Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a) := by
  have hp : (x ^ a) ^ 2 / x = 1 / x ^ (1 - 2 * a) := by
    calc
      (x ^ a) ^ 2 / x = x ^ (a * 2) / x ^ (1 : ℝ) := by
        rw [Real.rpow_mul hx.le, Real.rpow_two, Real.rpow_one]
      _ = x ^ (a * 2 - 1) := (Real.rpow_sub hx _ _).symm
      _ = x ^ (-(1 - 2 * a)) := by congr 1; ring
      _ = 1 / x ^ (1 - 2 * a) := by rw [Real.rpow_neg hx.le, one_div]
  have hq : Real.log x * (Real.log x ^ J) ^ 2 = Real.log x ^ (2 * J + 1) := by
    rw [← pow_mul, Nat.mul_comm J 2, pow_succ']
  calc
    _ = 2 * M ^ 2 * (Real.log x * (Real.log x ^ J) ^ 2) *
        ((x ^ a) ^ 2 / x) := by ring
    _ = _ := by rw [hp, hq]; ring

open Classical in
theorem selberg39_uniform_real_diagonal
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (M : ℝ) (hM : 0 ≤ M) :
    let ρ : ℝ := 2624989 / 10000000
    let S : ℝ := 2742997 / 2624989
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop,
        let W := presievingModulus 𝓗 x
        let R := x ^ ρ
        let B := fragmentNormalization W R
        ∀ (y : (Fin 39 → ℕ) →₀ ℝ) (v : ℕ),
          (∀ r ∈ y.support,
            Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W ∧
              ((∏ i, r i : ℕ) : ℝ) ≤ R ^ S) →
          (∀ r, |y r| ≤ M / B ^ 39) →
          let D := y.support.biUnion
            (fun r => Fintype.piFinset (fun i => (r i).divisors))
          |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
              if Nat.ModEq W n v then
                (∑ d ∈ D, if ∀ i, d i ∣ n + h i then
                  selbergCoefficient y d else 0) ^ 2 else 0) -
            x / (W : ℝ) *
              y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ)))| ≤
            ε * (x / (W : ℝ) / B ^ 39) := by
  intro ρ S h ε hε
  let a : ℝ := 2742997 / 10000000
  let J : ℕ := 2 ^ (39 + 2) - 1
  let C : ℝ := 8 * Real.exp 8 * 1482 * (Real.exp 8) ^ 1481
  let d₀ : ℝ → ℕ := fun x => ⌊Real.log (Real.log (Real.log x))⌋₊
  have hρ : 0 < ρ := by norm_num [ρ]
  have hS : 0 < S := by norm_num [S]
  have ha : 0 < a := by norm_num [a]
  have ha1 : a < 1 := by norm_num [a]
  have hδ : 0 < 1 - 2 * a := by norm_num [a]
  have hM2 : 0 ≤ M ^ 2 := by simpa only [pow_two] using mul_nonneg hM hM
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hε2 : 0 < ε / 2 := half_pos hε
  have hDnat : Tendsto d₀ atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))
  have hDreal : Tendsto (fun x => (d₀ x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDnat
  have hmass := harmonic_fragment_normalizer_tendsto 𝓗 ρ S hρ hS
  have hcrossLimit : Tendsto
      (fun x : ℝ => M ^ 2 * C *
        (harmonicFragmentMass (presievingModulus 𝓗 x) (x ^ ρ) S /
          fragmentNormalization (presievingModulus 𝓗 x) (x ^ ρ)) ^ 39 /
            (d₀ x : ℝ)) atTop (nhds 0) :=
    ((hmass.pow 39).const_mul (M ^ 2 * C)).div_atTop hDreal
  have hlogLimit : Tendsto
      (fun x : ℝ => Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a))
      atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((2 * J + 1 : ℕ) : ℝ) hδ).tendsto_div_nhds_zero
  have hcrtLimit : Tendsto
      (fun x : ℝ => 2 * M ^ 2 * Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a))
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using hlogLimit.const_mul (2 * M ^ 2)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    presieving_le_mul_log_eventually 𝓗 ρ hρ,
    presieving_le_mul_log_eventually 𝓗 1 zero_lt_one,
    floor_rpow_log_envelope a ha ha1, hDnat.eventually_gt_atTop 0,
    hcrtLimit.eventually_le_const hε2, hcrossLimit.eventually_le_const hε2]
    with x hx hWρ hWlog hfloor hD₀ hcrt hcross
  intro W R B
  let D₀ : ℕ := d₀ x
  let L : ℕ := ⌊R ^ S⌋₊
  let Q : ℝ := (1 + Real.log (L : ℝ)) ^ J
  let F : ℝ := ∑ n ∈ Finset.Icc 1 L,
    if Squarefree n ∧ Nat.Coprime n W then 1 / (n.totient : ℝ) else 0
  let T : ℝ := harmonicFragmentMass W R S
  let A : ℝ := x / (W : ℝ) / B ^ 39
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hW : 0 < W := presieving_pos 𝓗 x
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hD₀R : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  have hcapEq : R ^ S = x ^ a := by
    change (x ^ ρ) ^ S = x ^ a
    rw [← Real.rpow_mul hx0.le]
    congr 1
    norm_num [ρ, S, a]
  have hcap : 1 ≤ R ^ S := by
    rw [hcapEq]
    exact (Nat.one_le_floor_iff _).mp hfloor.1
  have hLle : (L : ℝ) ≤ x ^ a := by
    dsimp only [L]
    rw [hcapEq]
    exact Nat.floor_le (Real.rpow_nonneg hx0.le a)
  have hlogL0 : 0 ≤ 1 + Real.log (L : ℝ) := by
    simpa only [L, hcapEq] using hfloor.2.1
  have hlogL : 1 + Real.log (L : ℝ) ≤ Real.log x := by
    simpa only [L, hcapEq] using hfloor.2.2
  have hQ0 : 0 ≤ Q := pow_nonneg hlogL0 J
  have hQle : Q ≤ Real.log x ^ J := pow_le_pow_left₀ hlogL0 hlogL J
  have hφ : (1 : ℝ) ≤ (Nat.totient W : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.totient W from Nat.totient_pos.mpr hW)
  have hB1 : 1 ≤ B := by
    change 1 ≤ ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log (x ^ ρ)
    rw [Real.log_rpow hx0, div_mul_eq_mul_div]
    exact (one_le_div hWR).mpr
      (hWρ.trans (le_mul_of_one_le_left (mul_nonneg hρ.le hlog) hφ))
  have hB : 0 < B := zero_lt_one.trans_le hB1
  have hA : 0 < A := div_pos (div_pos hx0 hWR) (pow_pos hB 39)
  have hWlog' : (W : ℝ) ≤ Real.log x := by simpa only [one_mul] using hWlog
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact Finset.sum_nonneg fun n _ =>
      ite_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg n.totient)) le_rfl
  have hFT : F ≤ T := finite_mean_le_fragment_mass W R S hcap
  have hCeq :
      (8 * Real.exp 8 / (D₀ : ℝ)) * 1482 * (Real.exp 8) ^ 1481 = C / (D₀ : ℝ) := by
    dsimp only [C]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  have hinj : Function.Injective h :=
    (𝓗.orderEmbOfFin h𝓗_card).injective
  have hcover : ∀ i j : Fin 39, h i ≠ h j → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h i) (h j) → p ∣ W := by
    intro i j hij p hp hpd
    exact difference_prime_dvd_presieving 𝓗 x
      (𝓗.orderEmbOfFin_mem h𝓗_card i)
      (𝓗.orderEmbOfFin_mem h𝓗_card j) hij hp hpd
  intro y v hy hbound D
  have hD (e : DecidableEq (Fin 39)) :
      y.support.biUnion (fun r => @Fintype.piFinset (Fin 39) e inferInstance
        (fun _ => ℕ) (fun i => (r i).divisors)) = D := by
    ext d
    simp only [D, Finset.mem_biUnion, Fintype.mem_piFinset]
  have hyL : ∀ r ∈ y.support,
      Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W ∧ (∏ i, r i) ≤ L := by
    intro r hr
    exact ⟨(hy r hr).1, (hy r hr).2.1,
      (Nat.le_floor_iff (zero_le_one.trans hcap)).mpr (hy r hr).2.2⟩
  have hl1 := selbergCoefficient_l1_le y L (M / B ^ 39)
    (fun r hr => ⟨(hyL r hr).1, (hyL r hr).2.2⟩) hbound
  simp only [hD, Fintype.card_fin] at hl1
  change (∑ d ∈ D, |selbergCoefficient y d|) ≤ M / B ^ 39 * (L : ℝ) * Q at hl1
  have hsum0 : 0 ≤ ∑ d ∈ D, |selbergCoefficient y d| :=
    Finset.sum_nonneg fun d _ => abs_nonneg _
  have hprod₁ :
      2 * M ^ 2 * (W : ℝ) * (L : ℝ) ^ 2 ≤
        2 * M ^ 2 * Real.log x * (x ^ a) ^ 2 :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left hWlog' (mul_nonneg (by norm_num) hM2))
      (pow_le_pow_left₀ (Nat.cast_nonneg L) hLle 2)
      (sq_nonneg (L : ℝ)) (mul_nonneg (mul_nonneg (by norm_num) hM2) hlog)
  have hprod₂ :
      2 * M ^ 2 * (W : ℝ) * (L : ℝ) ^ 2 * Q ^ 2 ≤
        2 * M ^ 2 * Real.log x * (x ^ a) ^ 2 * (Real.log x ^ J) ^ 2 :=
    mul_le_mul hprod₁ (pow_le_pow_left₀ hQ0 hQle 2) (sq_nonneg Q)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM2) hlog) (sq_nonneg _))
  have hcrtNorm :
      2 * (∑ d ∈ D, |selbergCoefficient y d|) ^ 2 / A ≤
        2 * M ^ 2 * Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a) := by
    calc
      _ ≤ 2 * (M / B ^ 39 * (L : ℝ) * Q) ^ 2 / A :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hl1 2) (by norm_num)) hA.le
      _ ≤ 2 * M ^ 2 * (W : ℝ) * (L : ℝ) ^ 2 * Q ^ 2 / x :=
        normalized_square_le M B (L : ℝ) Q x (W : ℝ) hB1 hx0 hWR
      _ ≤ 2 * M ^ 2 * Real.log x * (x ^ a) ^ 2 * (Real.log x ^ J) ^ 2 / x :=
        div_le_div_of_nonneg_right hprod₂ hx0.le
      _ = _ := crt_power_identity M x a J hx0
  have hcrossNorm :
      (x / (W : ℝ) * ((M / B ^ 39) ^ 2 * (C / (D₀ : ℝ)) * F ^ 39)) / A ≤
        M ^ 2 * C * (T / B) ^ 39 / (D₀ : ℝ) := by
    calc
      _ = M ^ 2 * C * (F / B) ^ 39 / (D₀ : ℝ) :=
        normalized_cross_eq M B F C (D₀ : ℝ) x (W : ℝ) 39 hB hD₀R hx0 hWR
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg hF0 hB.le)
            (div_le_div_of_nonneg_right hFT hB.le) 39) (mul_nonneg hM2 hC)) hD₀R.le
  have hite (n : ℕ) (d : Fin 39 → ℕ) :
      @ite ℝ (∀ i, d i ∣ n + h i) Fintype.decidableForallFintype
        (selbergCoefficient y d) 0 =
          if ∀ i, d i ∣ n + h i then selbergCoefficient y d else 0 :=
    ite_cond_congr rfl
  have htwo := selberg_square_real_interval_two_error h hinj y L W v D₀ (M / B ^ 39)
    hW hD₀ (primorial_dvd_presieving 𝓗 x) hyL hbound hcover x hx0.le
  simp only [hD, hite, Fintype.card_fin] at htwo
  change _ ≤ 2 * (∑ d ∈ D, |selbergCoefficient y d|) ^ 2 +
    x / (W : ℝ) * ((M / B ^ 39) ^ 2 *
      ((8 * Real.exp 8 / (D₀ : ℝ)) * 1482 * (Real.exp 8) ^ 1481) * F ^ 39) at htwo
  rw [hCeq] at htwo
  exact htwo.trans (by
    calc
      _ ≤ (ε / 2) * A + (ε / 2) * A := add_le_add
        ((div_le_iff₀ hA).mp (hcrtNorm.trans hcrt))
        ((div_le_iff₀ hA).mp (hcrossNorm.trans hcross))
      _ = ε * A := by ring)

end

open Classical in
theorem selbergCoefficient_mem_hereditary
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ)
    (P : (ι → ℕ) → Prop)
    (hP : ∀ d r, (∀ i, d i ∣ r i) → P r → P d)
    (hy : ∀ r ∈ y.support, P r) (d : ι → ℕ)
    (hd : selbergCoefficient y d ≠ 0) : P d := by
  unfold selbergCoefficient at hd
  obtain ⟨r, hr, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero (mul_ne_zero_iff.mp hd).2
  exact hP d r (ite_ne_right_iff.mp hterm).1 (hy r hr)

theorem mixedFace_eq_on_prime
    {k : ℕ} (h : Fin (k + 1) → ℕ) (i : Fin (k + 1))
    (D : Finset (Fin (k + 1) → ℕ)) (lam : (Fin (k + 1) → ℕ) → ℝ)
    (x : ℝ) (n : ℕ) (hn : ⌈x⌉₊ ≤ n) (hp : Nat.Prime (n + h i))
    (hsmall : ∀ d ∈ D, (d i : ℝ) < x + (h i : ℝ)) :
    (∑ d ∈ D, if ∀ j, d j ∣ n + h j then lam d else 0) =
      ∑ d ∈ D.filter (fun d => d i = 1),
        if ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)
        then lam d else 0 := by
  classical
  have hxn : x ≤ (n : ℝ) := Nat.le_of_ceil_le hn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdi : d i = 1
  · have hconditions : (∀ j, d j ∣ n + h j) ↔
        ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j) := by
      rw [Fin.forall_iff_succAbove i]
      simp only [hdi, one_dvd, true_and]
    simp only [hdi, ite_eq_left, hconditions]
  · have hnot : ¬ ∀ j, d j ∣ n + h j := by
      intro hdiv
      rcases (Nat.dvd_prime hp).mp (hdiv i) with hunit | hself
      · exact hdi hunit
      · have hlt : (d i : ℝ) < ((n + h i : ℕ) : ℝ) := by
          push_cast
          exact (hsmall d hd).trans_le (add_le_add hxn le_rfl)
        exact (ne_of_lt hlt) (congrArg (fun m : ℕ => (m : ℝ)) hself)
    simp only [hdi, hnot, ite_false]

theorem mixedPair_compatible
    {k : ℕ} (h : Fin (k + 1) → ℕ) (hinj : Function.Injective h)
    (i : Fin (k + 1)) (d : Fin (k + 1) → ℕ) (e : Fin k → ℕ)
    (W : ℕ) (hdW : Nat.Coprime (∏ j, d j) W)
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (n : ℕ)
    (hnd : ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j))
    (hne : ∀ j : Fin k, e j ∣ n + h (i.succAbove j)) :
    ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b) := by
  intro a b hab
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  have hpa' := dvd_trans hpa (hnd a)
  have hpb' := dvd_trans hpb (hne b)
  have hdist : p ∣ Nat.dist (h (i.succAbove a)) (h (i.succAbove b)) := by
    rw [← Nat.dist_add_add_left n, Nat.dist]
    exact dvd_add (Nat.dvd_sub hpa' hpb') (Nat.dvd_sub hpb' hpa')
  have hneShift : h (i.succAbove a) ≠ h (i.succAbove b) :=
    hinj.ne (Fin.succAbove_right_injective.ne hab)
  have hpW := hcover _ _ hneShift p hp hdist
  have hcoordW := Nat.coprime_fintype_prod_left_iff.mp hdW (i.succAbove a)
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpW hcoordW

theorem mixedFace_sum_expand
    {k : ℕ} (h : Fin (k + 1) → ℕ) (i : Fin (k + 1))
    (D : Finset (Fin (k + 1) → ℕ)) (E : Finset (Fin k → ℕ))
    (lamOuter : (Fin (k + 1) → ℕ) → ℝ) (lamInner : (Fin k → ℕ) → ℝ)
    (W v : ℕ) (I : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ I, if Nat.ModEq W n v then
      f (n + h i) *
        (∑ d ∈ D,
          if ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)
          then lamOuter d else 0) *
        (∑ e ∈ E,
          if ∀ j : Fin k, e j ∣ n + h (i.succAbove j) then lamInner e else 0)
      else 0) =
      ∑ d ∈ D, ∑ e ∈ E, (lamOuter d * lamInner e) *
        ∑ n ∈ I,
          if Nat.ModEq W n v ∧
            (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
            (∀ j : Fin k, e j ∣ n + h (i.succAbove j))
          then f (n + h i) else 0 := by
  classical
  calc
    _ = ∑ n ∈ I, ∑ d ∈ D, ∑ e ∈ E,
        if Nat.ModEq W n v ∧
          (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
          (∀ j : Fin k, e j ∣ n + h (i.succAbove j))
        then f (n + h i) * lamOuter d * lamInner e else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hnv : Nat.ModEq W n v
      · simp only [hnv, ite_true, true_and]
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        by_cases hnd : ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j) <;>
          by_cases hne : ∀ j : Fin k, e j ∣ n + h (i.succAbove j) <;>
          simp [hnd, hne, mul_assoc]
      · simp only [hnv, ite_false, false_and, Finset.sum_const_zero]
    _ = ∑ d ∈ D, ∑ e ∈ E, ∑ n ∈ I,
        if Nat.ModEq W n v ∧
          (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
          (∀ j : Fin k, e j ∣ n + h (i.succAbove j))
        then f (n + h i) * lamOuter d * lamInner e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = _ := by
      simp only [Finset.mul_sum, mul_ite, mul_zero, mul_left_comm, mul_comm]

theorem mixedPair_crt {k : ℕ} (h : Fin (k + 1) → ℕ)
    (hinj : Function.Injective h) (i : Fin (k + 1))
    (d : Fin (k + 1) → ℕ) (e : Fin k → ℕ) (W v : ℕ) (hW : 0 < W)
    (hd : Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W)
    (he : Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W)
    (hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b))
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (hv : Nat.Coprime (v + h i) W) :
    let q := W * ∏ j : Fin k, Nat.lcm (d (i.succAbove j)) (e j)
    ∃ c : ℕ, 0 < q ∧ c < q ∧ Nat.Coprime (c + h i) q ∧
      ∀ n : ℕ, Nat.ModEq q n c ↔ Nat.ModEq W n v ∧
        (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
        (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) := by
  classical
  dsimp only
  have hd0 (j : Fin (k + 1)) : d j ≠ 0 :=
    (hd.1.squarefree_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ j))).ne_zero
  have he0 (j : Fin k) : e j ≠ 0 :=
    (he.1.squarefree_of_dvd (Finset.dvd_prod_of_mem e (Finset.mem_univ j))).ne_zero
  have hdW (j : Fin (k + 1)) : Nat.Coprime (d j) W :=
    Nat.coprime_fintype_prod_left_iff.mp hd.2 j
  have heW (j : Fin k) : Nat.Coprime (e j) W :=
    Nat.coprime_fintype_prod_left_iff.mp he.2 j
  have hneg (m t n : ℕ) (hm : 0 < m) :
      Nat.ModEq m n (m - t % m) ↔ m ∣ n + t := by
    have hres : Nat.ModEq m (m - t % m + t) 0 := by
      have ht := (Nat.mod_modEq t m).add_left (m - t % m)
      rw [Nat.sub_add_cancel (Nat.mod_lt t hm).le] at ht
      exact ht.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl m))
    constructor
    · intro hn
      exact Nat.modEq_zero_iff_dvd.mp ((hn.add_right t).trans hres)
    · intro hn
      exact Nat.ModEq.add_right_cancel' t
        ((Nat.modEq_zero_iff_dvd.mpr hn).trans hres.symm)
  let s : Option (Fin k) → ℕ := fun o =>
    o.elim W (fun j => Nat.lcm (d (i.succAbove j)) (e j))
  let a : Option (Fin k) → ℕ := fun o =>
    o.elim v (fun j =>
      Nat.lcm (d (i.succAbove j)) (e j) -
        h (i.succAbove j) % Nat.lcm (d (i.succAbove j)) (e j))
  let l := (Finset.univ : Finset (Option (Fin k))).toList
  have hpos (j : Fin k) : 0 < Nat.lcm (d (i.succAbove j)) (e j) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hd0 (i.succAbove j)) (he0 j))
  have hWs (j : Fin k) : Nat.Coprime W (s (some j)) := by
    change Nat.Coprime W (Nat.lcm (d (i.succAbove j)) (e j))
    exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul _ _)
      ((hdW (i.succAbove j)).symm.mul_right (heW j).symm)
  have hss (j m : Fin k) (hjm : j ≠ m) :
      Nat.Coprime (s (some j)) (s (some m)) := by
    have hret : i.succAbove j ≠ i.succAbove m :=
      Fin.succAbove_right_injective.ne hjm
    have h₁ : Nat.Coprime (d (i.succAbove j)) (d (i.succAbove m) * e m) :=
      (coprime_of_squarefree_fintype_prod d hd.1 hret).mul_right (hc j m hjm)
    have h₂ : Nat.Coprime (e j) (d (i.succAbove m) * e m) :=
      ((hc m j hjm.symm).symm).mul_right
        (coprime_of_squarefree_fintype_prod e he.1 hjm)
    exact Nat.Coprime.of_dvd (Nat.lcm_dvd_mul _ _) (Nat.lcm_dvd_mul _ _)
      (h₁.mul_left h₂)
  have co : l.Pairwise (fun u z => Nat.Coprime (s u) (s z)) := by
    change ((Finset.univ : Finset (Option (Fin k))).toList).Pairwise _
    refine ((Finset.univ : Finset (Option (Fin k))).nodup_toList).pairwise_of_forall_ne ?_
    intro u hu z hz huz
    cases u with
    | none =>
      cases z with
      | none => exact (huz rfl).elim
      | some j => exact hWs j
    | some j =>
      cases z with
      | none => exact (hWs j).symm
      | some m => exact hss j m (by simpa using huz)
  let c : ℕ := Nat.chineseRemainderOfList a s l co
  have hprod : (l.map s).prod = W * ∏ j : Fin k, Nat.lcm (d (i.succAbove j)) (e j) := by
    simp [l, s]
  have hcrtOption (n : ℕ) :
      Nat.ModEq (W * ∏ j : Fin k, Nat.lcm (d (i.succAbove j)) (e j)) n c ↔
        ∀ o : Option (Fin k), Nat.ModEq (s o) n (a o) := by
    rw [← hprod]
    change Nat.ModEq (l.map s).prod n
      (Nat.chineseRemainderOfList a s l co : ℕ) ↔ _
    constructor
    · intro hn o
      have ho : o ∈ l := by simp [l]
      exact ((Nat.modEq_list_map_prod_iff co).mp hn o ho).trans
        ((Nat.chineseRemainderOfList a s l co).property o ho)
    · intro hn
      exact Nat.chineseRemainderOfList_modEq_unique a s l co (fun o _ => hn o)
  have hclass (n : ℕ) :
      Nat.ModEq (W * ∏ j : Fin k, Nat.lcm (d (i.succAbove j)) (e j)) n c ↔
        Nat.ModEq W n v ∧
          (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
          (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) := by
    rw [hcrtOption]
    constructor
    · intro hn
      refine ⟨hn none, ?_, ?_⟩
      · intro j
        exact (Nat.lcm_dvd_iff.mp ((hneg _ _ _ (hpos j)).mp (hn (some j)))).1
      · intro j
        exact (Nat.lcm_dvd_iff.mp ((hneg _ _ _ (hpos j)).mp (hn (some j)))).2
    · rintro ⟨hn, hdn, hen⟩ o
      cases o with
      | none => exact hn
      | some j =>
        exact (hneg _ _ _ (hpos j)).mpr (Nat.lcm_dvd (hdn j) (hen j))
  have hcclass := (hclass c).mp (Nat.ModEq.refl c)
  have hcW : Nat.Coprime (c + h i) W := by
    rw [Nat.coprime_iff_gcd_eq_one, (hcclass.1.add_right (h i)).gcd_eq]
    exact hv
  have hclcm (j : Fin k) :
      Nat.Coprime (c + h i) (Nat.lcm (d (i.succAbove j)) (e j)) := by
    apply Nat.coprime_of_dvd
    intro p hp hpi hplcm
    have hpj : p ∣ c + h (i.succAbove j) :=
      dvd_trans hplcm (Nat.lcm_dvd (hcclass.2.1 j) (hcclass.2.2 j))
    have hdist : p ∣ Nat.dist (h i) (h (i.succAbove j)) := by
      rw [← Nat.dist_add_add_left c, Nat.dist]
      exact dvd_add (Nat.dvd_sub hpi hpj) (Nat.dvd_sub hpj hpi)
    have hij : h i ≠ h (i.succAbove j) := hinj.ne (Fin.ne_succAbove i j)
    have hpW := hcover i (i.succAbove j) hij p hp hdist
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpi hpW hcW
  have hq : 0 < W * ∏ j : Fin k, Nat.lcm (d (i.succAbove j)) (e j) :=
    Nat.mul_pos hW (Finset.prod_pos fun j _ => hpos j)
  have hlt : c < W * ∏ j : Fin k, Nat.lcm (d (i.succAbove j)) (e j) := by
    rw [← hprod]
    apply Nat.chineseRemainderOfList_lt_prod a s l co
    intro o _
    cases o with
    | none => exact hW.ne'
    | some j => exact (hpos j).ne'
  exact ⟨c, hq, hlt,
    hcW.mul_right (Nat.coprime_fintype_prod_right_iff.mpr hclcm), hclass⟩

open Classical in
theorem selberg_mixed_vonMangoldt_real_interval_crt
    {k : ℕ} (h : Fin (k + 1) → ℕ) (hinj : Function.Injective h)
    (i : Fin (k + 1))
    (D : Finset (Fin (k + 1) → ℕ)) (E : Finset (Fin k → ℕ))
    (lamOuter : (Fin (k + 1) → ℕ) → ℝ)
    (lamInner : (Fin k → ℕ) → ℝ)
    (W v : ℕ) (hW : 0 < W)
    (hD : ∀ d ∈ D,
      Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W)
    (hE : ∀ e ∈ E,
      Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W)
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (hv : Nat.Coprime (v + h i) W)
    (x : ℝ) (_hx : 0 < x)
    (hsmall : ∀ d ∈ D, (d i : ℝ) < x + (h i : ℝ)) :
    let I := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
    let Dface := D.filter (fun d => d i = 1)
    let outerRoot : ℕ → ℝ := fun n =>
      ∑ d ∈ D, if ∀ j, d j ∣ n + h j then lamOuter d else 0
    let faceRoot : ℕ → ℝ := fun n =>
      ∑ d ∈ Dface,
        if ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)
        then lamOuter d else 0
    let innerRoot : ℕ → ℝ := fun n =>
      ∑ e ∈ E, if ∀ j, e j ∣ n + h (i.succAbove j) then lamInner e else 0
    let modulus : (Fin (k + 1) → ℕ) → (Fin k → ℕ) → ℕ := fun d e =>
      W * ∏ j : Fin k, Nat.lcm (d (i.succAbove j)) (e j)
    let mean : ℕ → ℝ := fun q =>
      (∑ n ∈ I,
        if Nat.Coprime (n + h i) q then ArithmeticFunction.vonMangoldt (n + h i)
        else 0) / (q.totient : ℝ)
    let primePowerCorrection : ℝ :=
      ∑ n ∈ I, if Nat.ModEq W n v then
        (ArithmeticFunction.vonMangoldt (n + h i) -
          (if Nat.Prime (n + h i) then Real.log ((n + h i : ℕ) : ℝ) else 0)) *
          (outerRoot n - faceRoot n) * innerRoot n
        else 0
    (∀ n ∈ I, Nat.Prime (n + h i) → outerRoot n = faceRoot n) ∧
      ∃ residue : (Fin (k + 1) → ℕ) → (Fin k → ℕ) → ℕ,
        (∀ d ∈ Dface, ∀ e ∈ E,
          (∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b)) →
          0 < modulus d e ∧ residue d e < modulus d e ∧
            Nat.Coprime (residue d e + h i) (modulus d e) ∧
            ∀ n : ℕ,
              Nat.ModEq (modulus d e) n (residue d e) ↔
                Nat.ModEq W n v ∧
                  (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
                  (∀ j : Fin k, e j ∣ n + h (i.succAbove j))) ∧
        (∑ n ∈ I, if Nat.ModEq W n v then
          ArithmeticFunction.vonMangoldt (n + h i) * outerRoot n * innerRoot n
          else 0) =
          (∑ d ∈ Dface, ∑ e ∈ E,
            if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b)
            then lamOuter d * lamInner e *
              (mean (modulus d e) +
                ((∑ n ∈ I,
                  if Nat.ModEq (modulus d e) (n + h i) (residue d e + h i)
                  then ArithmeticFunction.vonMangoldt (n + h i) else 0) -
                    mean (modulus d e)))
            else 0) + primePowerCorrection := by
  intro I Dface outerRoot faceRoot innerRoot modulus mean primePowerCorrection
  have hprime : ∀ n ∈ I, Nat.Prime (n + h i) → outerRoot n = faceRoot n := by
    intro n hn hp
    exact mixedFace_eq_on_prime h i D lamOuter x n (Finset.mem_Icc.mp hn).1 hp hsmall
  have hpair (d : Fin (k + 1) → ℕ) (hd : d ∈ Dface)
      (e : Fin k → ℕ) (he : e ∈ E)
      (hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b)) :
      ∃ c : ℕ, 0 < modulus d e ∧ c < modulus d e ∧
        Nat.Coprime (c + h i) (modulus d e) ∧
        ∀ n : ℕ, Nat.ModEq (modulus d e) n c ↔
          Nat.ModEq W n v ∧
            (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
            (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) :=
    mixedPair_crt h hinj i d e W v hW (hD d (Finset.mem_filter.mp hd).1)
      (hE e he) hc hcover hv
  let residue : (Fin (k + 1) → ℕ) → (Fin k → ℕ) → ℕ := fun d e =>
    if hd : d ∈ Dface then
      if he : e ∈ E then
        if hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b)
        then Classical.choose (hpair d hd e he hc) else 0
      else 0
    else 0
  have hresidue (d : Fin (k + 1) → ℕ) (hd : d ∈ Dface)
      (e : Fin k → ℕ) (he : e ∈ E)
      (hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b)) :
      0 < modulus d e ∧ residue d e < modulus d e ∧
        Nat.Coprime (residue d e + h i) (modulus d e) ∧
        ∀ n : ℕ, Nat.ModEq (modulus d e) n (residue d e) ↔
          Nat.ModEq W n v ∧
            (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
            (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) := by
    simpa only [residue, dite_eq_left hd, dite_eq_left he, dite_eq_left hc] using
      Classical.choose_spec (hpair d hd e he hc)
  refine ⟨hprime, residue, hresidue, ?_⟩
  have hface :
      (∑ n ∈ I, if Nat.ModEq W n v then
        ArithmeticFunction.vonMangoldt (n + h i) * faceRoot n * innerRoot n
        else 0) =
        ∑ d ∈ Dface, ∑ e ∈ E,
          if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b)
          then lamOuter d * lamInner e *
            (mean (modulus d e) +
              ((∑ n ∈ I,
                if Nat.ModEq (modulus d e) (n + h i) (residue d e + h i)
                then ArithmeticFunction.vonMangoldt (n + h i) else 0) -
                  mean (modulus d e)))
          else 0 := by
    dsimp only [faceRoot, innerRoot]
    rw [mixedFace_sum_expand]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    by_cases hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d (i.succAbove a)) (e b)
    · rw [ite_eq_left hc, ← add_sub_assoc, add_sub_cancel_left]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      have hclass := (hresidue d hd e he hc).2.2.2 n
      have hshift : Nat.ModEq (modulus d e) (n + h i) (residue d e + h i) ↔
          Nat.ModEq (modulus d e) n (residue d e) :=
        Nat.ModEq.add_iff_right (Nat.ModEq.refl (h i))
      simp only [hshift, hclass]
    · rw [ite_eq_right hc]
      have hzero : (∑ n ∈ I,
          if Nat.ModEq W n v ∧
            (∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)) ∧
            (∀ j : Fin k, e j ∣ n + h (i.succAbove j))
          then ArithmeticFunction.vonMangoldt (n + h i) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n _
        apply ite_eq_right
        intro hconditions
        exact hc (mixedPair_compatible h hinj i d e W
          (hD d (Finset.mem_filter.mp hd).1).2 hcover n
          hconditions.2.1 hconditions.2.2)
      rw [hzero, mul_zero]
  have hcorrection :
      (∑ n ∈ I, if Nat.ModEq W n v then
        ArithmeticFunction.vonMangoldt (n + h i) * outerRoot n * innerRoot n
        else 0) =
        (∑ n ∈ I, if Nat.ModEq W n v then
          ArithmeticFunction.vonMangoldt (n + h i) * faceRoot n * innerRoot n
          else 0) + primePowerCorrection := by
    dsimp only [primePowerCorrection]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnv : Nat.ModEq W n v
    · simp only [hnv, ite_true]
      by_cases hp : Nat.Prime (n + h i)
      · rw [hprime n hn hp]
        ring
      · simp only [hp, ite_false, sub_zero]
        ring
    · simp only [hnv, ite_false, add_zero]
  exact hcorrection.trans (congrArg (fun s : ℝ => s + primePowerCorrection) hface)

theorem actual_modulus_pairwise_coprime_lcm
    {k : ℕ} (d e : Fin k → ℕ)
    (hd : Squarefree (∏ i, d i)) (he : Squarefree (∏ i, e i))
    (hcross : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) :
    Set.Pairwise ((Finset.univ : Finset (Fin k)) : Set (Fin k))
      (Function.onFun Nat.Coprime (fun i => Nat.lcm (d i) (e i))) := by
  intro i _ j _ hij
  have hdd := coprime_of_squarefree_fintype_prod d hd hij
  have hee := coprime_of_squarefree_fintype_prod e he hij
  have hi : Nat.Coprime (d i) (d j * e j) := hdd.mul_right (hcross i j hij)
  have hj : Nat.Coprime (e i) (d j * e j) :=
    (hcross j i hij.symm).symm.mul_right hee
  exact Nat.Coprime.of_dvd (Nat.lcm_dvd_mul (d i) (e i))
    (Nat.lcm_dvd_mul (d j) (e j)) (hi.mul_left hj)

theorem actual_modulus_coprime_W_prod_lcm
    {k : ℕ} (W : ℕ) (d e : Fin k → ℕ)
    (hd : Nat.Coprime (∏ i, d i) W) (he : Nat.Coprime (∏ i, e i) W) :
    Nat.Coprime W (∏ i, Nat.lcm (d i) (e i)) := by
  apply Nat.Coprime.prod_right
  intro i _
  have hWd := (Nat.coprime_fintype_prod_left_iff.mp hd i).symm
  have hWe := (Nat.coprime_fintype_prod_left_iff.mp he i).symm
  exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d i) (e i))
    (hWd.mul_right hWe)

theorem actual_modulus_eq_product
    {k : ℕ} (W : ℕ) (d e : Fin k → ℕ)
    (hd : Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W)
    (he : Squarefree (∏ i, e i) ∧ Nat.Coprime (∏ i, e i) W)
    (hcross : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) :
    Nat.lcm W (Nat.lcm (∏ i, d i) (∏ i, e i)) =
      W * ∏ i, Nat.lcm (d i) (e i) := by
  classical
  have hpair := actual_modulus_pairwise_coprime_lcm d e hd.1 he.1 hcross
  have hprod : (∏ i, Nat.lcm (d i) (e i)) =
      Nat.lcm (∏ i, d i) (∏ i, e i) := by
    apply Nat.dvd_antisymm
    · rw [← Finset.lcm_eq_prod hpair]
      apply Finset.lcm_dvd
      intro i _
      exact Nat.lcm_dvd
        ((Finset.dvd_prod_of_mem d (Finset.mem_univ i)).trans (Nat.dvd_lcm_left _ _))
        ((Finset.dvd_prod_of_mem e (Finset.mem_univ i)).trans (Nat.dvd_lcm_right _ _))
    · apply Nat.lcm_dvd
      · exact Finset.prod_dvd_prod_of_dvd d (fun i => Nat.lcm (d i) (e i))
          (fun i _ => Nat.dvd_lcm_left (d i) (e i))
      · exact Finset.prod_dvd_prod_of_dvd e (fun i => Nat.lcm (d i) (e i))
          (fun i _ => Nat.dvd_lcm_right (d i) (e i))
  rw [← hprod]
  exact (actual_modulus_coprime_W_prod_lcm W d e hd.2 he.2).lcm_eq_mul

theorem finMulAntidiag_filter_coordinate
    {r n a : ℕ} {i : Fin (r + 1)} :
    {d ∈ (r + 1).finMulAntidiag n | d i = a} =
      if a ∣ n then (r.finMulAntidiag (n / a)).map
        ⟨i.insertNth a, Fin.insertNth_right_injective _⟩ else ∅ := by
  classical
  ext d
  obtain ⟨⟨b, d⟩, rfl⟩ := (Fin.insertNthEquiv (fun _ ↦ ℕ) i).surjective d
  have hinsert : (Fin.insertNthEquiv (fun _ ↦ ℕ) i) (b, d) =
      i.insertNth b d := rfl
  rw [hinsert]
  simp_rw [Finset.mem_filter, mem_ite, Finset.mem_map,
    Function.Embedding.coeFn_mk, Nat.mem_finMulAntidiag, Finset.notMem_empty,
    imp_false, not_not, show ∀ p q, (p → q) ∧ p ↔ p ∧ q by grind,
    Fin.insertNth_apply_same, Fin.prod_insertNth, Fin.insertNth_inj]
  constructor
  · rintro ⟨⟨rfl, hn⟩, rfl⟩
    grind [dvd_mul_right, mul_ne_zero_iff, Nat.mul_div_cancel_left]
  · rintro ⟨han, e, ⟨he, hna⟩, rfl, rfl⟩
    rw [he, Nat.mul_div_cancel' han]
    grind [Nat.div_ne_zero_iff.mp hna]

theorem zeta_pow_eq_card_finMulAntidiag {r n : ℕ} :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n =
      (r.finMulAntidiag n).card := by
  classical
  induction r generalizing n with
  | zero =>
      by_cases hn : n = 1
      · rw [hn, pow_zero, ArithmeticFunction.one_one,
          Nat.finMulAntidiag_one, Finset.card_singleton]
      · rw [pow_zero, ArithmeticFunction.one_apply_ne hn,
          Nat.finMulAntidiag_zero_left hn, Finset.card_empty]
  | succ r ih =>
      obtain rfl | hn := eq_or_ne n 0
      · exact ArithmeticFunction.map_zero
      obtain rfl | hr := eq_or_ne r 0
      · rw [pow_one, ArithmeticFunction.zeta_apply_ne hn]
        refine (Finset.card_eq_one.mpr ⟨fun _ ↦ n, ?_⟩).symm
        ext d
        rw [Nat.mem_finMulAntidiag, Fin.prod_univ_one, and_iff_left hn,
          Finset.mem_singleton]
        exact ⟨fun h ↦ funext fun i ↦ (congrArg d (Fin.fin_one_eq_zero i)).trans h,
          fun h ↦ congrFun h 0⟩
      rw [pow_succ, ArithmeticFunction.mul_apply,
        Finset.card_eq_sum_card_image (fun d ↦ d (Fin.last r)),
        Nat.image_apply_finMulAntidiag (by omega),
        Nat.sum_divisorsAntidiagonal'
          (fun a b ↦ ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) a *
            ArithmeticFunction.zeta b)]
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      rw [Nat.mem_divisors] at ha
      rw [finMulAntidiag_filter_coordinate, ite_eq_left ha.1, Finset.card_map, ih,
        ArithmeticFunction.zeta_apply_ne (_root_.ne_zero_of_dvd_ne_zero hn ha.1), mul_one]

theorem one_le_zeta_pow {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    1 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n := by
  classical
  rw [zeta_pow_eq_card_finMulAntidiag, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
  refine ⟨fun i ↦ if i = (⟨0, hr⟩ : Fin r) then n else 1, ?_⟩
  rw [Nat.mem_finMulAntidiag]
  exact ⟨by simp [Finset.prod_ite_eq' Finset.univ (⟨0, hr⟩ : Fin r) (fun _ ↦ n)], hn.ne'⟩

theorem product_lcm_fiber_card_le
    {k : ℕ} (hk : 0 < k) (W : ℕ) (hW : 0 < W)
    (D E : Finset (Fin k → ℕ))
    (hD : ∀ d ∈ D, (∀ i, 0 < d i) ∧ Nat.Coprime (∏ i, d i) W)
    (hE : ∀ e ∈ E, (∀ i, 0 < e i) ∧ Nat.Coprime (∏ i, e i) W)
    (q : ℕ) :
    (((D.product E).filter fun p =>
      W * ∏ i, Nat.lcm (p.1 i) (p.2 i) = q).card) ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 * k)) q := by
  classical
  set F := (D.product E).filter fun p => W * ∏ i, Nat.lcm (p.1 i) (p.2 i) = q
  rcases Finset.eq_empty_or_nonempty F with hF | ⟨p₀, hp₀⟩
  · simp [hF]
  obtain ⟨hpD₀, hpE₀⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp₀).1
  obtain ⟨hd₀, hdcop₀⟩ := hD p₀.1 hpD₀
  obtain ⟨he₀, hecop₀⟩ := hE p₀.2 hpE₀
  have hqOf : ∀ p ∈ F, W * ∏ i, Nat.lcm (p.1 i) (p.2 i) = q :=
    fun _ hp ↦ (Finset.mem_filter.mp hp).2
  let m := ∏ i, Nat.lcm (p₀.1 i) (p₀.2 i)
  have hm : 0 < m := Finset.prod_pos fun i _ ↦ Nat.lcm_pos (hd₀ i) (he₀ i)
  have hq : q = W * m := (hqOf p₀ hp₀).symm
  have hWm : Nat.Coprime W m :=
    actual_modulus_coprime_W_prod_lcm W p₀.1 p₀.2 hdcop₀ hecop₀
  have hz : ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 * k)) m ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 * k)) q := by
    rw [hq, (ArithmeticFunction.isMultiplicative_zeta.pow (k := 3 * k)).map_mul_of_coprime hWm]
    exact Nat.le_mul_of_pos_left _ (one_le_zeta_pow (by omega) hW)
  refine le_trans ?_ hz
  rw [zeta_pow_eq_card_finMulAntidiag]
  let eqv : Fin 3 × Fin k ≃ Fin (3 * k) := finProdFinEquiv
  let slot : Fin 3 → ℕ → ℕ → ℕ := fun s a b ↦
    if s = 0 then Nat.gcd a b else if s = 1 then a / Nat.gcd a b else b / Nat.gcd a b
  let encode : ((Fin k → ℕ) × (Fin k → ℕ)) → Fin (3 * k) → ℕ := fun p j ↦
    slot (eqv.symm j).1 (p.1 (eqv.symm j).2) (p.2 (eqv.symm j).2)
  apply Finset.card_le_card_of_injOn encode
  · intro p hp
    have hprod : (∏ j, encode p j) =
        ∏ x : Fin 3 × Fin k, slot x.1 (p.1 x.2) (p.2 x.2) :=
      (Fintype.prod_equiv eqv _ (encode p) fun x ↦ by
        simp [encode, Equiv.symm_apply_apply]).symm
    have hlocal : ∀ i, slot 0 (p.1 i) (p.2 i) * slot 1 (p.1 i) (p.2 i) *
        slot 2 (p.1 i) (p.2 i) = Nat.lcm (p.1 i) (p.2 i) := fun i ↦ by
      dsimp [slot]
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left (p.1 i) (p.2 i)),
        ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right (p.1 i) (p.2 i)), Nat.lcm_eq_mul_div]
    have hencode : (∏ j, encode p j) = ∏ i, Nat.lcm (p.1 i) (p.2 i) := by
      rw [hprod, Fintype.prod_prod_type' (fun a b ↦ slot a (p.1 b) (p.2 b)),
        Finset.prod_comm]
      exact Finset.prod_congr rfl fun i _ ↦ (Fin.prod_univ_three _).trans (hlocal i)
    have hmod : ∏ i, Nat.lcm (p.1 i) (p.2 i) = m :=
      Nat.eq_of_mul_eq_mul_left hW (by rw [hqOf p hp, hq])
    exact Nat.mem_finMulAntidiag.mpr ⟨hencode.trans hmod, hm.ne'⟩
  · intro p _ p' _ hencode
    have hslot : ∀ (s : Fin 3) (i : Fin k),
        slot s (p.1 i) (p.2 i) = slot s (p'.1 i) (p'.2 i) := fun s i ↦ by
      simpa only [encode, Equiv.symm_apply_apply] using congrFun hencode (eqv (s, i))
    have hcoords : ∀ i, p.1 i = p'.1 i ∧ p.2 i = p'.2 i := by
      intro i
      have hg := hslot 0 i
      have ha := hslot 1 i
      norm_num [slot] at hg ha
      have hb : p.2 i / Nat.gcd (p.1 i) (p.2 i) =
          p'.2 i / Nat.gcd (p'.1 i) (p'.2 i) := by
        simpa [slot, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
          using hslot 2 i
      exact ⟨by
        rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left (p.1 i) (p.2 i)),
          ← Nat.mul_div_cancel' (Nat.gcd_dvd_left (p'.1 i) (p'.2 i)), ha, hg], by
        rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right (p.1 i) (p.2 i)),
          ← Nat.mul_div_cancel' (Nat.gcd_dvd_right (p'.1 i) (p'.2 i)), hb, hg]⟩
    ext i
    · exact (hcoords i).1
    · exact (hcoords i).2

theorem selberg_actual_modulus_fiber_card_le_zeta_pow
    {k : ℕ} (hk : 0 < k) (W : ℕ) (hW : 0 < W)
    (D E : Finset (Fin k → ℕ))
    (hD : ∀ d ∈ D,
      Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W)
    (hE : ∀ e ∈ E,
      Squarefree (∏ i, e i) ∧ Nat.Coprime (∏ i, e i) W)
    (gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop)
    [DecidableRel gate]
    (hcross : ∀ d ∈ D, ∀ e ∈ E, gate d e →
      ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j))
    (q : ℕ) :
    (((D.product E).filter fun p => gate p.1 p.2 ∧
      Nat.lcm W (Nat.lcm (∏ i, p.1 i) (∏ i, p.2 i)) = q).card) ≤
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 * k)) q) := by
  classical
  have hpos {d : Fin k → ℕ} (hd : Squarefree (∏ i, d i)) : ∀ i, 0 < d i := by
    intro i
    exact Nat.pos_of_ne_zero
      ((Finset.prod_ne_zero_iff.mp hd.ne_zero) i (Finset.mem_univ i))
  refine (Finset.card_le_card ?_).trans
    (product_lcm_fiber_card_le hk W hW D E
      (fun d hd ↦ ⟨hpos (hD d hd).1, (hD d hd).2⟩)
      (fun e he ↦ ⟨hpos (hE e he).1, (hE e he).2⟩) q)
  intro p hp
  obtain ⟨hpDE, hgate, hq⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpD, hpE⟩ := Finset.mem_product.mp hpDE
  refine Finset.mem_filter.mpr ⟨hpDE, ?_⟩
  rw [← actual_modulus_eq_product W p.1 p.2 (hD p.1 hpD) (hE p.2 hpE)
    (hcross p.1 hpD p.2 hpE hgate)]
  exact hq

theorem selberg_actual_modulus_weighted_error_le
    {k : ℕ} (hk : 0 < k) (W : ℕ) (hW : 0 < W)
    (D E : Finset (Fin k → ℕ))
    (hD : ∀ d ∈ D,
      Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W)
    (hE : ∀ e ∈ E,
      Squarefree (∏ i, e i) ∧ Nat.Coprime (∏ i, e i) W)
    (gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop)
    [DecidableRel gate]
    (hcross : ∀ d ∈ D, ∀ e ∈ E, gate d e →
      ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j))
    (lam mu : (Fin k → ℕ) → ℝ)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hlam : ∀ d ∈ D, |lam d| ≤ B₁)
    (hmu : ∀ e ∈ E, |mu e| ≤ B₂)
    (Q : Finset ℕ) (delta : ℕ → ℝ)
    (hdelta : ∀ q ∈ Q, 0 ≤ delta q)
    (hmoduli : ∀ d ∈ D, ∀ e ∈ E, gate d e →
      Nat.lcm W (Nat.lcm (∏ i, d i) (∏ i, e i)) ∈ Q) :
    (∑ p ∈ (D.product E).filter (fun p => gate p.1 p.2),
      |lam p.1| * |mu p.2| *
        delta (Nat.lcm W (Nat.lcm (∏ i, p.1 i) (∏ i, p.2 i)))) ≤
      B₁ * B₂ * ∑ q ∈ Q,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 * k)) q : ℕ) : ℝ) *
          delta q := by
  classical
  let S := (D.product E).filter fun p => gate p.1 p.2
  let mod : ((Fin k → ℕ) × (Fin k → ℕ)) → ℕ := fun p ↦
    Nat.lcm W (Nat.lcm (∏ i, p.1 i) (∏ i, p.2 i))
  have hmaps : ∀ p ∈ S, mod p ∈ Q := by
    intro p hp
    obtain ⟨hpDE, hgate⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpD, hpE⟩ := Finset.mem_product.mp hpDE
    exact hmoduli p.1 hpD p.2 hpE hgate
  change (∑ p ∈ S, |lam p.1| * |mu p.2| * delta (mod p)) ≤ _
  trans B₁ * B₂ * ∑ p ∈ S, delta (mod p)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    obtain ⟨hpDE, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpD, hpE⟩ := Finset.mem_product.mp hpDE
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hlam p.1 hpD) (hmu p.2 hpE) (abs_nonneg _) hB₁)
      (hdelta (mod p) (hmaps p hp))
  · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB₁ hB₂)
    rw [← Finset.sum_fiberwise_of_maps_to' hmaps delta]
    refine Finset.sum_le_sum fun q hq ↦ ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hdelta q hq)
    simp only [S, mod, Finset.filter_filter]
    exact_mod_cast selberg_actual_modulus_fiber_card_le_zeta_pow
      hk W hW D E hD hE gate hcross q

/-!
## Exceptional mass and harmonic limits

Bound the exceptional exponent integrals and pass from harmonic configuration sums to the
limiting fragment measures.
-/

/--
The auxiliary radius assigned to an exceptional-mass bin, equal to half the remaining budget
after subtracting `2 * (11 / 40)` and the bin's right endpoint, with safety margin `1 / 10000`.
-/
def exceptionalBinAuxRadius (j : Fin 1024) : ℚ :=
  (1 - 2 * (11 / 40 : ℚ) - exceptionalBinRight j) / 2 - 1 / 10000

/--
The degree-21 alternating Taylor polynomial for `log (1 + t)`, used for rational upper estimates
on the relevant nonnegative range.
-/
def exceptionalLogUpper21 (t : ℚ) : ℚ :=
  ∑ m ∈ Finset.Icc (1 : ℕ) 21, (-1 : ℚ) ^ (m + 1) * t ^ m / (m : ℚ)

/--
The integer ceiling of `10^25` times the rational exceptional-bin estimate, using the bin's
right endpoint and the degree-21 logarithm polynomial.
-/
def exceptionalBinCeiling (j : Fin 1024) : ℤ :=
  ⌈(10 : ℚ) ^ 25 *
    (24 * exceptionalBinStep *
      exceptionalLogUpper21 ((exceptionalBinRight j - 2 * (9519 / 50000 : ℚ)) /
        (9519 / 50000 : ℚ)) /
      (5 * exceptionalBinRight j * ((2249 / 5000 : ℚ) - exceptionalBinRight j)))⌉

/--
The sum of the `1024` upward-rounded exceptional-bin estimates, rescaled from integers by
`10^25`.
-/
def exceptionalBinRationalSum : ℚ :=
  (∑ j : Fin 1024, (exceptionalBinCeiling j : ℚ)) / (10 : ℚ) ^ 25

theorem exceptionalBin_margins (j : Fin 1024) :
    0 < exceptionalBinStep ∧
      2 * (9519 / 50000 : ℚ) < exceptionalBinRight j ∧
      exceptionalBinRight j ≤ (40481 / 100000 : ℚ) ∧
      (4499 / 200000 : ℚ) ≤ exceptionalBinAuxRadius j ∧
      exceptionalBinAuxRadius j < (863 / 25000 : ℚ) ∧
      (863 / 25000 : ℚ) < (19037 / 100000 : ℚ) ∧
      (19037 / 100000 : ℚ) < (9519 / 50000 : ℚ) ∧
      exceptionalBinRight j + 2 * (11 / 40 : ℚ) + 2 * exceptionalBinAuxRadius j =
        1 - (1 / 5000 : ℚ) ∧
      0 ≤ (exceptionalBinRight j - 2 * (9519 / 50000 : ℚ)) /
        (9519 / 50000 : ℚ) ∧
      (exceptionalBinRight j - 2 * (9519 / 50000 : ℚ)) /
        (9519 / 50000 : ℚ) < 1 := by
  have hj0 : (0 : ℚ) ≤ (j.val : ℚ) := Nat.cast_nonneg _
  have hj1 : (j.val : ℚ) ≤ 1023 := by exact_mod_cast (Nat.le_pred_of_lt j.isLt)
  norm_num [exceptionalBinStep, exceptionalBinRight, exceptionalBinAuxRadius]
  all_goals
    repeat' constructor
    all_goals nlinarith

theorem sum_fin_mul_eq_sum_fin_prod {m n : ℕ} (f : Fin (m * n) → ℤ) :
    (∑ j : Fin (m * n), f j) =
      ∑ b : Fin m, ∑ k : Fin n, f (finProdFinEquiv (b, k)) :=
  (finProdFinEquiv.sum_comp f).symm.trans
    (Fintype.sum_prod_type (fun p : Fin m × Fin n => f (finProdFinEquiv p)))

theorem exceptionalBinCeiling_double_sum :
    (∑ b : Fin 32, ∑ k : Fin 32,
      exceptionalBinCeiling (finProdFinEquiv (b, k))) =
        (3361336040272905676441604 : ℤ) := by
  decide +kernel

theorem exceptionalBinRationalSum_value :
    exceptionalBinRationalSum =
        (840334010068226419110401 : ℚ) / 2500000000000000000000000 ∧
      exceptionalBinRationalSum < (337 / 1000 : ℚ) ∧
      (201 / 200 : ℚ) * (337 / 1000 : ℚ) < (17 / 50 : ℚ) := by
  have hQ : exceptionalBinRationalSum =
      (840334010068226419110401 : ℚ) / 2500000000000000000000000 := by
    rw [exceptionalBinRationalSum, ← Int.cast_sum,
      sum_fin_mul_eq_sum_fin_prod (m := 32) (n := 32), exceptionalBinCeiling_double_sum]
    norm_num
  exact ⟨hQ, by rw [hQ]; norm_num, by norm_num⟩

theorem exceptional_log_upper21 (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    Real.log (1 + t) ≤
      ∑ m ∈ Finset.Icc (1 : ℕ) 21, (-1 : ℝ) ^ (m + 1) * t ^ m / (m : ℝ) := by
  let f : ℕ → ℝ := fun n => t ^ (n + 1) / ((n : ℝ) + 1)
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le fun n => ?_
    dsimp only [f]
    refine div_le_div₀ (pow_nonneg ht _) ?_ (by positivity) ?_
    · exact pow_le_pow_of_le_one ht ht1.le (Nat.le_succ _)
    · exact add_le_add (Nat.cast_le.mpr (Nat.le_succ n)) le_rfl
  have hseries : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n) (Real.log (1 + t)) := by
    have h : HasSum (fun n : ℕ => -((-t) ^ (n + 1) / ((n : ℝ) + 1)))
        (Real.log (1 + t)) := by
      simpa only [neg_neg, sub_neg_eq_add] using
        (Real.hasSum_pow_div_log_of_abs_lt_one
          (x := -t) (by rwa [abs_neg, abs_of_nonneg ht])).neg
    refine h.congr_fun fun n => ?_
    dsimp only [f]
    rw [neg_pow t (n + 1), pow_succ (-1 : ℝ) n]
    ring
  calc
    Real.log (1 + t) ≤ ∑ n ∈ Finset.range 21, (-1 : ℝ) ^ n * f n :=
      Antitone.tendsto_le_alternating_series hseries.tendsto_sum_nat hanti 10
    _ = ∑ m ∈ Finset.Icc (1 : ℕ) 21, (-1 : ℝ) ^ (m + 1) * t ^ m / (m : ℝ) := by
      rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      simp only [f, Nat.add_comm 1 n, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem exceptionalPairDensity_monotone :
    MonotoneOn
      (fun s : ℝ => Real.log ((s - (9519 / 50000 : ℝ)) / (9519 / 50000 : ℝ)) / s)
      (Set.Icc (2 * (9519 / 50000 : ℝ)) (40481 / 100000 : ℝ)) := by
  let ξ : ℝ := 9519 / 50000
  let a : ℝ := 40481 / 100000
  let f : ℝ → ℝ := fun s => Real.log ((s - ξ) / ξ) / s
  have hξ : 0 < ξ := by norm_num [ξ]
  have ha : a < 3 * ξ := by norm_num [a, ξ]
  have hpos (s : ℝ) (hs : s ∈ Set.Icc (2 * ξ) a) :
      0 < s ∧ 0 < s - ξ := by
    constructor <;> linarith [hs.1]
  have hderiv (s : ℝ) (hs : s ∈ Set.Icc (2 * ξ) a) :
      HasDerivAt f ((s / (s - ξ) - Real.log ((s - ξ) / ξ)) / s ^ 2) s := by
    obtain ⟨hspos, hsub⟩ := hpos s hs
    have hlog := (((hasDerivAt_id' s).sub_const ξ).div_const ξ).log
      (ne_of_gt (div_pos hsub hξ))
    rw [div_div_div_cancel_right₀ hξ.ne', one_div] at hlog
    simpa only [f, inv_mul_eq_div, mul_one] using
      hlog.fun_div (hasDerivAt_id' s) hspos.ne'
  change MonotoneOn f (Set.Icc (2 * ξ) a)
  refine (strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_).monotoneOn
  · intro s hs
    exact (hderiv s hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Set.Icc (2 * ξ) a := interior_subset hs
    obtain ⟨hspos, hsub⟩ := hpos s hs'
    have hqlt : (s - ξ) / ξ < 2 :=
      (div_lt_iff₀ hξ).2 (by linarith [hs'.2])
    have hloglt : Real.log ((s - ξ) / ξ) < 1 :=
      (Real.log_le_sub_one_of_pos (div_pos hsub hξ)).trans_lt (by linarith)
    have hratio : 1 < s / (s - ξ) :=
      (one_lt_div hsub).2 (sub_lt_self s hξ)
    rw [(hderiv s hs').deriv]
    exact div_pos (sub_pos.mpr (hloglt.trans hratio)) (pow_pos hspos 2)

theorem exceptionalBin_integral_upper (j : Fin 1024) :
    let D : ℝ → ℝ :=
      fun s => Real.log ((s - (9519 / 50000 : ℝ)) / (9519 / 50000 : ℝ)) / s
    let l : ℝ := (exceptionalBinRight j : ℝ) - (exceptionalBinStep : ℝ)
    let u : ℝ := (exceptionalBinRight j : ℝ)
    0 ≤ (∫ s in l..u, D s) ∧
      (12 / 5 : ℝ) * (exceptionalBinAuxRadius j : ℝ)⁻¹ *
          (∫ s in l..u, D s) ≤
        (exceptionalBinCeiling j : ℝ) / (10 : ℝ) ^ 25 := by
  intro D l u
  rcases exceptionalBin_margins j with
    ⟨hstepQ, _, huTopQ, hzQ, _, _, _, _, htQ, ht1Q⟩
  have hstep : 0 < (exceptionalBinStep : ℝ) := Rat.cast_pos.mpr hstepQ
  have huUpper : u ≤ (40481 / 100000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, u] using
      (Rat.cast_le (K := ℝ)).mpr huTopQ
  have hz : 0 < (exceptionalBinAuxRadius j : ℝ) :=
    Rat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) hzQ)
  have hleft : l = 2 * (9519 / 50000 : ℝ) +
      (j.val : ℝ) * (exceptionalBinStep : ℝ) := by
    dsimp only [l, exceptionalBinRight]
    push_cast
    ring
  have hlLower : 2 * (9519 / 50000 : ℝ) ≤ l := by
    rw [hleft]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep.le)
  have hlu : l ≤ u := sub_le_self _ hstep.le
  have huPos : 0 < u :=
    lt_of_lt_of_le (by norm_num) (hlLower.trans hlu)
  have hwidth : u - l = (exceptionalBinStep : ℝ) := sub_sub_cancel _ _
  have hsub : Set.Icc l u ⊆
      Set.Icc (2 * (9519 / 50000 : ℝ)) (40481 / 100000 : ℝ) :=
    Set.Icc_subset_Icc hlLower huUpper
  have hmono : MonotoneOn D
      (Set.Icc (2 * (9519 / 50000 : ℝ)) (40481 / 100000 : ℝ)) :=
    exceptionalPairDensity_monotone
  have hbase : D (2 * (9519 / 50000 : ℝ)) = 0 := by norm_num [D]
  have hbaseMem : 2 * (9519 / 50000 : ℝ) ∈
      Set.Icc (2 * (9519 / 50000 : ℝ)) (40481 / 100000 : ℝ) := by
    norm_num
  have hnonneg : ∀ s ∈ Set.Icc l u, 0 ≤ D s := by
    intro s hs
    have hs' := hsub hs
    simpa only [hbase] using hmono hbaseMem hs' hs'.1
  have hint : IntervalIntegrable D MeasureTheory.volume l u := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hlu]
    exact hmono.mono hsub
  have hupper : (∫ s in l..u, D s) ≤ (exceptionalBinStep : ℝ) * D u := by
    calc
      _ ≤ ∫ _s in l..u, D u :=
        intervalIntegral.integral_mono_on hlu hint intervalIntegrable_const
          (fun s hs => hmono (hsub hs) (hsub ⟨hlu, le_rfl⟩) hs.2)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, hwidth]
  let t : ℚ := (exceptionalBinRight j - 2 * (9519 / 50000 : ℚ)) /
    (9519 / 50000 : ℚ)
  have harg : 1 + (t : ℝ) =
      (u - (9519 / 50000 : ℝ)) / (9519 / 50000 : ℝ) := by
    dsimp only [t, u]
    push_cast
    ring
  have hlog : Real.log ((u - (9519 / 50000 : ℝ)) / (9519 / 50000 : ℝ)) ≤
      (exceptionalLogUpper21 t : ℝ) := by
    simpa only [exceptionalLogUpper21, Rat.cast_sum, Rat.cast_div, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast, harg] using
      exceptional_log_upper21 (t : ℝ) (Rat.cast_nonneg.mpr htQ)
        (by exact_mod_cast ht1Q)
  have hzEq : (exceptionalBinAuxRadius j : ℝ) =
      ((2249 / 5000 : ℝ) - u) / 2 := by
    dsimp only [exceptionalBinAuxRadius, u]
    push_cast
    ring
  let q : ℚ := 24 * exceptionalBinStep * exceptionalLogUpper21 t /
    (5 * exceptionalBinRight j * ((2249 / 5000 : ℚ) - exceptionalBinRight j))
  have hqcast : (q : ℝ) =
      24 * (exceptionalBinStep : ℝ) * (exceptionalLogUpper21 t : ℝ) /
        (5 * u * ((2249 / 5000 : ℝ) - u)) := by
    simp only [q, u, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat]
  have hscaled : (12 / 5 : ℝ) * (exceptionalBinAuxRadius j : ℝ)⁻¹ *
      (∫ s in l..u, D s) ≤ (q : ℝ) := by
    calc
      _ ≤ (12 / 5 : ℝ) * (exceptionalBinAuxRadius j : ℝ)⁻¹ *
          ((exceptionalBinStep : ℝ) * D u) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ ≤ (12 / 5 : ℝ) * (exceptionalBinAuxRadius j : ℝ)⁻¹ *
          ((exceptionalBinStep : ℝ) * ((exceptionalLogUpper21 t : ℝ) / u)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog huPos.le) hstep.le)
          (by positivity)
      _ = (q : ℝ) := by
        rw [hqcast, hzEq]
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
  have hceilQ : (10 : ℚ) ^ 25 * q ≤ (exceptionalBinCeiling j : ℚ) :=
    Int.le_ceil _
  have hceil : (10 : ℝ) ^ 25 * (q : ℝ) ≤ (exceptionalBinCeiling j : ℝ) := by
    exact_mod_cast hceilQ
  refine ⟨intervalIntegral.integral_nonneg hlu hnonneg, hscaled.trans ?_⟩
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 25)).2
  simpa only [mul_comm] using hceil

end PrimeGap182.Selberg

section
open Real Finset Filter Asymptotics Topology

open Classical in
theorem PrimeGap182.Selberg.selberg_square_real_interval_crt_marked
    {ι : Type*} [Fintype ι] (h : ι → ℕ) (hinj : Function.Injective h) (i : ι)
    (D : Finset (ι → ℕ)) (lam : (ι → ℕ) → ℝ)
    (W b M : ℕ) (hW : 0 < W) (hM : 0 < M) (hWM : Nat.Coprime W M)
    (hD : ∀ d ∈ D,
      Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W ∧
        Nat.Coprime (∏ j, d j) M)
    (hcover : ∀ a c : ι, h a ≠ h c → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h c) → p ∣ W)
    (x : ℝ) (hx : 0 ≤ x) :
    |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq W n b ∧ M ∣ n + h i then
          (∑ d ∈ D, if ∀ j, d j ∣ n + h j then lam d else 0) ^ 2
        else 0) -
      x / ((W : ℝ) * (M : ℝ)) *
        (∑ d ∈ D, ∑ e ∈ D,
          if ∀ a c : ι, a ≠ c → Nat.Coprime (d a) (e c) then
            lam d * lam e / (∏ j, (Nat.lcm (d j) (e j) : ℝ))
          else 0)| ≤ 2 * (∑ d ∈ D, |lam d|) ^ 2 := by
  let c := Nat.chineseRemainder hWM b (M - h i % M)
  have hres : Nat.ModEq M (M - h i % M + h i) 0 := by
    have ht := (Nat.mod_modEq (h i) M).add_left (M - h i % M)
    rw [Nat.sub_add_cancel (Nat.mod_lt (h i) hM).le] at ht
    exact ht.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl M))
  have hmark (n : ℕ) : Nat.ModEq M n (M - h i % M) ↔ M ∣ n + h i := by
    constructor
    · intro hn
      exact Nat.modEq_zero_iff_dvd.mp ((hn.add_right (h i)).trans hres)
    · intro hn
      exact Nat.ModEq.add_right_cancel' (h i)
        ((Nat.modEq_zero_iff_dvd.mpr hn).trans hres.symm)
  have hclass (n : ℕ) :
      Nat.ModEq (W * M) n (c : ℕ) ↔ Nat.ModEq W n b ∧ M ∣ n + h i := by
    constructor
    · intro hn
      exact ⟨(hn.of_mul_right M).trans c.property.1,
        (hmark n).mp ((hn.of_mul_left W).trans c.property.2)⟩
    · rintro ⟨hn, hm⟩
      exact Nat.chineseRemainder_modEq_unique hWM hn ((hmark n).mpr hm)
  have hcrt := PrimeGap182.Selberg.selberg_square_real_interval_crt
    h hinj D lam (W * M) (c : ℕ) (Nat.mul_pos hW hM)
    (fun d hd => ⟨(hD d hd).1, (hD d hd).2.1.mul_right (hD d hd).2.2⟩)
    (fun a c hac p hp hdist => dvd_mul_of_dvd_left (hcover a c hac p hp hdist) M)
    x hx
  simp_rw [hclass, Nat.cast_mul] at hcrt
  refine hcrt.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro d _
  apply Finset.sum_le_sum
  intro e _
  split_ifs
  · exact le_of_eq (abs_mul _ _)
  · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

open Classical in
theorem PrimeGap182.Selberg.selberg39_auxiliary_marked_real_interval_crt
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (x κ : ℝ) (hx : 1 < x) (hκ : 0 < κ) :
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
      let mean : ℝ :=
        (1 / (q : ℝ)) *
          ∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2
      ∀ (M : ℕ), 0 < M → Nat.Coprime W M →
        (∀ s ∈ u.support, Nat.Coprime (s 0) M) →
        (∀ r ∈ z.support, Nat.Coprime (∏ j, r j) M) →
        ∀ b : ℕ,
          |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
              if Nat.ModEq W n b ∧ M ∣ n + h i then
                (L (n + h i) * C n) ^ 2 else 0) -
            x / ((W : ℝ) * (M : ℝ)) * mean| ≤
            2 * (∑ e ∈ Du, |PrimeGap182.Selberg.selbergCoefficient u e|) ^ 2 *
              (∑ d ∈ Dz, |PrimeGap182.Selberg.selbergCoefficient z d|) ^ 2 := by
  refine (fun (_ : 0 < κ) => ?_) hκ
  classical
  intro ρ h W R P q u z hu hz Du Dz L C mean M hM hWM huM hzM b
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
  have hmean : mean = ∑ a ∈ D, ∑ c ∈ D,
      if ∀ j k : Fin 39, j ≠ k → Nat.Coprime (a j) (c k) then
        lam a * lam c / (∏ j, (Nat.lcm (a j) (c j) : ℝ)) else 0 := by
    dsimp only [mean]
    simp_rw [hvalue]
    convert PrimeGap182.Selberg.selberg_square_period_mean h hinj D lam W q hq
      (fun a ha => ⟨(hD a ha).1, (hD a ha).2.1, (hD a ha).2.2.2⟩)
      hcover using 1 <;> congr!
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
  have herror :
      2 * (∑ a ∈ D, |lam a|) ^ 2 ≤
        2 * (∑ e ∈ Du, |PrimeGap182.Selberg.selbergCoefficient u e|) ^ 2 *
          (∑ d ∈ Dz, |PrimeGap182.Selberg.selbergCoefficient z d|) ^ 2 := by
    calc
      _ ≤ 2 * ((∑ e ∈ Du, |PrimeGap182.Selberg.selbergCoefficient u e|) *
          (∑ d ∈ Dz, |PrimeGap182.Selberg.selbergCoefficient z d|)) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hl1 2)
          (by norm_num)
      _ = _ := by ring
  have hcrt := PrimeGap182.Selberg.selberg_square_real_interval_crt_marked h hinj i D lam W b M hW hM hWM
    (fun a ha => ⟨(hD a ha).1, (hD a ha).2.1, (hD a ha).2.2.1⟩)
    hcover x (by linarith)
  have hinterval :
      |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          if Nat.ModEq W n b ∧ M ∣ n + h i then (L (n + h i) * C n) ^ 2 else 0) -
        x / ((W : ℝ) * (M : ℝ)) * mean| ≤
        2 * (∑ a ∈ D, |lam a|) ^ 2 := by
    convert hcrt using 1
    · simp_rw [hvalue, hmean]
      congr!
  exact hinterval.trans herror

end

namespace PrimeGap182.Selberg

open Real Finset Asymptotics Topology
open ArithmeticFunction hiding log

open Classical in
theorem selberg39_auxiliary_real_interval_crt
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (x κ : ℝ) (hx : 1 < x) (hκ : 0 < κ) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W := presievingModulus 𝓗 x
    let R := x ^ ρ
    let P := fragmentPrimes W R κ
    let q : ℕ := ∏ p ∈ P, p
    ∀ (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ),
      (∀ s ∈ u.support, s 0 ∈ q.divisors) →
      (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
      let Du := u.support.biUnion
        (fun s => Fintype.piFinset (fun j => (s j).divisors))
      let Dz := z.support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
      let L : ℕ → ℝ := fun t =>
        ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
      let C : ℕ → ℝ := fun n =>
        ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
          selbergCoefficient z d else 0
      let mean : ℝ :=
        (1 / (q : ℝ)) *
          ∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2
      ∀ b : ℕ,
        |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            if Nat.ModEq W n b then (L (n + h i) * C n) ^ 2 else 0) -
          x / (W : ℝ) * mean| ≤
          2 * (∑ e ∈ Du, |selbergCoefficient u e|) ^ 2 *
            (∑ d ∈ Dz, |selbergCoefficient z d|) ^ 2 := by
  intro ρ h W R P q u z hu hz Du Dz L C mean b
  simpa only [Nat.cast_one, mul_one, one_dvd, and_true] using
    selberg39_auxiliary_marked_real_interval_crt
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ u z hu hz
      1 (by decide) (by simp) (fun s _ => by simp) (fun r _ => by simp) b

open Classical in
theorem auxiliary_two_radius_l1_bound
    (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ) (q : ℕ)
    (x r_c ζ_a M N Bx B : ℝ)
    (hx : 1 < x) (hrc : 0 ≤ r_c) (hζ_a : 0 ≤ ζ_a)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hBx : 0 < Bx) (hB : 0 < B)
    (hqsf : Squarefree q)
    (hu : ∀ s ∈ u.support, s 0 ∈ q.divisors ∧ (s 0 : ℝ) ≤ x ^ ζ_a)
    (hz : ∀ r ∈ z.support,
      Squarefree (∏ j, r j) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r_c)
    (huBound : ∀ s, |u s| ≤ N / Bx)
    (hzBound : ∀ r, |z r| ≤ M / B ^ 38)
    (hlogcap : 1 + Real.log (⌊x ^ (r_c + ζ_a)⌋₊ : ℝ) ≤ Real.log x) :
    let Du := u.support.biUnion
      (fun s => Fintype.piFinset (fun j => (s j).divisors))
    let Dz := z.support.biUnion
      (fun r => Fintype.piFinset (fun j => (r j).divisors))
    let J : ℕ := 7 + (2 ^ (38 + 2) - 1)
    2 * (∑ e ∈ Du, |selbergCoefficient u e|) ^ 2 *
        (∑ d ∈ Dz, |selbergCoefficient z d|) ^ 2 ≤
      (2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
        x ^ (2 * (r_c + ζ_a)) * Real.log x ^ (2 * J) := by
  intro Du Dz J
  let La : ℕ := ⌊x ^ ζ_a⌋₊
  let Lc : ℕ := ⌊x ^ r_c⌋₊
  let Ja : ℕ := 7
  let Jc : ℕ := 2 ^ (38 + 2) - 1
  let Qa : ℝ := (1 + Real.log (La : ℝ)) ^ Ja
  let Qc : ℝ := (1 + Real.log (Lc : ℝ)) ^ Jc
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hLa1 : 1 ≤ La :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx.le hζ_a)
  have hLc1 : 1 ≤ Lc :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx.le hrc)
  have hLa1R : (1 : ℝ) ≤ La := by exact_mod_cast hLa1
  have hLc1R : (1 : ℝ) ≤ Lc := by exact_mod_cast hLc1
  have hLa0 : (0 : ℝ) < La := zero_lt_one.trans_le hLa1R
  have hLc0 : (0 : ℝ) < Lc := zero_lt_one.trans_le hLc1R
  have hLaCap : La ≤ ⌊x ^ (r_c + ζ_a)⌋₊ :=
    Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le hx.le (le_add_of_nonneg_left hrc))
  have hLcCap : Lc ≤ ⌊x ^ (r_c + ζ_a)⌋₊ :=
    Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le hx.le (le_add_of_nonneg_right hζ_a))
  have hlogLa0 : 0 ≤ 1 + Real.log (La : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg hLa1R)
  have hlogLc0 : 0 ≤ 1 + Real.log (Lc : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg hLc1R)
  have hlogLa : 1 + Real.log (La : ℝ) ≤ Real.log x := by
    have hmono := Real.log_le_log hLa0
      (show (La : ℝ) ≤ (⌊x ^ (r_c + ζ_a)⌋₊ : ℝ) by exact_mod_cast hLaCap)
    linarith only [hmono, hlogcap]
  have hlogLc : 1 + Real.log (Lc : ℝ) ≤ Real.log x := by
    have hmono := Real.log_le_log hLc0
      (show (Lc : ℝ) ≤ (⌊x ^ (r_c + ζ_a)⌋₊ : ℝ) by exact_mod_cast hLcCap)
    linarith only [hmono, hlogcap]
  have hQa0 : 0 ≤ Qa := pow_nonneg hlogLa0 Ja
  have hQc0 : 0 ≤ Qc := pow_nonneg hlogLc0 Jc
  have hQa : Qa ≤ Real.log x ^ Ja := pow_le_pow_left₀ hlogLa0 hlogLa Ja
  have hQc : Qc ≤ Real.log x ^ Jc := pow_le_pow_left₀ hlogLc0 hlogLc Jc
  have hQ : Qa * Qc ≤ Real.log x ^ J := by
    calc
      Qa * Qc ≤ Real.log x ^ Ja * Real.log x ^ Jc :=
        mul_le_mul hQa hQc hQc0 (pow_nonneg hlogx Ja)
      _ = Real.log x ^ J := (pow_add (Real.log x) Ja Jc).symm
  have hLa : (La : ℝ) ≤ x ^ ζ_a := Nat.floor_le (Real.rpow_nonneg hx0.le ζ_a)
  have hLc : (Lc : ℝ) ≤ x ^ r_c := Nat.floor_le (Real.rpow_nonneg hx0.le r_c)
  have hlength : (La : ℝ) * (Lc : ℝ) ≤ x ^ (r_c + ζ_a) := by
    calc
      (La : ℝ) * (Lc : ℝ) ≤ x ^ ζ_a * x ^ r_c :=
        mul_le_mul hLa hLc (Nat.cast_nonneg Lc) (Real.rpow_nonneg hx0.le ζ_a)
      _ = x ^ (r_c + ζ_a) := by rw [← Real.rpow_add hx0, add_comm ζ_a r_c]
  have huL : ∀ s ∈ u.support, Squarefree (∏ j, s j) ∧ (∏ j, s j) ≤ La := by
    intro s hs
    have hsquare : Squarefree (s 0) :=
      hqsf.squarefree_of_dvd (Nat.mem_divisors.mp (hu s hs).1).1
    have hle : s 0 ≤ La :=
      (Nat.le_floor_iff (Real.rpow_nonneg hx0.le ζ_a)).mpr (hu s hs).2
    simpa only [Fin.prod_univ_one] using And.intro hsquare hle
  have hzL : ∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ (∏ j, r j) ≤ Lc := by
    intro r hr
    exact ⟨(hz r hr).1,
      (Nat.le_floor_iff (Real.rpow_nonneg hx0.le r_c)).mpr (hz r hr).2⟩
  have hDu (e : DecidableEq (Fin 1)) :
      u.support.biUnion (fun s => @Fintype.piFinset (Fin 1) e inferInstance
        (fun _ => ℕ) (fun j => (s j).divisors)) = Du := by
    ext d
    simp only [Du, Finset.mem_biUnion, Fintype.mem_piFinset]
  have hDz (e : DecidableEq (Fin 38)) :
      z.support.biUnion (fun r => @Fintype.piFinset (Fin 38) e inferInstance
        (fun _ => ℕ) (fun j => (r j).divisors)) = Dz := by
    ext d
    simp only [Dz, Finset.mem_biUnion, Fintype.mem_piFinset]
  have hlu := selbergCoefficient_l1_le u La (N / Bx) huL huBound
  have hlz := selbergCoefficient_l1_le z Lc (M / B ^ 38) hzL hzBound
  simp only [hDu, Fintype.card_fin] at hlu
  simp only [hDz, Fintype.card_fin] at hlz
  change (∑ e ∈ Du, |selbergCoefficient u e|) ≤ N / Bx * (La : ℝ) * Qa at hlu
  change (∑ d ∈ Dz, |selbergCoefficient z d|) ≤ M / B ^ 38 * (Lc : ℝ) * Qc at hlz
  have hSu0 : 0 ≤ ∑ e ∈ Du, |selbergCoefficient u e| :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hSz0 : 0 ≤ ∑ d ∈ Dz, |selbergCoefficient z d| :=
    Finset.sum_nonneg fun d _ => abs_nonneg _
  have hcoef0 : 0 ≤ M * N / (Bx * B ^ 38) :=
    div_nonneg (mul_nonneg hM hN) (mul_nonneg hBx.le (pow_nonneg hB.le 38))
  have hsumprod :
      (∑ e ∈ Du, |selbergCoefficient u e|) *
          (∑ d ∈ Dz, |selbergCoefficient z d|) ≤
        M * N / (Bx * B ^ 38) * x ^ (r_c + ζ_a) * Real.log x ^ J := by
    calc
      _ ≤ (N / Bx * (La : ℝ) * Qa) * (M / B ^ 38 * (Lc : ℝ) * Qc) :=
        mul_le_mul hlu hlz hSz0
          (mul_nonneg (mul_nonneg (div_nonneg hN hBx.le) (Nat.cast_nonneg La)) hQa0)
      _ = M * N / (Bx * B ^ 38) * ((La : ℝ) * (Lc : ℝ)) * (Qa * Qc) := by
        field_simp [ne_of_gt hBx, ne_of_gt hB]
      _ ≤ M * N / (Bx * B ^ 38) * x ^ (r_c + ζ_a) * Real.log x ^ J :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlength hcoef0) hQ
          (mul_nonneg hQa0 hQc0)
          (mul_nonneg hcoef0 (Real.rpow_nonneg hx0.le (r_c + ζ_a)))
  have hxpow : (x ^ (r_c + ζ_a)) ^ 2 = x ^ (2 * (r_c + ζ_a)) := by
    rw [mul_comm (2 : ℝ) (r_c + ζ_a), Real.rpow_mul hx0.le, Real.rpow_two]
  calc
    _ = 2 * ((∑ e ∈ Du, |selbergCoefficient u e|) *
        (∑ d ∈ Dz, |selbergCoefficient z d|)) ^ 2 := by ring
    _ ≤ 2 * (M * N / (Bx * B ^ 38) *
        x ^ (r_c + ζ_a) * Real.log x ^ J) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hSu0 hSz0) hsumprod 2) (by norm_num)
    _ = (2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
        x ^ (2 * (r_c + ζ_a)) * Real.log x ^ (2 * J) := by
      rw [mul_pow, mul_pow, hxpow, ← pow_mul, mul_comm J 2]
      field_simp [ne_of_gt hBx, ne_of_gt hB]

open Classical in
theorem selberg39_auxiliary_uniform_real_harmonic
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ r_c ζ_a M N : ℝ)
    (hκ : 0 < κ) (hζ_a : 0 < ζ_a)
    (hradius : 2 * (r_c + ζ_a) < 1) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop,
        let ρ : ℝ := 2624989 / 10000000
        let h : Fin 39 → ℕ :=
          𝓗.orderEmbOfFin h𝓗_card
        let W := presievingModulus 𝓗 x
        let R := x ^ ρ
        let Bx := fragmentNormalization W x
        let B := fragmentNormalization W R
        let P := fragmentPrimes W R κ
        let q : ℕ := ∏ p ∈ P, p
        let J : ℕ := 7 + (2 ^ (38 + 2) - 1)
        0 < Bx ∧ 0 < B ∧
          ∀ (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ),
            (∀ s ∈ u.support,
              s 0 ∈ q.divisors ∧ (s 0 : ℝ) ≤ x ^ ζ_a) →
            (∀ r ∈ z.support,
              Squarefree (∏ j, r j) ∧ (∀ j, r j ∈ q.divisors) ∧
                ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r_c) →
            (∀ s, |u s| ≤ N / Bx) →
            (∀ r, |z r| ≤ M / B ^ 38) →
            let Du := u.support.biUnion
              (fun s => Fintype.piFinset (fun j => (s j).divisors))
            let Dz := z.support.biUnion
              (fun r => Fintype.piFinset (fun j => (r j).divisors))
            let L : ℕ → ℝ := fun t =>
              ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
            let C : ℕ → ℝ := fun n =>
              ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
                selbergCoefficient z d else 0
            let mean : ℝ := (1 / (q : ℝ)) *
              ∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2
            let harmonic : ℝ :=
              u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) *
                z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))
            ∀ b : ℕ,
              |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                  if Nat.ModEq W n b then (L (n + h i) * C n) ^ 2 else 0) -
                x / (W : ℝ) * mean| ≤
                  (2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
                    x ^ (2 * (r_c + ζ_a)) * (Real.log x) ^ (2 * J) ∧
              |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                  if Nat.ModEq W n b then (L (n + h i) * C n) ^ 2 else 0) -
                x / (W : ℝ) * harmonic| ≤
                  ε * (x / (W : ℝ) / Bx / B ^ 38) := by
  intro ε hε
  let ρ₀ : ℝ := 2624989 / 10000000
  have hρ : 0 < ρ₀ := by norm_num [ρ₀]
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnormalization : ∀ᶠ x : ℝ in Filter.atTop,
      1 < x ∧
        1 ≤ fragmentNormalization (presievingModulus 𝓗 x) x ∧
        1 ≤ fragmentNormalization (presievingModulus 𝓗 x) (x ^ ρ₀) ∧
        fragmentNormalization (presievingModulus 𝓗 x) (x ^ ρ₀) =
          ρ₀ * fragmentNormalization (presievingModulus 𝓗 x) x ∧
        (presievingModulus 𝓗 x : ℝ) ≤ Real.log x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      presieving_le_mul_log_eventually 𝓗 1 zero_lt_one,
      presieving_le_mul_log_eventually 𝓗 ρ₀ hρ]
      with x hx hWlog hWρ
    let W := presievingModulus 𝓗 x
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hW : 0 < W := presieving_pos 𝓗 x
    have hWR : (0 : ℝ) < W := by exact_mod_cast hW
    have hφ : (1 : ℝ) ≤ (Nat.totient W : ℝ) := by
      exact_mod_cast (show 1 ≤ Nat.totient W from Nat.totient_pos.mpr hW)
    have hWlog' : (W : ℝ) ≤ Real.log x := by simpa only [one_mul] using hWlog
    refine ⟨hx, ?_, ?_, ?_, hWlog'⟩
    · change 1 ≤ ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log x
      rw [div_mul_eq_mul_div]
      exact (one_le_div hWR).mpr
        (hWlog'.trans (le_mul_of_one_le_left hlog hφ))
    · change 1 ≤ ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log (x ^ ρ₀)
      rw [Real.log_rpow hx0, div_mul_eq_mul_div]
      exact (one_le_div hWR).mpr
        (hWρ.trans (le_mul_of_one_le_left (mul_nonneg hρ.le hlog) hφ))
    · unfold fragmentNormalization
      rw [Real.log_rpow hx0]
      ring
  by_cases hrc : 0 ≤ r_c
  · let a : ℝ := r_c + ζ_a
    let J₀ : ℕ := 7 + (2 ^ (38 + 2) - 1)
    have ha : 0 < a := add_pos_of_nonneg_of_pos hrc hζ_a
    have ha1 : a < 1 := by dsimp only [a]; linarith
    have hδ : 0 < 1 - 2 * a := by dsimp only [a]; linarith
    have hlogLimit : Filter.Tendsto
        (fun x : ℝ => Real.log x ^ (2 * J₀ + 1) / x ^ (1 - 2 * a))
        Filter.atTop (nhds 0) := by
      simpa only [Real.rpow_natCast] using
        (isLittleO_log_rpow_rpow_atTop ((2 * J₀ + 1 : ℕ) : ℝ)
          hδ).tendsto_div_nhds_zero
    have hlimit : Filter.Tendsto
        (fun x : ℝ => 2 * (M * N) ^ 2 * Real.log x ^ (2 * J₀ + 1) /
          x ^ (1 - 2 * a)) Filter.atTop (nhds 0) := by
      simpa only [mul_zero, mul_div_assoc] using hlogLimit.const_mul (2 * (M * N) ^ 2)
    have hperiod := selberg39_auxiliary_period_comparison
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ M (ρ₀ * N)
      hκ hM (mul_nonneg hρ.le hN) (ε * ρ₀ / 2) (half_pos (mul_pos hε hρ))
    filter_upwards [hnormalization, floor_rpow_log_envelope a ha ha1,
      hlimit.eventually_le_const hε2, hperiod] with x hn hfloor hsmall hp
    intro ρ h W R Bx B P q J
    rcases hn with ⟨hx, hBx1, hB1, hscale, hWlog⟩
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hBx : 0 < Bx := zero_lt_one.trans_le hBx1
    have hB : 0 < B := zero_lt_one.trans_le hB1
    have hW : 0 < W := presieving_pos 𝓗 x
    have hWR : (0 : ℝ) < W := by exact_mod_cast hW
    have hxW : 0 < x / (W : ℝ) := div_pos hx0 hWR
    have hscale' : B = ρ₀ * Bx := hscale
    refine ⟨hBx, hB, ?_⟩
    intro u z hu hz huBound hzBound Du Dz L C mean harmonic b
    let A : ℝ := x / (W : ℝ) / Bx / B ^ 38
    let S : ℝ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq W n b then (L (n + h i) * C n) ^ 2 else 0
    let raw : ℝ := (2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
      x ^ (2 * (r_c + ζ_a)) * (Real.log x) ^ (2 * J)
    have hA : 0 < A := div_pos (div_pos hxW hBx) (pow_pos hB 38)
    have huMem : ∀ s ∈ u.support, s 0 ∈ q.divisors :=
      fun s hs => (hu s hs).1
    have hzMem : ∀ r ∈ z.support,
        Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors :=
      fun r hr => ⟨(hz r hr).1, (hz r hr).2.1⟩
    have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hqsf : Squarefree q := squarefree_prime_prod P hP
    have hl1 := auxiliary_two_radius_l1_bound u z q x r_c ζ_a M N Bx B
      hx hrc hζ_a.le hM hN hBx hB hqsf hu
      (fun r hr => ⟨(hz r hr).1, (hz r hr).2.2⟩) huBound hzBound hfloor.2.2
    have hfinite := selberg39_auxiliary_real_interval_crt
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ u z huMem hzMem b
    have hCRT : |S - x / (W : ℝ) * mean| ≤ raw := hfinite.trans hl1
    have hrawNorm : raw / A ≤
        2 * (M * N) ^ 2 * Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a) := by
      have hpow : x ^ (2 * (r_c + ζ_a)) = (x ^ a) ^ 2 := by
        dsimp only [a]
        rw [mul_comm 2, Real.rpow_mul hx0.le, Real.rpow_two]
      have hlogpow : Real.log x ^ (2 * J) = (Real.log x ^ J) ^ 2 := by
        rw [Nat.mul_comm 2 J, pow_mul]
      have hden : 1 ≤ Bx * B ^ 38 :=
        (one_le_pow₀ hB1).trans
          (le_mul_of_one_le_left (pow_nonneg hB.le 38) hBx1)
      calc
        raw / A =
            (2 * (M * N) ^ 2 * (W : ℝ) * (x ^ a) ^ 2 *
              (Real.log x ^ J) ^ 2 / x) / (Bx * B ^ 38) := by
          dsimp only [raw, A]
          rw [hpow, hlogpow]
          field_simp [hBx.ne', hB.ne', hx0.ne', hWR.ne']
        _ ≤ 2 * (M * N) ^ 2 * (W : ℝ) * (x ^ a) ^ 2 *
            (Real.log x ^ J) ^ 2 / x :=
          div_le_self
            (div_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (M * N)))
                    (Nat.cast_nonneg W)) (sq_nonneg (x ^ a)))
                (sq_nonneg (Real.log x ^ J))) hx0.le) hden
        _ ≤ 2 * (M * N) ^ 2 * Real.log x * (x ^ a) ^ 2 *
            (Real.log x ^ J) ^ 2 / x :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hWlog
                  (mul_nonneg (by norm_num) (sq_nonneg (M * N))))
                (sq_nonneg (x ^ a))) (sq_nonneg (Real.log x ^ J))) hx0.le
        _ = _ := crt_power_identity (M * N) x a J hx0
    have hCRTsmall : |S - x / (W : ℝ) * mean| ≤ (ε / 2) * A :=
      hCRT.trans ((div_le_iff₀ hA).mp (hrawNorm.trans hsmall))
    have huScaled : ∀ s, |u s| ≤ (ρ₀ * N) / B := by
      intro s
      have heq : N / Bx = (ρ₀ * N) / B := by
        rw [hscale']
        field_simp [hBx.ne', hρ.ne']
      exact (huBound s).trans_eq heq
    have hpMean := (hp.2 u z huMem hzMem huScaled hzBound 0).2.2
    have hbridge := selberg39_auxiliary_exact_period_bridge
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ u z huMem hzMem
    rcases hbridge with ⟨_, _, _, _, _, _, _, _, _, hAffine⟩
    have hmeanEq :
        (1 / (q : ℝ)) * (∑ n ∈ Finset.range q,
          (L (0 + W * n + h i) * C (0 + W * n)) ^ 2) = mean := hAffine 0
    change |(1 / (q : ℝ)) * (∑ n ∈ Finset.range q,
      (L (0 + W * n + h i) * C (0 + W * n)) ^ 2) - harmonic| ≤
        (ε * ρ₀ / 2) / B ^ 39 at hpMean
    rw [hmeanEq] at hpMean
    have hdenom : B ^ 39 = ρ₀ * (Bx * B ^ 38) := by
      rw [show (39 : ℕ) = 38 + 1 from rfl, pow_succ, hscale']
      ring
    have hscaleError : (ε * ρ₀ / 2) / B ^ 39 = (ε / 2) / (Bx * B ^ 38) := by
      rw [hdenom]
      field_simp [hρ.ne', hBx.ne', hB.ne']
    have hmeanInterval : |x / (W : ℝ) * mean - x / (W : ℝ) * harmonic| ≤
        (ε / 2) * A := by
      rw [← mul_sub, abs_mul, abs_of_pos hxW]
      calc
        _ ≤ x / (W : ℝ) * ((ε * ρ₀ / 2) / B ^ 39) :=
          mul_le_mul_of_nonneg_left hpMean hxW.le
        _ = (ε / 2) * A := by rw [hscaleError]; dsimp only [A]; ring
    change |S - x / (W : ℝ) * mean| ≤ raw ∧
      |S - x / (W : ℝ) * harmonic| ≤ ε * A
    refine ⟨hCRT, ?_⟩
    calc
      |S - x / (W : ℝ) * harmonic| ≤
          |S - x / (W : ℝ) * mean| +
            |x / (W : ℝ) * mean - x / (W : ℝ) * harmonic| := abs_sub_le _ _ _
      _ ≤ (ε / 2) * A + (ε / 2) * A := add_le_add hCRTsmall hmeanInterval
      _ = ε * A := by ring
  · filter_upwards [hnormalization] with x hn
    intro ρ h W R Bx B P q J
    rcases hn with ⟨hx, hBx1, hB1, _, _⟩
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hBx : 0 < Bx := zero_lt_one.trans_le hBx1
    have hB : 0 < B := zero_lt_one.trans_le hB1
    have hW : 0 < W := presieving_pos 𝓗 x
    have hWR : (0 : ℝ) < W := by exact_mod_cast hW
    refine ⟨hBx, hB, ?_⟩
    intro u z hu hz huBound hzBound Du Dz L C mean harmonic b
    have hz0 : z = 0 := by
      ext r
      by_contra hzr
      have hr : r ∈ z.support := Finsupp.mem_support_iff.mpr hzr
      have hp : (1 : ℝ) ≤ ((∏ j, r j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero (hz r hr).1.ne_zero)
      have hlt : x ^ r_c < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hx (lt_of_not_ge hrc)
      exact (not_lt_of_ge hp) ((hz r hr).2.2.trans_lt hlt)
    have hDz : Dz = ∅ := by
      simp only [Dz, hz0, Finsupp.support_zero, Finset.biUnion_empty]
    have hC (n : ℕ) : C n = 0 := by
      dsimp only [C]
      rw [hDz, Finset.sum_empty]
    have hperiodZero :
        (∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2) = 0 := by
      simp [hC]
    have hmeanZero : mean = 0 := by
      dsimp only [mean]
      rw [hperiodZero, mul_zero]
    have hharmonicZero : harmonic = 0 := by
      dsimp only [harmonic]
      rw [hz0, Finsupp.sum_zero_index, mul_zero]
    have hintervalZero :
        (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          if Nat.ModEq W n b then (L (n + h i) * C n) ^ 2 else 0) = 0 := by
      simp [hC]
    constructor
    · rw [hintervalZero, hmeanZero, mul_zero, sub_self, abs_zero]
      exact mul_nonneg
        (mul_nonneg
          (div_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) (sq_nonneg N))
            (mul_nonneg (sq_nonneg Bx) (pow_nonneg hB.le 76)))
          (Real.rpow_nonneg hx0.le _)) (pow_nonneg (Real.log_nonneg hx.le) (2 * J))
    · rw [hintervalZero, hharmonicZero, mul_zero, sub_self, abs_zero]
      exact mul_nonneg hε.le
        (div_nonneg (div_nonneg (div_nonneg hx0.le hWR.le) hBx.le)
          (pow_nonneg hB.le 38))

theorem selbergCoefficient_weighted_erase
    (i : Fin 39) (y : (Fin 39 → ℕ) →₀ ℝ) (d : Fin 38 → ℕ) :
    let z : (Fin 38 → ℕ) →₀ ℝ :=
      y.sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
        (yr / ((r i).totient : ℝ)))
    selbergCoefficient z d = selbergCoefficient y (i.insertNth 1 d) := by
  classical
  intro z
  have hprodR :
      (∏ j : Fin 39, (i.insertNth (α := fun _ => ℕ) 1 d j : ℝ)) =
        ∏ j : Fin 38, (d j : ℝ) := by
    rw [Fin.prod_univ_succAbove _ i]
    simp
  have hsum :
      z.sum (fun r yr =>
        if ∀ j, d j ∣ r j then yr / (∏ j, ((r j).totient : ℝ)) else 0) =
      y.sum (fun r yr =>
        if ∀ j, d j ∣ r (i.succAbove j) then
          (yr / ((r i).totient : ℝ)) /
            (∏ j : Fin 38, ((r (i.succAbove j)).totient : ℝ)) else 0) := by
    dsimp only [z]
    rw [Finsupp.sum_sum_index (fun r => by simp)
      (fun r a b => by split_ifs <;> simp [add_div])]
    simp
  unfold selbergCoefficient
  rw [Fin.prod_insertNth, one_mul, hprodR]
  congr 1
  refine Eq.trans ?_ (Eq.trans hsum ?_)
  · apply Finsupp.sum_congr
    intro r hr
    split_ifs <;> rfl
  · apply Finsupp.sum_congr
    intro r hr
    simp [Fin.forall_iff_succAbove i,
      Fin.prod_univ_succAbove (fun j : Fin 39 => ((r j).totient : ℝ)) i, div_div]

open Classical in
theorem selbergCoefficient_mem_divisorClosure
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ) (d : ι → ℕ)
    (hd : selbergCoefficient y d ≠ 0) :
    d ∈ y.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors)) := by
  unfold selbergCoefficient Finsupp.sum at hd
  obtain ⟨r, hr, hterm⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (mul_ne_zero_iff.mp hd).2
  have hdata := ite_ne_right_iff.mp hterm
  have hden : (∏ j, ((r j).totient : ℝ)) ≠ 0 :=
    (div_ne_zero_iff.mp hdata.2).2
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hr, Fintype.mem_piFinset.mpr ?_⟩
  intro j
  refine Nat.mem_divisors.mpr ⟨hdata.1 j, ?_⟩
  intro hzero
  exact (Finset.prod_ne_zero_iff.mp hden j (Finset.mem_univ j)) (by simp [hzero])

open Classical in
theorem selberg_divisor_sum_weighted_erase
    (i : Fin 39) (y : (Fin 39 → ℕ) →₀ ℝ) (h : Fin 39 → ℕ) (n : ℕ) :
    let z : (Fin 38 → ℕ) →₀ ℝ :=
      y.sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
        (yr / ((r i).totient : ℝ)))
    let D := y.support.biUnion
      (fun r => Fintype.piFinset (fun j => (r j).divisors))
    let E := z.support.biUnion
      (fun r => Fintype.piFinset (fun j => (r j).divisors))
    (∑ d ∈ D,
        if d i = 1 ∧ (∀ j, d j ∣ n + h j) then selbergCoefficient y d else 0) =
      ∑ d ∈ E,
        if ∀ j, d j ∣ n + h (i.succAbove j) then selbergCoefficient z d else 0 := by
  intro z D E
  let f (d : Fin 38 → ℕ) : ℝ :=
    if ∀ j, d j ∣ n + h (i.succAbove j) then selbergCoefficient z d else 0
  let g (d : Fin 39 → ℕ) : ℝ :=
    if d i = 1 ∧ (∀ j, d j ∣ n + h j) then selbergCoefficient y d else 0
  have hcoeff (d : Fin 38 → ℕ) :
      selbergCoefficient z d = selbergCoefficient y (i.insertNth 1 d) :=
    selbergCoefficient_weighted_erase i y d
  have hterm (d : Fin 38 → ℕ) : f d = g (i.insertNth 1 d) := by
    simp [f, g, Fin.forall_iff_succAbove i, hcoeff]
  symm
  change (∑ d ∈ E, f d) = ∑ d ∈ D, g d
  refine Finset.sum_bij_ne_zero (fun d _ _ => i.insertNth 1 d) ?_ ?_ ?_ ?_
  · intro d _ hd
    simpa only [D, Finset.mem_biUnion, Fintype.mem_piFinset] using
      selbergCoefficient_mem_divisorClosure y (i.insertNth 1 d)
        (hcoeff d ▸ (ite_ne_right_iff.mp hd).2)
  · intro d _ _ e _ _ heq
    exact Fin.insertNth_right_injective (α := fun _ => ℕ) (p := i) (1 : ℕ) heq
  · intro d _ hd
    obtain ⟨⟨hdi, _⟩, hyne⟩ := ite_ne_right_iff.mp hd
    let e : Fin 38 → ℕ := fun j => d (i.succAbove j)
    have hrecover : i.insertNth 1 e = d :=
      Fin.insertNth_eq_iff.mpr ⟨hdi.symm, rfl⟩
    have hzne : selbergCoefficient z e ≠ 0 := by
      rw [hcoeff e, hrecover]
      exact hyne
    have hfe : f e ≠ 0 := by
      rw [hterm e, hrecover]
      exact hd
    refine ⟨e, ?_, hfe, hrecover⟩
    simpa only [E, Finset.mem_biUnion, Fintype.mem_piFinset] using
      selbergCoefficient_mem_divisorClosure z e hzne
  · intro d _ _
    exact hterm d

theorem canonical_erased_profile_sum
    (i : Fin 39) (Q : Finset ℕ) (f : (Fin 39 → ℕ) → ℝ) (r : Fin 38 → ℕ) :
    let T := (Fintype.piFinset (fun _ : Fin 39 => Q)).filter
      (fun t => Squarefree (∏ j, t j))
    let y : (Fin 39 → ℕ) →₀ ℝ := ∑ t ∈ T, Finsupp.single t (f t)
    (y.sum (fun t yt => Finsupp.single (fun j => t (i.succAbove j))
      (yt / ((t i).totient : ℝ)))) r =
        ∑ s ∈ Q,
          if Squarefree (s * ∏ j, r j) ∧ (∀ j, r j ∈ Q) then
            f (i.insertNth s r) / (s.totient : ℝ) else 0 := by
  classical
  intro T y
  dsimp only [y]
  rw [Finsupp.sum_finsetSum _ _ _ (fun t => by simp)
    (fun t a b => by simp [add_div, Finsupp.single_add])]
  simp only [Finsupp.sum_single_index, Finsupp.single_zero, zero_div,
    Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hrecover (t : Fin 39 → ℕ)
      (ht : (fun j => t (i.succAbove j)) = r) : t = i.insertNth (t i) r :=
    Fin.eq_insertNth_iff.mpr ⟨rfl, ht⟩
  refine Finset.sum_bij (fun t _ => t i) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨htT, htr⟩ := Finset.mem_filter.mp ht
    obtain ⟨htQ, htSq⟩ := Finset.mem_filter.mp htT
    have hQ := Fintype.mem_piFinset.mp htQ
    refine Finset.mem_filter.mpr ⟨hQ i, ?_, ?_⟩
    · rw [hrecover t htr, Fin.prod_insertNth] at htSq
      exact htSq
    · intro j
      rw [← htr]
      exact hQ (i.succAbove j)
  · intro t ht u hu htu
    calc
      t = i.insertNth (t i) r := hrecover t (Finset.mem_filter.mp ht).2
      _ = i.insertNth (u i) r := by rw [htu]
      _ = u := (hrecover u (Finset.mem_filter.mp hu).2).symm
  · intro s hs
    obtain ⟨hsQ, hsSq, hrQ⟩ := Finset.mem_filter.mp hs
    refine ⟨i.insertNth s r, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      rw [Fin.forall_iff_succAbove i]
      simpa only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using
        And.intro hsQ hrQ
    · simpa only [Fin.prod_insertNth] using hsSq
    · exact Fin.insertNth_comp_succAbove i s r
  · intro t ht
    rw [← hrecover t (Finset.mem_filter.mp ht).2]

open Classical in
theorem selberg39_canonical_erased_face
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ M : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    ∀ᶠ x : ℝ in Filter.atTop,
      let W := presievingModulus 𝓗 x
      let R := x ^ ρ
      let B := fragmentNormalization W R
      let P := fragmentPrimes W R κ
      let q := ∏ p ∈ P, p
      let T := (Fintype.piFinset (fun _ : Fin 39 => q.divisors)).filter
        (fun r => Squarefree (∏ j, r j))
      1 < x ∧ 0 < B ∧
        ∀ F : (Fin 39 → MeasureTheory.FiniteMeasure ℝ) → ℝ,
          (∀ X, |F X| ≤ M) →
          let y : (Fin 39 → ℕ) →₀ ℝ :=
            ∑ r ∈ T, Finsupp.single r
              (F (fun j => primeLogConfiguration R (r j)) / B ^ 39)
          let z : (Fin 38 → ℕ) →₀ ℝ :=
            y.sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
              (yr / ((r i).totient : ℝ)))
          let D := y.support.biUnion
            (fun r => Fintype.piFinset (fun j => (r j).divisors))
          let E := z.support.biUnion
            (fun r => Fintype.piFinset (fun j => (r j).divisors))
          (∀ r : Fin 39 → ℕ,
            y r = if r ∈ T then
              F (fun j => primeLogConfiguration R (r j)) / B ^ 39
            else 0) ∧
          (∀ r : Fin 38 → ℕ,
            z r = B⁻¹ ^ 39 *
              ∑ s ∈ q.divisors,
                if Squarefree (s * ∏ j, r j) ∧ (∀ j, r j ∈ q.divisors) then
                  F (i.insertNth (primeLogConfiguration R s)
                    (fun j => primeLogConfiguration R (r j))) /
                      (s.totient : ℝ)
                else 0) ∧
          (∀ d : Fin 38 → ℕ,
            selbergCoefficient z d = selbergCoefficient y (i.insertNth 1 d)) ∧
          (∀ n : ℕ,
            (∑ d ∈ D,
                if d i = 1 ∧ (∀ j, d j ∣ n + h j) then selbergCoefficient y d else 0) =
              ∑ d ∈ E,
                if ∀ j, d j ∣ n + h (i.succAbove j) then selbergCoefficient z d else 0) ∧
          (∀ r ∈ z.support,
            Squarefree (∏ j, r j) ∧ (∀ j, r j ∈ q.divisors) ∧
              ∃ s ∈ y.support, (fun j => s (i.succAbove j)) = r) ∧
          (∀ r : Fin 38 → ℕ,
            |z r| ≤ M * harmonicFragmentMass W R κ / B ^ 39 ∧
              |z r| ≤ (M * (Real.exp Real.eulerMascheroniConstant * κ + 1)) / B ^ 38) := by
  intro ρ h
  have hρ : 0 < ρ := by norm_num [ρ]
  have hm := harmonic_fragment_normalizer_tendsto 𝓗 ρ κ hρ hκ
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hm.eventually_le_const (lt_add_one _)] with x hx hm
  intro W R B P q T
  have hW : 0 < W := presieving_pos 𝓗 x
  have hB : 0 < B := by
    apply mul_pos
    · exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
    · exact Real.log_pos (Real.one_lt_rpow hx hρ)
  refine ⟨hx, hB, ?_⟩
  intro F hF y z D E
  have hy (r : Fin 39 → ℕ) :
      y r = if r ∈ T then
        F (fun j => primeLogConfiguration R (r j)) / B ^ 39 else 0 := by
    simp [y, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hyT (r : Fin 39 → ℕ) (hr : r ∈ y.support) : r ∈ T := by
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hr) (by rw [hy, ite_eq_right hnot])
  have hzSum (r : Fin 38 → ℕ) :
      z r = B⁻¹ ^ 39 *
        ∑ s ∈ q.divisors,
          if Squarefree (s * ∏ j, r j) ∧ (∀ j, r j ∈ q.divisors) then
            F (i.insertNth (primeLogConfiguration R s)
              (fun j => primeLogConfiguration R (r j))) /
                (s.totient : ℝ) else 0 := by
    have hsum := canonical_erased_profile_sum i q.divisors
      (fun t => F (fun j => primeLogConfiguration R (t j)) / B ^ 39) r
    change z r = _ at hsum
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs
    · have hconfiguration :
          (fun j => primeLogConfiguration R
            (i.insertNth (α := fun _ => ℕ) s r j)) =
            i.insertNth (primeLogConfiguration R s)
              (fun j => primeLogConfiguration R (r j)) := by
        apply Fin.eq_insertNth_iff.mpr
        simp [funext_iff, Fin.removeNth_apply]
      rw [hconfiguration]
      simp only [div_eq_mul_inv, inv_pow]
      ac_rfl
    · simp
  have hzProject (r : Fin 38 → ℕ) (hr : r ∈ z.support) :
      ∃ s ∈ y.support, (fun j => s (i.succAbove j)) = r := by
    have hmem := Finsupp.support_sum hr
    obtain ⟨s, hs, hsr⟩ := Finset.mem_biUnion.mp hmem
    exact ⟨s, hs,
      (Finset.mem_singleton.mp (Finsupp.support_single_subset hsr)).symm⟩
  have hzBound (r : Fin 38 → ℕ) :
      |z r| ≤ M * harmonicFragmentMass W R κ / B ^ 39 := by
    have hnonneg : 0 ≤ B⁻¹ ^ 39 := by positivity
    rw [hzSum, abs_mul, abs_of_nonneg hnonneg]
    calc
      _ ≤ B⁻¹ ^ 39 *
          ∑ s ∈ q.divisors,
            |if Squarefree (s * ∏ j, r j) ∧ (∀ j, r j ∈ q.divisors) then
              F (i.insertNth (primeLogConfiguration R s)
                (fun j => primeLogConfiguration R (r j))) /
                  (s.totient : ℝ) else 0| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hnonneg
      _ ≤ B⁻¹ ^ 39 * ∑ s ∈ q.divisors, M / (s.totient : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        apply Finset.sum_le_sum
        intro s hs
        simp only [abs_ite, abs_div, Nat.abs_cast, abs_zero]
        split_ifs
        · exact div_le_div_of_nonneg_right (hF _) (Nat.cast_nonneg _)
        · exact div_nonneg hM (Nat.cast_nonneg _)
      _ = M * harmonicFragmentMass W R κ / B ^ 39 := by
        change B⁻¹ ^ 39 * (∑ s ∈ q.divisors, M / (s.totient : ℝ)) =
          M * (∑ s ∈ q.divisors, (s.totient : ℝ)⁻¹) / B ^ 39
        simp only [div_eq_mul_inv, ← Finset.mul_sum, inv_pow]
        ac_rfl
  refine ⟨hy, hzSum, selbergCoefficient_weighted_erase i y,
    selberg_divisor_sum_weighted_erase i y h, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, hsr⟩ := hzProject r hr
    obtain ⟨hsQ, hsSq⟩ := Finset.mem_filter.mp (hyT s hs)
    have hQ := Fintype.mem_piFinset.mp hsQ
    refine ⟨?_, ?_, s, hs, hsr⟩
    · rw [← hsr]
      apply hsSq.squarefree_of_dvd
      rw [Fin.prod_univ_succAbove _ i]
      exact dvd_mul_left _ _
    · intro j
      rw [← hsr]
      exact hQ (i.succAbove j)
  · intro r
    refine ⟨hzBound r, (hzBound r).trans ?_⟩
    calc
      M * harmonicFragmentMass W R κ / B ^ 39 =
          (M * (harmonicFragmentMass W R κ / B)) / B ^ 38 := by
        rw [show B ^ 39 = B * B ^ 38 from pow_succ' B 38, div_mul_eq_div_div,
          mul_div_assoc]
      _ ≤ (M * (Real.exp Real.eulerMascheroniConstant * κ + 1)) / B ^ 38 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hM)
          (pow_nonneg hB.le _)

end PrimeGap182.Selberg

section
open Set

end

section
open Set
open scoped ContDiff

end

namespace PrimeGap182.Selberg

section
open Set
open scoped ContDiff

theorem measure_frontier_superlevel_eq_zero {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : Measure E) (f : E → ℝ) (t : ℝ)
    (hf : ∀ᵐ z ∂μ, ContinuousAt f z) (ht : μ {z | f z = t} = 0) :
    μ (frontier {z | t ≤ f z}) = 0 := by
  have he : ∀ᵐ z ∂μ, f z ≠ t := by
    apply ae_iff.mpr
    simpa only [ne_eq, not_not, Set.ofPred_mem_eq] using ht
  have hn : ∀ᵐ z ∂μ, z ∉ frontier {z | t ≤ f z} := by
    filter_upwards [hf, he] with z hz hz'
    rcases lt_or_gt_of_ne hz' with h | h
    · have hi : z ∈ interior ({z | t ≤ f z}ᶜ) := mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hz (isOpen_Iio.mem_nhds h)) (by
          intro v hv hh; exact (not_le_of_gt (show f v < t from hv)) hh))
      have := (mem_interior_iff_notMem_frontier (interior_subset hi)).mp hi
      simpa only [frontier_compl] using this
    · have hi : z ∈ interior {z | t ≤ f z} := mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hz (isOpen_Ioi.mem_nhds h)) (by
          intro v hv; exact le_of_lt (show t < f v from hv)))
      exact (mem_interior_iff_notMem_frontier (interior_subset hi)).mp hi
  simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp hn)

/--
Weak convergence of probability measures gives convergence of integrals against a bounded
measurable function that is continuous almost everywhere for the limiting measure.
-/
theorem tendsto_integral_of_weak_convergence {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hw : Tendsto μ l (𝓝 ν)) (f : E → ℝ) (hf : Measurable f)
    (hb : Bornology.IsBounded (Set.range f))
    (hc : ∀ᵐ z ∂(ν : Measure E), ContinuousAt f z) :
    Tendsto (fun x => ∫ z, f z ∂(μ x : Measure E)) l (𝓝 (∫ z, f z ∂(ν : Measure E))) := by
  classical
  obtain ⟨C, _hC, hCb⟩ := hb.exists_pos_norm_le
  have hfB (z) : ‖f z‖ ≤ C := hCb _ ⟨z, rfl⟩
  let u := fun z => f z + C
  have um : Measurable u := hf.add_const _
  have u0 z : 0 ≤ u z := by
    have := hfB z; rw [Real.norm_eq_abs] at this
    dsimp [u]
    linarith [neg_le_of_abs_le this]
  have uM z : u z ≤ 2*C := by
    have := hfB z; rw [Real.norm_eq_abs] at this
    dsimp [u]; linarith [le_of_abs_le this]
  have fi (η : Measure E) [IsFiniteMeasure η] : Integrable f η :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hfB)
  have ui (η : Measure E) [IsFiniteMeasure η] : Integrable u η :=
    (fi η).add (integrable_const C)
  have uc : ∀ᵐ z ∂(ν : Measure E), ContinuousAt u z := hc.mono
    (fun _ h => h.add continuousAt_const)
  have lev : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) (2*C)),
      (ν : Measure E) (frontier {z | t ≤ u z}) = 0 := by
    have exc := (Measure.countable_meas_level_set_pos (μ := (ν : Measure E)) um).ae_notMem
      (volume : Measure ℝ)
    filter_upwards [ae_restrict_of_ae exc] with t h
    exact measure_frontier_superlevel_eq_zero _ u t uc (not_lt.mp h |>.antisymm (bot_le))
  have meas (η : Measure E) [IsFiniteMeasure η] : Measurable
      (fun t : ℝ => η.real {z | t ≤ u z}) :=
    Antitone.measurable (fun _ _ h => ENNReal.toReal_mono
      (measure_ne_top _ _) (measure_mono (fun _ hv => le_trans h hv)))
  have hl : Tendsto (fun x => ∫ t in Ioc (0 : ℝ) (2*C),
      (μ x : Measure E).real {z | t ≤ u z}) l
      (𝓝 (∫ t in Ioc (0 : ℝ) (2*C), (ν : Measure E).real {z | t ≤ u z})) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    · exact Eventually.of_forall (fun x => (meas _).aestronglyMeasurable)
    · refine Eventually.of_forall (fun x => .of_forall (fun t => ?_))
      have h0 : 0 ≤ (μ x : Measure E).real {z | t ≤ u z} := by positivity
      rw [Real.norm_of_nonneg h0]
      have hx : (μ x : Measure E) Set.univ = 1 := measure_univ
      simpa only [measureReal_def, hx, ENNReal.toReal_one] using
        ENNReal.toReal_mono (by simp : (μ x : Measure E) Set.univ ≠ ⊤)
          (measure_mono (subset_univ {z | t ≤ u z}) :
            (μ x : Measure E) {z | t ≤ u z} ≤ (μ x : Measure E) Set.univ)
    · exact integrable_const 1
    · filter_upwards [lev] with t ht
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
        (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hw ht)
  have hlU : Tendsto (fun x => ∫ z, u z ∂(μ x : Measure E)) l
      (𝓝 (∫ z, u z ∂(ν : Measure E))) := by
    simpa only [(ui _).integral_eq_integral_Ioc_meas_le
        (Filter.Eventually.of_forall u0) (Filter.Eventually.of_forall uM)] using hl
  simpa only [u, integral_add (fi _) (integrable_const C), integral_const,
    probReal_univ, one_smul, add_sub_cancel_right] using hlU.sub_const C

theorem measure_pi_nnreal_smul {E : Type*} [MeasurableSpace E] (n : ℕ)
    (P : Measure E) [IsFiniteMeasure P] (b : ℝ≥0) :
    Measure.pi (fun _ : Fin n => b • P) =
      ((b : ℝ≥0∞) ^ n) • Measure.pi (fun _ : Fin n => P) := by
  apply Measure.pi_eq
  intro t ht
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem tendsto_integral_pi_smul {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [TopologicalSpace.PseudoMetrizableSpace E]
    (n : ℕ) (P : ℝ → ProbabilityMeasure E) (P₀ : ProbabilityMeasure E)
    (b : ℝ → ℝ≥0) (b₀ : ℝ≥0) (hb₀ : b₀ ≠ 0)
    (hP : Tendsto P atTop (𝓝 P₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (f : (Fin n → E) → ℝ) (hf : Measurable f)
    (hfB : Bornology.IsBounded (Set.range f))
    (hfC : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => b₀ • (P₀ : Measure E)), ContinuousAt f z) :
    Tendsto
      (fun x => ∫ z, f z ∂Measure.pi (fun _ : Fin n => b x • (P x : Measure E))) atTop
      (𝓝 (∫ z, f z ∂Measure.pi (fun _ : Fin n => b₀ • (P₀ : Measure E)))) := by
  have hw : Tendsto (fun x => ProbabilityMeasure.pi (fun _ : Fin n => P x)) atTop
      (𝓝 (ProbabilityMeasure.pi (fun _ : Fin n => P₀))) :=
    (ProbabilityMeasure.continuous_pi.tendsto _).comp (tendsto_pi_nhds.2 (fun _ => hP))
  have hc : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => (P₀ : Measure E)), ContinuousAt f z := by
    rw [measure_pi_nnreal_smul] at hfC
    exact (Measure.ae_ennreal_smul_measure_iff
      (pow_ne_zero _ (by exact_mod_cast hb₀))).mp hfC
  have hw' := tendsto_integral_of_weak_convergence hw f hf hfB hc
  have hs := (((NNReal.continuous_coe.tendsto b₀).comp hb).pow n).mul hw'
  simpa only [measure_pi_nnreal_smul, integral_smul_measure, ENNReal.toReal_pow,
    ENNReal.coe_toReal, smul_eq_mul, Function.comp_def, ProbabilityMeasure.toMeasure_pi] using hs

open Classical in
theorem measure_pi_sum_dirac_eq {E α : Type*} [MeasurableSpace E] (n : ℕ)
    (Q : Finset α) (w : α → ℝ≥0) (u : α → E) :
    Measure.pi (fun _ : Fin n => (∑ s ∈ Q, w s • Measure.dirac (u s))) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Q),
        (∏ j, w (r j)) • Measure.dirac (fun j => u (r j)) := by
  apply Measure.pi_eq
  intro t ht
  have htp : MeasurableSet (Set.univ.pi t) := MeasurableSet.univ_pi ht
  simp only [Measure.finsetSum_apply, Measure.coe_nnreal_smul_apply,
    Measure.dirac_apply' _ htp, Measure.dirac_apply' _ (ht _)]
  simp_rw [show (Set.univ : Set (Fin n)) = (Finset.univ : Finset (Fin n)) from (by ext; simp),
    Set.indicator_pi_one_apply]
  simp_rw [ENNReal.ofNNReal_finsetProd]
  have hp (z : Fin n → α) := Finset.prod_mul_distrib
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n => (w (z i) : ℝ≥0∞)) (g := fun i => (t i).indicator 1 (u (z i)))
  simp_rw [← hp]
  exact Eq.symm (Finset.prod_univ_sum _
    (fun j : Fin n => fun z : α => (w z : ℝ≥0∞) * (t j).indicator 1 (u z)))

open Classical in
theorem integral_mix_pi {E α : Type*} [MeasurableSpace E]
    (n : ℕ) (Q : Finset α) (w : α → ℝ≥0) (u : α → E) (f : (Fin n → E) → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ z, f z ∂Measure.pi (fun _ : Fin n => ∑ s ∈ Q, w s • Measure.dirac (u s))) =
    ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Q),
      (∏ j, (w (r j) : ℝ)) * f (fun j => u (r j)) := by
  rw [measure_pi_sum_dirac_eq n Q, integral_finsetSum_measure]
  · simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, NNReal.coe_prod,
      integral_dirac' _ _ hf]
  · intro r _
    exact (integrable_dirac' hf (by finiteness)).smul_measure_nnreal

theorem harmonicConfigurationMass_map_fragmentBandMasses_eq_sum_dirac {m : ℕ}
    (a : Fin (m + 2) → ℝ) (W : ℕ) (R κ : ℝ) :
    ((harmonicConfigurationMass W R κ).map
      (fragmentBandMasses a) : Measure (Fin (m + 1) → ℝ)) =
      ∑ s ∈ (∏ p ∈ fragmentPrimes W R κ, p).divisors,
        ((Nat.totient s : ℝ)⁻¹).toNNReal •
          Measure.dirac (fragmentBandMasses a
            (primeLogConfiguration R s)) := by
  apply Measure.ext
  intro t ht
  rw [FiniteMeasure.toMeasure_map, Measure.map_apply
    (measurable_fragmentBandMasses a) ht]
  let atom (s : ℕ) : FiniteMeasure (FiniteMeasure ℝ) :=
    ⟨Measure.dirac (primeLogConfiguration R s), inferInstance⟩
  have ha (s : ℕ) :
      (((((s.totient : ℝ)⁻¹).toNNReal • atom s) : FiniteMeasure (FiniteMeasure ℝ)) :
        Measure (FiniteMeasure ℝ)) =
          ((s.totient : ℝ)⁻¹).toNNReal •
            Measure.dirac (primeLogConfiguration R s) := by
    rw [FiniteMeasure.toMeasure_smul]
    rfl
  change ((↑(∑ s ∈ (∏ p ∈ fragmentPrimes W R κ, p).divisors,
      ((s.totient : ℝ)⁻¹).toNNReal • atom s) : Measure (FiniteMeasure ℝ))
        (fragmentBandMasses a ⁻¹' t)) = _
  rw [FiniteMeasure.toMeasure_sum]
  simp_rw [Measure.finsetSum_apply, ha, Measure.coe_nnreal_smul_apply,
    Measure.dirac_apply' _ ((measurable_fragmentBandMasses a) ht),
    Measure.dirac_apply' _ ht]
  rfl

theorem fragmentNormalization_pos (H : Finset ℕ) (x R : ℝ) (hR : 1 < R) :
    0 < fragmentNormalization (presievingModulus H x) R := by
  have hw : 0 < presievingModulus H x := presieving_pos H x
  exact mul_pos (div_pos (by exact_mod_cast Nat.totient_pos.mpr hw)
    (by exact_mod_cast hw)) (Real.log_pos hR)

theorem tendsto_harmonic_pi_sum {m : ℕ}
    (H : Finset ℕ) (ρ κ : ℝ) (a : Fin (m + 2) → ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (m + 1)) = κ) (n : ℕ)
    (K : (Fin n → Fin (m + 1) → ℝ) → ℝ)
    (hK : Measurable K) (hKb : Bornology.IsBounded (Set.range K))
    (hKc : ∀ᵐ Y ∂Measure.pi (fun _ : Fin n =>
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)),
      ContinuousAt K Y) :
    let R : ℝ → ℝ := fun x => x ^ ρ
    let W := presievingModulus H
    let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → Finset ℕ := fun x =>
      (∏ p ∈ fragmentPrimes (W x) (R x) κ, p).divisors
    let u : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s => fragmentBandMasses a
      (primeLogConfiguration (R x) s)
    Filter.Tendsto (fun x : ℝ => (B x ^ n)⁻¹ *
      ∑ r ∈ Fintype.piFinset (fun _ : Fin n => q x), (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
          K (fun j => u x (r j))) Filter.atTop
      (𝓝 (∫ Y, K Y ∂Measure.pi (fun _ : Fin n =>
        ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
          Measure.map (fragmentBandMasses a) (fragmentLaw κ)))) := by
  classical
  intro R W B q u
  let P : ProbabilityMeasure (FiniteMeasure ℝ) :=
    ⟨fragmentLaw κ, fragmentLaw_isProbabilityMeasure κ⟩
  let L := P.toFiniteMeasure.map (fragmentBandMasses a)
  let P₀ := L.normalize
  let V : ℝ → FiniteMeasure (Fin (m + 1) → ℝ) := fun x =>
    (harmonicConfigurationMass (W x) (R x) κ).map (fragmentBandMasses a)
  let b : ℝ → ℝ≥0 := fun x =>
    (harmonicFragmentMass (W x) (R x) κ / B x).toNNReal
  let b₀ : ℝ≥0 := (Real.exp Real.eulerMascheroniConstant * κ).toNNReal
  have hL : P₀.toFiniteMeasure = L := by
    dsimp [P₀, L]
    rw [FiniteMeasure.normalize_map _ P.toFiniteMeasure_nonzero
      (measurable_fragmentBandMasses a),
      ProbabilityMeasure.toFiniteMeasure_normalize_eq_self]
    apply FiniteMeasure.toMeasure_injective
    rfl
  have hν : ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
          Measure.map (fragmentBandMasses a) (fragmentLaw κ) =
        b₀ • (P₀ : Measure (Fin (m + 1) → ℝ)) := by
    have hP₀ : (P₀ : Measure (Fin (m + 1) → ℝ)) = (L : Measure (Fin (m + 1) → ℝ)) :=
      congrArg (fun z : FiniteMeasure (Fin (m + 1) → ℝ) => (z : Measure (Fin (m + 1) → ℝ))) hL
    rw [hP₀]
    change (ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ)) •
      (Measure.map (fragmentBandMasses a) (P : Measure _)) =
      (b₀ : ℝ≥0∞) • (Measure.map (fragmentBandMasses a) (P : Measure _))
    have hb : (b₀ : ℝ≥0∞) = ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (mul_pos (Real.exp_pos _) hκ).le]
      congr 1
      apply Subtype.ext
      simp [b₀, Real.toNNReal_of_nonneg (mul_pos (Real.exp_pos _) hκ).le]
    rw [← hb]
  have hw := harmonic_fragment_band_vector_tendsto
    H ρ κ a hρ hκ ha ha0 ha1
  have hp : Tendsto (fun x => (V x).normalize) atTop (𝓝 P₀) := hw.fst_nhds
  have hb : Tendsto b atTop (𝓝 b₀) := tendsto_real_toNNReal
    (harmonic_fragment_normalizer_tendsto H ρ κ hρ hκ)
  have hb0 : b₀ ≠ 0 := by
    apply ne_of_gt
    exact Real.toNNReal_pos.mpr (mul_pos (Real.exp_pos _) hκ)
  rw [hν] at hKc ⊢
  have ht := tendsto_integral_pi_smul n (fun x => (V x).normalize) P₀ b b₀ hb0 hp hb K hK hKb hKc
  apply ht.congr'
  filter_upwards [(tendsto_rpow_atTop hρ).eventually_gt_atTop 1] with x hx
  have hB : 0 < B x := fragmentNormalization_pos H x (R x) hx
  have hVm : (V x).mass.toReal = harmonicFragmentMass (W x) (R x) κ := by
    dsimp [V]
    rw [FiniteMeasure.mass_map_of_aemeasurable _
        (measurable_fragmentBandMasses a).aemeasurable,
      harmonicConfigurationMass_mass]
  have heq : (b x) • ( (V x).normalize : Measure (Fin (m + 1) → ℝ)) =
      ((B x)⁻¹).toNNReal • (V x : Measure (Fin (m + 1) → ℝ)) := by
    have ht' := FiniteMeasure.inv_toNNReal_smul_eq_mass_div_smul_normalize (V x) (B x)
    apply Eq.symm
    have ht'' := congrArg (fun z : FiniteMeasure (Fin (m + 1) → ℝ) =>
      (z : Measure (Fin (m + 1) → ℝ))) ht'
    simpa only [FiniteMeasure.toMeasure_smul,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure, hVm, b]
      using ht''
  calc
    _ = (∫ z, K z ∂Measure.pi (fun _ : Fin n =>
      ((B x)⁻¹).toNNReal • (∑ s ∈ q x,
        ((Nat.totient s : ℝ)⁻¹).toNNReal • Measure.dirac (u x s)))) := by
      congr 2
      apply funext
      intro j
      rw [heq]
      rw [harmonicConfigurationMass_map_fragmentBandMasses_eq_sum_dirac]
    _ = _ := by
      simp_rw [Finset.smul_sum, smul_smul]
      rw [integral_mix_pi n _ _ _ K hK.stronglyMeasurable]
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr hB.le),
        Real.coe_toNNReal _ (inv_nonneg.mpr (Nat.cast_nonneg _)), Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow, ← Finset.mul_sum,
        mul_assoc]

open Classical in
theorem exists_shared_prime_of_not_squarefree_prod {ι : Type*} [Fintype ι]
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (r : ι → ℕ)
    (hr : ∀ j, r j ∈ (∏ p ∈ S, p).divisors) (h : ¬ Squarefree (∏ j, r j)) :
    ∃ j k, j ≠ k ∧ ∃ p ∈ S, p ∣ r j ∧ p ∣ r k := by
  by_contra! hn
  apply h
  have hq : Squarefree (∏ p ∈ S, p) := squarefree_prime_prod S hS
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro j _ k _ hjk
    apply Nat.coprime_iff_isRelPrime.mp
    apply Nat.coprime_of_dvd
    intro p hp hj hk
    have hpd : p ∣ ∏ q ∈ S, q := dvd_trans hj (Nat.mem_divisors.mp (hr j)).1
    have hpS : p ∈ S := by
      rw [← Nat.primeFactors_prod hS]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpd, hq.ne_zero⟩
    exact hn j k hjk p hpS hj hk
  · intro j _
    exact hq.squarefree_of_dvd (Nat.mem_divisors.mp (hr j)).1

theorem reciprocal_totient_product_sum_shared_prime_eq_div_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (j k : ι) (hjk : j ≠ k)
    (p : ℕ) (hpS : p ∈ S) :
    let Q := (∏ p ∈ S, p).divisors
    let M : ℝ := ∑ s ∈ Q, (Nat.totient s : ℝ)⁻¹
    (∑ r ∈ Fintype.piFinset (fun _ : ι => Q),
      (∏ l, (Nat.totient (r l) : ℝ)⁻¹) *
        (if p ∣ r j ∧ p ∣ r k then 1 else 0)) = M ^ (Fintype.card ι) / (p : ℝ) ^ 2 := by
  classical
  intro Q M
  let A := ({j, k} : Finset ι)
  let u := fun l s => if l ∈ A then
      (Nat.totient s : ℝ)⁻¹ * (if p ∣ s then (1 : ℝ) else 0) else (Nat.totient s : ℝ)⁻¹
  have hu (l : ι) (s : ℕ) : u l s =
      (Nat.totient s : ℝ)⁻¹ * (if l ∈ A → p ∣ s then 1 else 0) := by
    by_cases hl : l ∈ A <;> simp [u, hl]
  have hv (r : ι → ℕ) : (∏ l, u l (r l)) = (∏ l, (Nat.totient (r l) : ℝ)⁻¹) *
      (if p ∣ r j ∧ p ∣ r k then 1 else 0) := by
    simp only [hu, Finset.prod_mul_distrib, Fintype.prod_boole]
    simp [A, or_imp, forall_and]
  simp_rw [← hv]
  rw [Finset.sum_prod_piFinset]
  have hs (l : ι) : (∑ d ∈ Q, u l d) = M * (if l ∈ A then (p : ℝ)⁻¹ else 1) := by
    by_cases hl : l ∈ A
    · simp only [u, hl, ↓reduceIte, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, marked_reciprocal_totient_sum S hS hpS]
      simp only [M, Q, div_eq_mul_inv]
    · simp [u, hl, M]
  simp_rw [hs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Finset.prod_ite_mem_eq]
  simp [A, hjk, pow_two, div_eq_mul_inv, mul_inv_rev]

theorem bad_configuration_indicator_le_shared_prime_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (ok : (ι → ℕ) → Prop) [DecidablePred ok]
    (hwit : ∀ r, (∀ j, r j ∈ (∏ p ∈ S, p).divisors) → ¬ ok r →
      ∃ j k, j ≠ k ∧ ∃ p ∈ S, p ∣ r j ∧ p ∣ r k)
    (r : ι → ℕ) (hr : r ∈ Fintype.piFinset (fun _ : ι => (∏ p ∈ S, p).divisors)) :
    (if ok r then (0 : ℝ) else 1) ≤
      ∑ j, ∑ k ∈ Finset.univ.filter (fun k : ι => j ≠ k),
        ∑ p ∈ S, (if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0) := by
  classical
  have non (j k) (p) : 0 ≤ (if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases hh : ok r
  · simp only [ite_eq_left hh]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun p _ => non j k p)))
  · rw [ite_eq_right hh]
    obtain ⟨j,k,hne,p,hpS,hj,hk⟩ := hwit r (Fintype.mem_piFinset.mp hr) hh
    calc
      (1 : ℝ) = (if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0) := (ite_eq_left ⟨hj,hk⟩).symm
      _ ≤ ∑ p ∈ S, if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun z : ℕ => if z ∣ r j ∧ z ∣ r k then (1 : ℝ) else 0)
          (fun _ _ => non j k _) hpS
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k : ι => j ≠ k),
          ∑ p ∈ S, if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0 := Finset.single_le_sum
            (f := fun b => ∑ p ∈ S, if p ∣ r j ∧ p ∣ r b then (1 : ℝ) else 0)
            (by intro b _; exact Finset.sum_nonneg (fun p _ => non j b p))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩)
      _ ≤ ∑ j, ∑ k ∈ Finset.univ.filter (fun k : ι => j ≠ k),
          ∑ p ∈ S, if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0 := Finset.single_le_sum
            (f := fun b => ∑ k ∈ Finset.univ.filter (fun k : ι => b ≠ k),
              ∑ p ∈ S, if p ∣ r b ∧ p ∣ r k then (1 : ℝ) else 0)
            (by intro b _; exact Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
                (fun p _ => non b k p))) (Finset.mem_univ j)

theorem sum_shared_prime_weights_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    let Q := (∏ p ∈ S, p).divisors
    let T := Fintype.piFinset (fun _ : ι => Q)
    let M := (∑ s ∈ Q, (Nat.totient s : ℝ)⁻¹)
    (∑ r ∈ T, (∏ l, (Nat.totient (r l) : ℝ)⁻¹) *
      (∑ j, ∑ k ∈ Finset.univ.filter (fun k : ι => j ≠ k), ∑ p ∈ S,
        (if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0))) ≤
      (Fintype.card ι : ℝ) ^ 2 * M ^ (Fintype.card ι) * (∑ p ∈ S, 1 / (p : ℝ) ^ 2) := by
  classical
  intro Q T M
  have h0 : 0 ≤ M := Finset.sum_nonneg fun s _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    _ = ∑ j, ∑ k ∈ Finset.univ.filter (fun k : ι => j ≠ k), ∑ p ∈ S,
        ∑ r ∈ T, (∏ l, (Nat.totient (r l) : ℝ)⁻¹) *
          (if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext j
      rw [Finset.sum_comm]
      congr 1
      funext k
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k ∈ Finset.univ.filter (fun k : ι => j ≠ k), ∑ p ∈ S,
        M ^ (Fintype.card ι) / (p : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro p hp
      exact reciprocal_totient_product_sum_shared_prime_eq_div_sq S hS j k
        (Finset.mem_filter.mp hk).2 p hp
    _ ≤ ∑ j : ι, ∑ _k : ι, ∑ p ∈ S, M ^ (Fintype.card ι) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun k : ι => j ≠ k) Finset.univ)
        (by intro k _ _; exact Finset.sum_nonneg (fun p _ =>
          div_nonneg (pow_nonneg h0 _) (sq_nonneg _)))
    _ = _ := by simp [div_eq_mul_inv, ← Finset.mul_sum, pow_two]; ring

theorem harmonic_restriction_error_le_shared_prime_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (ok : (ι → ℕ) → Prop) [DecidablePred ok]
    (hwit : ∀ r, (∀ j, r j ∈ (∏ p ∈ S, p).divisors) → ¬ ok r →
      ∃ j k, j ≠ k ∧ ∃ p ∈ S, p ∣ r j ∧ p ∣ r k)
    (f : (ι → ℕ) → ℝ) (C : ℝ) (hf : ∀ r, ‖f r‖ ≤ C) :
    let Q := (∏ p ∈ S, p).divisors
    let T := Fintype.piFinset (fun _ : ι => Q)
    let M := (∑ s ∈ Q, (Nat.totient s : ℝ)⁻¹)
    ‖(∑ r ∈ T, (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * (if ok r then f r else 0)) -
      (∑ r ∈ T, (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * f r)‖ ≤
      C * (Fintype.card ι : ℝ) ^ 2 * M ^ (Fintype.card ι) * ∑ p ∈ S, 1 / (p : ℝ) ^ 2 := by
  classical
  intro Q T M
  have C0 : 0 ≤ C := (norm_nonneg (f (fun _ => 1))).trans (hf _)
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ T, ‖(∏ j, (Nat.totient (r j) : ℝ)⁻¹) * (if ok r then f r else 0) -
          (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * f r‖ := norm_sum_le _ _
    _ ≤ C * (∑ r ∈ T, (∏ l, (Nat.totient (r l) : ℝ)⁻¹) *
        (∑ j, ∑ k ∈ Finset.univ.filter (fun k : ι => j ≠ k),
          ∑ p ∈ S, (if p ∣ r j ∧ p ∣ r k then (1 : ℝ) else 0))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hp : 0 ≤ ∏ j, (Nat.totient (r j) : ℝ)⁻¹ := Finset.prod_nonneg
        (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      by_cases hgood : ok r
      · simp only [ite_eq_left hgood, sub_self, norm_zero]
        apply mul_nonneg C0
        apply mul_nonneg hp
        apply Finset.sum_nonneg; intro j hj
        apply Finset.sum_nonneg; intro k hk
        exact Finset.sum_nonneg (fun p _ => by split_ifs <;> norm_num)
      · simp only [ite_eq_right hgood, mul_zero, zero_sub, norm_neg, norm_mul]
        rw [Real.norm_eq_abs, abs_of_nonneg hp]
        calc
          _ ≤ (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * C := by gcongr; exact hf r
          _ = C * (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * 1 := by ring
          _ ≤ _ := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
              (by simpa only [ite_eq_right hgood] using
                bad_configuration_indicator_le_shared_prime_count S ok hwit r hr)
                (mul_nonneg C0 hp)
    _ ≤ _ := by
      have hz := mul_le_mul_of_nonneg_left (sum_shared_prime_weights_le (ι := ι) S hS) C0
      simpa only [T, Q, M, mul_assoc] using hz

theorem fragmentPrimes_sum_inv_sq_le_presieved_prime_tail (H : Finset ℕ) (x R κ : ℝ) :
    (∑ p ∈ fragmentPrimes (presievingModulus H x)
        R κ, 1 / (p : ℝ) ^ 2) ≤
      ∑' p : ℕ, if Nat.Prime p ∧ ¬ p ∣ presievingModulus H x
        then 1 / (p : ℝ) ^ 2 else 0 := by
  classical
  let g : ℕ → ℝ := fun p => if Nat.Prime p ∧
      ¬ p ∣ presievingModulus H x then 1/(p : ℝ) ^ 2 else 0
  have hsum : Summable (fun p : ℕ => 1 / (p : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hg : Summable g := Summable.of_nonneg_of_le
    (fun _ => by dsimp [g]; split_ifs <;> positivity)
    (fun p => by dsimp [g]; split_ifs <;> simp)
    hsum
  calc
    _ = ∑ p ∈ fragmentPrimes (presievingModulus H x)
        R κ, g p := by
      apply Finset.sum_congr rfl
      intro p hp
      have h := Finset.mem_filter.mp hp
      simp [g, Nat.prime_of_mem_primesLE h.1, h.2]
    _ ≤ _ := hg.sum_le_tsum _ fun p _ => by dsimp [g]; split_ifs <;> positivity

open Classical in
theorem normalized_harmonic_restriction_error_le {n : ℕ} (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (ok : (Fin n → ℕ) → Prop) [DecidablePred ok]
    (hok : ∀ r, (∀ j, r j ∈ (∏ p ∈ S, p).divisors) → ¬ ok r →
      ∃ j k, j ≠ k ∧ ∃ p ∈ S, p ∣ r j ∧ p ∣ r k)
    (K : (Fin n → ℕ) → ℝ) (C : ℝ) (hK : ∀ r, ‖K r‖ ≤ C)
    (B : ℝ) (hB : 0 < B) :
    ‖(B ^ n)⁻¹ * (∑ r ∈ Fintype.piFinset (fun _ : Fin n => (∏ p ∈ S, p).divisors),
      (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * (if ok r then K r else 0)) -
     (B ^ n)⁻¹ * (∑ r ∈ Fintype.piFinset (fun _ : Fin n => (∏ p ∈ S, p).divisors),
      (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * K r)‖ ≤
      (B ^ n)⁻¹ * (C * (Fintype.card (Fin n) : ℝ) ^ 2 *
        ((∑ d ∈ (∏ p ∈ S, p).divisors, (d.totient : ℝ)⁻¹)) ^ n *
        ∑ p ∈ S, 1/(p : ℝ) ^ 2) := by
  rw [← mul_sub, norm_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hB.le _))]
  classical
  exact mul_le_mul_of_nonneg_left (by simpa only [Fintype.card_fin] using
    (harmonic_restriction_error_le_shared_prime_tail (ι := Fin n) S hS ok hok K C hK))
    (inv_nonneg.mpr (pow_nonneg hB.le _))

/--
The harmonic product-sum limit is unchanged by a restriction whose excluded configurations must
share a prime factor between distinct coordinates.
-/
theorem tendsto_restricted_harmonic_pi_sum {m n : ℕ}
    (Hs : Finset ℕ) (ρ κ : ℝ) (a : Fin (m + 2) → ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (m + 1)) = κ)
    (ok : (Fin n → ℕ) → Prop) [DecidablePred ok]
    (hok : ∀ (S : Finset ℕ), (∀ p ∈ S, Nat.Prime p) →
      ∀ r, (∀ j, r j ∈ (∏ p ∈ S, p).divisors) → ¬ ok r →
        ∃ j k, j ≠ k ∧ ∃ p ∈ S, p ∣ r j ∧ p ∣ r k)
    (K : (Fin n → Fin (m + 1) → ℝ) → ℝ)
    (hK : Measurable K) (hKb : Bornology.IsBounded (Set.range K))
    (hKc : ∀ᵐ Y ∂Measure.pi (fun _ : Fin n =>
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)),
      ContinuousAt K Y) :
    let R : ℝ → ℝ := fun x => x ^ ρ
    let W := presievingModulus Hs
    let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → Finset ℕ := fun x =>
      (∏ p ∈ fragmentPrimes (W x) (R x) κ, p).divisors
    let u : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s => fragmentBandMasses a
      (primeLogConfiguration (R x) s)
    Filter.Tendsto (fun x : ℝ => (B x ^ n)⁻¹ *
      ∑ r ∈ Fintype.piFinset (fun _ : Fin n => q x), (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
        (if ok r then K (fun j => u x (r j)) else 0)) Filter.atTop
      (𝓝 (∫ Y, K Y ∂Measure.pi (fun _ : Fin n =>
        ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
          Measure.map (fragmentBandMasses a) (fragmentLaw κ)))) := by
  classical
  intro R W B q u
  obtain ⟨C, Cpos, hC⟩ := hKb.exists_pos_norm_le
  let good := fun x : ℝ => (B x ^ n)⁻¹ *
    ∑ r ∈ Fintype.piFinset (fun _ : Fin n => q x), (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
      (if ok r then K (fun j => u x (r j)) else 0)
  let full := fun x : ℝ => (B x ^ n)⁻¹ *
    ∑ r ∈ Fintype.piFinset (fun _ : Fin n => q x), (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
       K (fun j => u x (r j))
  have hfull : Tendsto full atTop
      (𝓝 (∫ Y, K Y ∂Measure.pi (fun _ : Fin n =>
        ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
          Measure.map (fragmentBandMasses a) (fragmentLaw κ)))) :=
    tendsto_harmonic_pi_sum Hs ρ κ a hρ hκ ha ha0 ha1 n K hK hKb hKc
  let M := fun x => harmonicFragmentMass (W x) (R x) κ
  let tail := fun x => ∑' p : ℕ,
      if Nat.Prime p ∧ ¬ p ∣ W x then 1/(p : ℝ) ^ 2 else 0
  let err := fun x => C * (Fintype.card (Fin n) : ℝ) ^ 2 * (M x / B x) ^ n * tail x
  have ht : Tendsto err atTop (𝓝 0) := by
    have h := ((harmonic_fragment_normalizer_tendsto
      Hs ρ κ hρ hκ).pow n).const_mul (C * (Fintype.card (Fin n) : ℝ) ^ 2)
    simpa only [err, M, W, R, B, mul_zero] using
      h.mul (presieved_prime_square_tail_tendsto Hs)
  have hd : ∀ᶠ x : ℝ in atTop, ‖good x - full x‖ ≤ err x := by
    filter_upwards [(tendsto_rpow_atTop hρ).eventually_gt_atTop 1] with x hx
    have hB := fragmentNormalization_pos Hs x (R x) hx
    let S := fragmentPrimes (W x) (R x) κ
    have hS : ∀ p ∈ S, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hpnt := normalized_harmonic_restriction_error_le S hS ok (hok S hS)
      (fun r => K fun j => u x (r j)) C (fun r => hC _ ⟨_, rfl⟩) (B x) hB
    change ‖good x - full x‖ ≤ _
    have ht' : (∑ p ∈ S, 1/(p : ℝ) ^ 2) ≤ tail x :=
    fragmentPrimes_sum_inv_sq_le_presieved_prime_tail Hs x (R x) κ
    have MM : 0 ≤ M x := Finset.sum_nonneg (fun s _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    calc
      _ ≤ (B x ^ n)⁻¹ * (C * (Fintype.card (Fin n) : ℝ) ^ 2 * M x ^ n *
              ∑ p ∈ S, 1/(p : ℝ) ^ 2) := hpnt
      _ ≤ (B x ^ n)⁻¹ * (C * (Fintype.card (Fin n) : ℝ) ^ 2 * M x ^ n * tail x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht'
          (mul_nonneg (mul_nonneg Cpos.le (sq_nonneg _)) (pow_nonneg MM n)))
          (inv_nonneg.mpr (pow_nonneg hB.le n))
      _ = err x := by simp only [err, div_pow]; ring
  have hz : Tendsto (fun x => good x - full x) atTop (𝓝 0) := squeeze_zero_norm' hd ht
  simpa [good, sub_add_cancel] using hz.add hfull

theorem sum_pi_snoc {n : ℕ} (Q : Finset ℕ) (f : (Fin (n + 1) → ℕ) → ℝ) :
    (∑ u ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Q), f u) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Q), ∑ s ∈ Q, f (Fin.snoc r s) := by
  classical
  have hf : Fintype.piFinset (fun _ : Fin (n + 1) => Q) =
      { r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Q) | True } := by simp
  rw [hf, Finset.filter_piFinset_eq_map_snocEquiv
    (fun _ : Fin (n + 1) => Q) (fun _ => True)]
  simp only [Finset.filter_true, Finset.sum_map, Finset.sum_product]
  rw [Finset.sum_comm]
  change (∑ x ∈ Fintype.piFinset (fun _ : Fin n => Q), ∑ s ∈ Q, f (Fin.snoc x s)) = _
  rfl

theorem squarefree_prod_of_squarefree_mul_prod {n : ℕ} (r : Fin n → ℕ) (s : ℕ) :
    Squarefree (s * ∏ j, r j) → Squarefree (∏ j, r j) := fun h =>
  h.squarefree_of_dvd (dvd_mul_left _ _)

open Classical in
theorem harmonic_sum_snoc_insertNth {n : ℕ} {E : Type*} (Q : Finset ℕ) (i : Fin (n + 1))
    (u : ℕ → E) (G : (Fin n → E) → ℝ) (F : (Fin (n + 1) → E) → ℝ) :
    (∑ t ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Q),
      (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
        (if Squarefree (∏ j, t j) then G (fun j => u (t j.castSucc)) *
            F (fun l => u (i.insertNth (α := fun _ => ℕ) (t (Fin.last n))
              (Fin.init t) l)) else 0)) =
    ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Q),
      (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
        (if Squarefree (∏ j, r j) then G (fun j => u (r j)) else 0) *
          ∑ a ∈ Q, (a.totient : ℝ)⁻¹ *
            (if Squarefree (a * ∏ j, r j) then
              F (fun l => u (i.insertNth (α := fun _ => ℕ) a r l)) else 0) := by
  rw [sum_pi_snoc Q]
  simp only [Fin.prod_snoc, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]
  apply Finset.sum_congr rfl
  intro r _
  have hprod (b : ℕ) : (∏ j, (Nat.totient (Fin.snoc (α := fun _ => ℕ) r b j) : ℝ)⁻¹) =
      (∏ j, (Nat.totient (r j) : ℝ)⁻¹) * (Nat.totient b : ℝ)⁻¹ := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hprod]
  by_cases h : Squarefree (b * ∏ j, r j)
  · have hr : Squarefree (∏ j, r j) := squarefree_prod_of_squarefree_mul_prod r b h
    simp only [hr, h, mul_comm (∏ j : Fin n, r j) b, ite_true]
    ring
  · have h' : ¬ Squarefree ((∏ j, r j) * b) := by simpa [mul_comm] using h
    by_cases hr : Squarefree (∏ j, r j) <;> simp [h, h', hr]

open Classical in
theorem harmonic_sum_snoc_snoc_insertNth {n : ℕ} {E : Type*} (Q : Finset ℕ) (i : Fin (n + 1))
    (u : ℕ → E) (F F' : (Fin (n + 1) → E) → ℝ) :
    (∑ v ∈ Fintype.piFinset (fun _ : Fin (n + 1 + 1) => Q),
      (∏ j, (Nat.totient (v j) : ℝ)⁻¹) *
        (if Squarefree (∏ j : Fin (n + 1), v j.castSucc) ∧
              Squarefree ((∏ j : Fin n, v j.castSucc.castSucc) * v (Fin.last (n + 1))) then
           F (fun l => u (i.insertNth (α := fun _ => ℕ) (v (Fin.last n).castSucc)
              (Fin.init (Fin.init v)) l)) *
           F' (fun l => u (i.insertNth (α := fun _ => ℕ) (v (Fin.last (n + 1)))
               (Fin.init (Fin.init v)) l)) else 0)) =
    ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Q), (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
      (∑ a ∈ Q, (a.totient : ℝ)⁻¹ *
          (if Squarefree (a * ∏ j, r j) then
              F (fun l => u (i.insertNth (α := fun _ => ℕ) a r l)) else 0)) *
      (∑ b ∈ Q, (b.totient : ℝ)⁻¹ *
          (if Squarefree (b * ∏ j, r j) then
            F' (fun l => u (i.insertNth (α := fun _ => ℕ) b r l)) else 0)) := by
  rw [sum_pi_snoc Q]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init_snoc]
  rw [sum_pi_snoc Q]
  simp only [Fin.prod_snoc, Fin.snoc_castSucc, Fin.snoc_last, Fin.init_snoc]
  apply Finset.sum_congr rfl
  intro r _
  have hprod (a b : ℕ) : (∏ j, (Nat.totient (Fin.snoc (α := fun _ => ℕ)
        (Fin.snoc (α := fun _ => ℕ) r a) b j) : ℝ)⁻¹) =
      ((∏ j, (Nat.totient (r j) : ℝ)⁻¹) * (a.totient : ℝ)⁻¹) * (b.totient : ℝ)⁻¹ := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [hprod]
  rw [mul_assoc, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases h : Squarefree (b * ∏ j, r j) <;> by_cases h' : Squarefree (c * ∏ j, r j) <;>
    simp only [h, h', mul_comm (∏ j : Fin n, r j), ite_true, ite_false,
      and_true, and_false] <;> ring

theorem sum_four_linear_terms {α : Type*} (T : Finset α) (f0 f1 f2 f3 : α → ℝ)
    (c d e : ℝ) :
    c * (∑ i ∈ T, f0 i) + d * (∑ i ∈ T, f1 i) + d * (∑ i ∈ T, f2 i) + e * (∑ i ∈ T, f3 i) =
      ∑ i ∈ T, (c * f0 i + d * f1 i + d * f2 i + e * f3 i) := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem polarized_harmonic_sum_expansion {E : Type*} (i : Fin 39) (Q : Finset ℕ)
    (B : ℝ) (hB : B ≠ 0) (U : ℕ → E)
    (G G' : (Fin 38 → E) → ℝ) (F F' : (Fin 39 → E) → ℝ) :
    let T39 := (Fintype.piFinset (fun _ : Fin 38 => Q)).filter
      (fun r => Squarefree (∏ j, r j))
    let T40 := (Fintype.piFinset (fun _ : Fin 39 => Q)).filter
      (fun r => Squarefree (∏ j, r j))
    let w := fun K : (Fin 38 → E) → ℝ =>
      ∑ r ∈ T39, Finsupp.single r (K (fun j => U (r j)) / B ^ 38)
    let y := fun K : (Fin 39 → E) → ℝ =>
      ∑ r ∈ T40, Finsupp.single r (K (fun j => U (r j)) / B ^ 39)
    let erase := fun v : (Fin 39 → ℕ) →₀ ℝ =>
      v.sum (fun r vr => Finsupp.single (fun j => r (i.succAbove j))
        (vr / ((r i).totient : ℝ)))
    let z := w G + erase (y F)
    let z' := w G' + erase (y F')
    B ^ 38 * z.sum (fun r zr => zr * z' r / ∏ j, ((r j).totient : ℝ)) =
      (B ^ 38)⁻¹ * (∑ r ∈ Fintype.piFinset (fun _ : Fin 38 => Q),
        (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
          (if Squarefree (∏ j, r j) then G (fun j => U (r j))*G' (fun j => U (r j)) else 0)) +
      (B ^ 39)⁻¹ * (∑ t ∈ Fintype.piFinset (fun _ : Fin 39 => Q),
        (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
          (if Squarefree (∏ j, t j) then
            G (fun j => U (t j.castSucc)) *
              F' (fun l => U (i.insertNth (α := fun _ => ℕ) (t (Fin.last 38))
                (Fin.init t) l)) else 0)) +
      (B ^ 39)⁻¹ * (∑ t ∈ Fintype.piFinset (fun _ : Fin 39 => Q),
        (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
          (if Squarefree (∏ j, t j) then
            G' (fun j => U (t j.castSucc)) *
            F (fun l => U (i.insertNth (α := fun _ => ℕ) (t (Fin.last 38))
              (Fin.init t) l)) else 0)) +
      (B ^ 40)⁻¹ * (∑ v ∈ Fintype.piFinset (fun _ : Fin 40 => Q),
        (∏ j, (Nat.totient (v j) : ℝ)⁻¹) *
          (if Squarefree (∏ j : Fin 39, v j.castSucc) ∧
              Squarefree ((∏ j : Fin 38, v j.castSucc.castSucc) * v (Fin.last 39)) then
            F (fun l => U (i.insertNth (α := fun _ => ℕ) (v (Fin.last 38).castSucc)
                (Fin.init (Fin.init v)) l)) *
            F' (fun l => U (i.insertNth (α := fun _ => ℕ) (v (Fin.last 39))
              (Fin.init (Fin.init v)) l))
          else 0)) := by
  classical
  intro T39 T40 w y e z z'
  let Ret := Fintype.piFinset (fun _ : Fin 38 => Q)
  let tw := fun r : Fin 38 → ℕ => ∏ j, (Nat.totient (r j) : ℝ)⁻¹
  let D := fun r : Fin 38 → ℕ => ∏ j, r j
  let A := fun (K : (Fin 38 → E) → ℝ) (r : Fin 38 → ℕ) =>
    if Squarefree (D r) then K (fun j => U (r j)) else 0
  let Z := fun (K : (Fin 39 → E) → ℝ) (r : Fin 38 → ℕ) (s : ℕ) =>
    K (fun l => U (i.insertNth (α := fun _ => ℕ) s r l))
  let S := fun (K : (Fin 39 → E) → ℝ) (r : Fin 38 → ℕ) =>
    ∑ s ∈ Q, (s.totient : ℝ)⁻¹ * (if Squarefree (s * D r) then Z K r s else 0)
  have Wv (K) (r : Fin 38 → ℕ) : w K r =
      if r ∈ Ret then A K r / B ^ 38 else 0 := by
    dsimp [w, T39, A, D]
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
      Finset.mem_filter, Fintype.mem_piFinset]
    have ret (r : Fin 38 → ℕ) : (r ∈ Ret) ↔ ∀ j, r j ∈ Q := Fintype.mem_piFinset
    by_cases hr : r ∈ Ret
    · have h : ∀ j, r j ∈ Q := ret r |>.mp hr
      by_cases hsq : Squarefree (∏ j : Fin 38, r j) <;>
        simp [hr, h, hsq]
    · have h : ¬ ∀ j, r j ∈ Q := by simpa only [ret] using hr
      simp [hr, h]
  have Ev (K) (r : Fin 38 → ℕ) : e (y K) r =
      if r ∈ Ret then S K r / B ^ 39 else 0 := by
    rw [canonical_erased_profile_sum i Q (fun t => K (fun j => U (t j))/B ^ 39) r]
    have ret : (∀ j, r j ∈ Q) ↔ r ∈ Ret := Fintype.mem_piFinset.symm
    by_cases hr : r ∈ Ret
    · rw [ite_eq_left hr]
      simp_rw [ret, hr, and_true, S, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases ht : Squarefree (s * D r)
      · simp [ht, D, Z]
        ring
      · simp [ht, D]
    · rw [ite_eq_right hr]
      simp_rw [ret, hr, and_false, ite_false, Finset.sum_const_zero]
  have Zv (K KK) (r : Fin 38 → ℕ) : (w K + e (y KK)) r =
      if r ∈ Ret then A K r / B ^ 38 + S KK r / B ^ 39 else 0 := by
    rw [Finsupp.add_apply, Wv, Ev]
    by_cases hr : r ∈ Ret <;> simp [hr]
  have zs (K KK) : (w K + e (y KK)).support ⊆ Ret := by
    intro r hr
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hr) (by rw [Zv, ite_eq_right hn])
  let expr0 := (∑ r ∈ Ret, tw r *
      (if Squarefree (D r) then G (fun j => U (r j))*G' (fun j => U (r j)) else 0))
  let expr1 := (∑ r ∈ Ret, tw r * A G r * S F' r)
  let expr2 := (∑ r ∈ Ret, tw r * A G' r * S F r)
  let expr3 := (∑ r ∈ Ret, tw r * S F r * S F' r)
  have ind1 := harmonic_sum_snoc_insertNth Q i U G F'
  have ind2 := harmonic_sum_snoc_insertNth Q i U G' F
  have ind3 := harmonic_sum_snoc_snoc_insertNth Q i U F F'
  rw [ind1, ind2, ind3]
  dsimp only [z, z']
  change B ^ 38 * _ = (B ^ 38)⁻¹ * expr0 + (B ^ 39)⁻¹ * expr1 +
    (B ^ 39)⁻¹ * expr2 + (B ^ 40)⁻¹ * expr3
  dsimp only [expr0, expr1, expr2, expr3]
  rw [sum_four_linear_terms]
  rw [Finsupp.sum_of_support_subset _ (zs G F) _ (by simp)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Zv, ite_eq_left hr]
  have hpow : B ^ 38 ≠ 0 := pow_ne_zero _ hB
  dsimp only [tw, D]
  simp only [A]
  have htinv : (∏ j, (Nat.totient (r j) : ℝ)⁻¹) = (∏ j, (Nat.totient (r j) : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib]
  rw [htinv]
  rw [div_eq_mul_inv, show B ^ 39 = B ^ 38 * B by ring, show B ^ 40 = B ^ 38 * B ^ 2 by ring]
  simp only [mul_inv_rev]
  by_cases hh : Squarefree (∏ j : Fin 38, r j)
  · simp only [D, hh, ite_eq_left]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    simp only [mul_inv_rev]
    field_simp [hpow, hB] ; ring
  · simp only [D, hh, ite_false, zero_div, zero_add, mul_zero, zero_mul, add_zero]
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp [hpow, hB]

theorem measurePreserving_insertNth {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure E) [SigmaFinite μ] (i : Fin (n + 1)) :
    MeasurePreserving (fun p : (Fin n → E) × E => i.insertNth p.2 p.1)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ) (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  convert ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i).symm).comp
    (Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin n => μ)) (ν := μ)) using 1
  ext p j
  rfl

theorem measurePreserving_init_last {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure E) [SigmaFinite μ] :
    MeasurePreserving (fun v : Fin (n + 1) → E => (Fin.init v, v (Fin.last n)))
      (Measure.pi (fun _ : Fin (n + 1) => μ)) ((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
  convert (Measure.measurePreserving_swap (μ := μ) (ν := Measure.pi (fun _ : Fin n => μ))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)) using 1
  ext v
  · simp [MeasurableEquiv.piFinSuccAbove,
      Fin.insertNthEquiv, Fin.init]
  · rfl

theorem exists_shared_prime_of_not_squarefree_overlapping_products {n : ℕ}
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (v : Fin (n + 1 + 1) → ℕ) (hv : ∀ j : Fin (n + 1 + 1), v j ∈ (∏ p ∈ S, p).divisors)
    (hbad : ¬ (Squarefree (∏ j : Fin (n + 1), v j.castSucc) ∧
          Squarefree ((∏ j : Fin n, v j.castSucc.castSucc) * v (Fin.last (n + 1))))) :
      ∃ j k, j ≠ k ∧ ∃ p ∈ S, p ∣ v j ∧ p ∣ v k := by
  classical
  rcases not_and_or.mp hbad with h | h
  · obtain ⟨j, k, hne, p, hp, hj, hk⟩ :=
      exists_shared_prime_of_not_squarefree_prod S hS
        (fun j : Fin (n + 1) => v j.castSucc) (fun j => hv _) h
    exact ⟨j.castSucc, k.castSucc, Fin.castSucc_inj.ne.mpr hne, p, hp, hj, hk⟩
  · let e : Fin (n + 1) → Fin (n + 1 + 1) := (Fin.castSucc (Fin.last n)).succAbove
    have heq (j : Fin (n + 1)) : v (e j) = Fin.snoc (α := fun _ => ℕ)
        (fun b : Fin n => v b.castSucc.castSucc) (v (Fin.last (n + 1))) j := by
      cases j using Fin.lastCases with
      | last =>
        change v ((Fin.last n).castSucc.succAbove (Fin.last n)) = _
        rw [Fin.succAbove_castSucc_self, Fin.snoc_last]
        rfl
      | cast j =>
        simp only [Fin.snoc_castSucc]
        change v ((Fin.last n).castSucc.succAbove j.castSucc) = v j.castSucc.castSucc
        rw [Fin.succAbove_castSucc_of_lt (Fin.last n) j.castSucc (Fin.castSucc_lt_last j)]
    obtain ⟨j, k, hjk, p, hp, hj, hk⟩ := exists_shared_prime_of_not_squarefree_prod S hS
      (Fin.snoc (α := fun _ => ℕ) (fun b : Fin n => v b.castSucc.castSucc) (v (Fin.last (n + 1))))
      (fun j => by rw [← heq]; exact hv _)
      (by simpa only [Fin.prod_snoc] using h)
    exact ⟨e j, e k, Fin.succAbove_right_injective.ne hjk, p, hp,
      by rwa [← heq] at hj, by rwa [← heq] at hk⟩

theorem integrable_of_measurable_of_bounded_range {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsFiniteMeasure μ] (f : E → ℝ) (hf : Measurable f)
    (hb : Bornology.IsBounded (Set.range f)) : Integrable f μ := by
  obtain ⟨C, _, hC⟩ := hb.exists_pos_norm_le
  exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall
    (fun t => hC _ ⟨t, rfl⟩))

theorem isBounded_range_mul_comp {D A A' : Type*} {f : A → ℝ} {g : A' → ℝ}
    (hf : Bornology.IsBounded (Set.range f)) (hg : Bornology.IsBounded (Set.range g))
    (u : D → A) (v : D → A') :
    Bornology.IsBounded (Set.range (fun x => f (u x) * g (v x))) := by
  apply (isBounded_mul hf hg).subset
  rintro _ ⟨x, rfl⟩
  exact ⟨_, ⟨u x, rfl⟩, _, ⟨v x, rfl⟩, rfl⟩

theorem integral_product_of_sums_with_marginals {Y E : Type*} [MeasurableSpace Y]
    [MeasurableSpace E]
    (η : Measure Y) (ν : Measure E) [SFinite η] [SFinite ν]
    (g g' : Y → ℝ) (f f' : Y × E → ℝ)
    (ig : Integrable (fun y => g y * g' y) η)
    (ih : Integrable (fun p : Y × E => g p.1 * f' p) (η.prod ν))
    (ih' : Integrable (fun p : Y × E => f p * g' p.1) (η.prod ν))
    (ihh : Integrable (fun p : (Y × E) × E => f p.1 * f' (p.1.1,p.2))
      ((η.prod ν).prod ν)) :
    (∫ y, (g y + ∫ t, f (y,t) ∂ν) * (g' y + ∫ t, f' (y,t) ∂ν) ∂η) =
      (∫ y, g y * g' y ∂η) +
        (∫ p : Y × E, g p.1 * f' p ∂η.prod ν) +
        (∫ p : Y × E, f p * g' p.1 ∂η.prod ν) +
        ∫ p : (Y × E) × E, f p.1 * f' (p.1.1,p.2) ∂(η.prod ν).prod ν := by
  have eqgp : (∫ p : Y × E, g p.1 * f' p ∂η.prod ν) =
      (∫ r, g r * (∫ t, f' (r, t) ∂ν) ∂η) := by
    rw [integral_prod _ ih]
    simp only [integral_const_mul]
  have eqpg : (∫ p : Y × E, f p * g' p.1 ∂η.prod ν) =
      (∫ r, (∫ t, f (r, t) ∂ν) * g' r ∂η) := by
    rw [integral_prod _ ih']
    simp only [integral_mul_const]
  have aux (p : Y × E) : (∫ t, f p * f' (p.1,t) ∂ν) = f p * (∫ t, f' (p.1,t) ∂ν) :=
    integral_const_mul _ _
  have ep : Integrable (fun p : Y × E => f p * (∫ t, f' (p.1,t) ∂ν)) (η.prod ν) := by
    convert ihh.integral_prod_left using 1
    exact (funext aux).symm
  have eqpp : (∫ p : (Y × E) × E, f p.1 * f' (p.1.1,p.2) ∂(η.prod ν).prod ν) =
      ∫ r, (∫ s, f (r, s) ∂ν) * (∫ t, f' (r, t) ∂ν) ∂η := by
    rw [integral_prod _ ihh, integral_congr_ae (.of_forall aux), integral_prod _ ep]
    simp only [integral_mul_const]
  have ieqgp := ih.integral_prod_left
  have ieqpg := ih'.integral_prod_left
  simp only [integral_const_mul] at ieqgp
  simp only [integral_mul_const] at ieqpg
  have ieqpp := ep.integral_prod_left
  simp only [integral_mul_const] at ieqpp
  rw [eqgp, eqpg, eqpp]
  calc
    _ = (∫ y, (g y * g' y + g y * (∫ t, f' (y, t) ∂ν)) +
        ((∫ t, f (y, t) ∂ν) * g' y + (∫ s, f (y, s) ∂ν) * (∫ t, f' (y, t) ∂ν)) ∂η) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring)
    _ = _ := by
      simpa only [Pi.add_apply, integral_add ig ieqgp, integral_add ieqpg ieqpp,
        add_assoc] using integral_add (ig.add ieqgp) (ieqpg.add ieqpp)

theorem insertNth_comp {α β : Type*} {n : ℕ} (i : Fin (n + 1))
    (U : α → β) (x : α) (f : Fin n → α) :
    i.insertNth (α := fun _ => β) (U x) (fun j => U (f j)) =
      (fun j => U (i.insertNth (α := fun _ => α) x f j)) := by
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · rw [Fin.insertNth_apply_same]
  · ext j
    simp [Fin.removeNth]

theorem integral_pi_product_of_sums_with_marginals {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsFiniteMeasure ν] (i : Fin 39)
    (G G' : (Fin 38 → E) → ℝ) (F F' : (Fin 39 → E) → ℝ)
    (hG : Measurable G) (hG' : Measurable G') (hF : Measurable F) (hF' : Measurable F')
    (hbG : Bornology.IsBounded (Set.range G)) (hbG' : Bornology.IsBounded (Set.range G'))
    (hbF : Bornology.IsBounded (Set.range F)) (hbF' : Bornology.IsBounded (Set.range F')) :
    (∫ y, (G y + ∫ t, F (i.insertNth t y) ∂ν) *
      (G' y + ∫ t, F' (i.insertNth t y) ∂ν) ∂Measure.pi (fun _ : Fin 38 => ν)) =
        (∫ y, G y * G' y ∂Measure.pi (fun _ : Fin 38 => ν)) +
        (∫ v, G (Fin.init v) * F' (i.insertNth (v (Fin.last 38)) (Fin.init v))
          ∂Measure.pi (fun _ : Fin 39 => ν)) +
        (∫ v, G' (Fin.init v) * F (i.insertNth (v (Fin.last 38)) (Fin.init v))
          ∂Measure.pi (fun _ : Fin 39 => ν)) +
        (∫ v, F (i.insertNth (v (Fin.last 38).castSucc) (Fin.init (Fin.init v))) *
             F' (i.insertNth (v (Fin.last 39)) (Fin.init (Fin.init v)))
          ∂Measure.pi (fun _ : Fin 40 => ν)) := by
  let Y := Fin 38 → E
  let η := Measure.pi (fun _ : Fin 38 => ν)
  let J : Y × E → (Fin 39 → E) := fun p => i.insertNth p.2 p.1
  have jp : MeasurePreserving J ((Measure.pi (fun _ : Fin 38 => ν)).prod ν)
       (Measure.pi (fun _ : Fin 39 => ν)) := measurePreserving_insertNth ν i
  have dp : MeasurePreserving (fun r : Fin 39 → E => (Fin.init r, r (Fin.last 38)))
      (Measure.pi (fun _ : Fin 39 => ν)) (η.prod ν) := measurePreserving_init_last ν
  have d2p : MeasurePreserving
      (fun r : Fin 40 → E => ((Fin.init (Fin.init r), r (Fin.last 38).castSucc), r (Fin.last 39)))
      (Measure.pi (fun _ : Fin 40 => ν)) ((η.prod ν).prod ν) := by
    convert ((measurePreserving_init_last (n := 38) ν).prod (MeasurePreserving.id ν)).comp
      (measurePreserving_init_last (n := 39) ν) using 1
    rfl
  have jm : Measurable J := jp.measurable
  have dm : Measurable (fun r : Fin 39 → E => (Fin.init r, r (Fin.last 38))) := dp.measurable
  have d2m : Measurable (fun r : Fin 40 → E => ((Fin.init (Fin.init r),
      r (Fin.last 38).castSucc), r (Fin.last 39))) := d2p.measurable
  let gp : Y × E → ℝ := fun p => G p.1 * F' (J p)
  let pg : Y × E → ℝ := fun p => G' p.1 * F (J p)
  let pp : (Y × E) × E → ℝ := fun p => F (J p.1) * F' (J (p.1.1,p.2))
  have mp : Measurable pp := (hF.comp (jm.comp measurable_fst)).mul
    (hF'.comp (jm.comp (by fun_prop)))
  have bpm := isBounded_range_mul_comp hbF hbF' (J ∘ Prod.fst) (fun p => J (p.1.1,p.2))
  have mi : Integrable gp (η.prod ν) := integrable_of_measurable_of_bounded_range _ _
    ((hG.comp measurable_fst).mul (hF'.comp jm)) (isBounded_range_mul_comp hbG hbF' Prod.fst J)
  have mi' : Integrable (fun p : Y × E => F (J p) * G' p.1) (η.prod ν) :=
    integrable_of_measurable_of_bounded_range _ _
      ((hF.comp jm).mul (hG'.comp measurable_fst)) (isBounded_range_mul_comp hbF hbG' J Prod.fst)
  have md : Integrable pp ((η.prod ν).prod ν) :=
    integrable_of_measurable_of_bounded_range _ _ mp bpm
  have c := integral_product_of_sums_with_marginals η ν G G' (F ∘ J) (F' ∘ J)
    (integrable_of_measurable_of_bounded_range _ _ (hG.mul hG')
      (isBounded_range_mul_comp hbG hbG' id id)) mi mi' md
  have cg : (∫ p, gp p ∂η.prod ν) =
       (∫ r, gp (Fin.init r, r (Fin.last 38)) ∂Measure.pi (fun _ : Fin 39 => ν)) := by
    rw [← dp.map_eq]
    exact integral_map_of_stronglyMeasurable dm (show StronglyMeasurable gp from
      ((hG.comp measurable_fst).mul (hF'.comp jm)).stronglyMeasurable)
  have cg' : (∫ p, pg p ∂η.prod ν) =
       (∫ r, pg (Fin.init r, r (Fin.last 38)) ∂Measure.pi (fun _ : Fin 39 => ν)) := by
    rw [← dp.map_eq]
    exact integral_map_of_stronglyMeasurable dm (show StronglyMeasurable pg from
      ((hG'.comp measurable_fst).mul (hF.comp jm)).stronglyMeasurable)
  have cq : (∫ p, pp p ∂(η.prod ν).prod ν) =
       (∫ r, pp ((Fin.init (Fin.init r), r (Fin.last 38).castSucc), r (Fin.last 39))
        ∂Measure.pi (fun _ : Fin 40 => ν)) := by
    rw [← d2p.map_eq]
    exact integral_map_of_stronglyMeasurable d2m mp.stronglyMeasurable
  have flip : (∫ p : Y × E, F (J p) * G' p.1 ∂η.prod ν) = ∫ p, pg p ∂η.prod ν :=
    integral_congr_ae (.of_forall fun p => mul_comm (F (J p)) (G' p.1))
  change (∫ y, (G y + ∫ t, F (i.insertNth t y) ∂ν) *
      (G' y + ∫ t, F' (i.insertNth t y) ∂ν) ∂η) = (∫ y, G y * G' y ∂η) +
      (∫ p, gp p ∂η.prod ν) + (∫ p, (fun u => F (J u) * G' u.1) p ∂η.prod ν) +
      (∫ p, pp p ∂(η.prod ν).prod ν) at c
  rw [flip, cg, cg', cq] at c
  exact c

theorem tendsto_mixed_harmonic_sum {m : ℕ} (Hs : Finset ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (i : Fin 39) (κ : ℝ) (hκ : 0 < κ) (a : Fin (m + 2) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = κ) (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F)) :
    let ν : Measure (Fin (m + 1) → ℝ) := ENNReal.ofReal
        (Real.exp Real.eulerMascheroniConstant * κ) •
          Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt G X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F X) →
    let W := presievingModulus Hs
    let R := fun x : ℝ => x ^ ρ
    let B := fun x : ℝ => fragmentNormalization (W x) (R x)
    let Q := fun x : ℝ => (∏ p ∈ fragmentPrimes (W x) (R x) κ, p).divisors
    let U := fun x : ℝ => fun s : ℕ =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    Tendsto (fun x : ℝ => ((B x) ^ 39)⁻¹ * (∑ t ∈ Fintype.piFinset (fun _ : Fin 39 => Q x),
        (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
          (if Squarefree (∏ j, t j) then
            G (fun j => U x (t j.castSucc)) *
            F (fun l => U x (i.insertNth (α := fun _ => ℕ) (t (Fin.last 38))
              (Fin.init t) l)) else 0))) atTop
      (𝓝 (∫ v, G (Fin.init v) * F (i.insertNth (v (Fin.last 38)) (Fin.init v))
          ∂Measure.pi (fun _ : Fin 39 => ν))) := by
  intro ν cG cF W R B Q U
  let E := Fin (m + 1) → ℝ
  let Y := Fin 38 → E
  let : IsProbabilityMeasure (fragmentLaw κ) :=
    fragmentLaw_isProbabilityMeasure κ
  let : IsFiniteMeasure ν := by
    dsimp [ν]
    exact (Measure.map (fragmentBandMasses a)
      (fragmentLaw κ)).smul_finite (by simp)
  let η := Measure.pi (fun _ : Fin 38 => ν)
  let η' := Measure.pi (fun _ : Fin 39 => ν)
  let J : Y × E → (Fin 39 → E) := fun p => i.insertNth p.2 p.1
  have jmeas : Measurable J := by dsimp [J]; fun_prop
  have jc : Continuous J := by dsimp [J]; fun_prop
  have jp : MeasurePreserving J (η.prod ν) η' := measurePreserving_insertNth ν i
  let d : (Fin 39 → E) → Y × E := fun r => (Fin.init r, r (Fin.last 38))
  have dmeas : Measurable d := by dsimp [d]; fun_prop
  have dc : Continuous d := by dsimp [d]; fun_prop
  have dp : MeasurePreserving d η' (η.prod ν) := measurePreserving_init_last ν
  let g : Y × E → ℝ := fun p => G p.1 * F (J p)
  have gm : Measurable g := (hG.comp measurable_fst).mul (hF.comp jmeas)
  have gb : Bornology.IsBounded (Set.range g) := isBounded_range_mul_comp hbG hbF Prod.fst J
  have gc : ∀ᵐ p ∂η.prod ν, ContinuousAt g p := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := η) (ν := ν)).tendsto_ae cG,
      jp.quasiMeasurePreserving.tendsto_ae cF] with p hp hq
    exact (hp.comp continuous_fst.continuousAt).mul (hq.comp jc.continuousAt)
  have gcD : ∀ᵐ r ∂η', ContinuousAt (g ∘ d) r := by
    filter_upwards [dp.quasiMeasurePreserving.tendsto_ae gc] with t ht
    exact ht.comp dc.continuousAt
  have bcom : Bornology.IsBounded (Set.range (g ∘ d)) :=
    gb.subset (Set.range_comp_subset_range d g)
  have hid (x : ℝ) (r : Fin 39 → ℕ) : ((g ∘ d) (fun j => U x (r j))) =
        (G (fun j => U x (r j.castSucc)) *
          F (fun l => U x (i.insertNth (α := fun _ => ℕ) (r (Fin.last 38)) (Fin.init r) l))) := by
    dsimp only [g, d, J, Function.comp_apply]
    simp only [Fin.init_def, insertNth_comp]
  have h := tendsto_restricted_harmonic_pi_sum (n := 39) Hs ρ κ a hρ hκ ha ha0 haLast
    (fun r : Fin 39 → ℕ => Squarefree (∏ j, r j)) (fun S hS r hr h =>
      exists_shared_prime_of_not_squarefree_prod S hS r hr h)
    (g ∘ d) (gm.comp dmeas) bcom gcD
  apply h.congr'
  exact Filter.Eventually.of_forall (fun x => by
    change ((B x) ^ 39)⁻¹ *
      (∑ t ∈ Fintype.piFinset (fun _ : Fin 39 => Q x), (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
        (if Squarefree (∏ j, t j) then (g ∘ d) (fun j => U x (t j)) else 0)) = _
    simp only [hid x])

theorem measurable_bounded_ae_continuous_insertNth_product {m n : ℕ}
    (ν : Measure (Fin (m + 1) → ℝ)) [IsFiniteMeasure ν] (i : Fin (n + 1))
    (F F' : (Fin (n + 1) → Fin (m + 1) → ℝ) → ℝ)
    (hF : Measurable F) (hF' : Measurable F')
    (hbF : Bornology.IsBounded (Set.range F)) (hbF' : Bornology.IsBounded (Set.range F'))
    (cF : ∀ᵐ X ∂Measure.pi (fun _ : Fin (n + 1) => ν), ContinuousAt F X)
    (cF' : ∀ᵐ X ∂Measure.pi (fun _ : Fin (n + 1) => ν), ContinuousAt F' X) :
    let g := fun v => F (i.insertNth (v (Fin.last n).castSucc) (Fin.init (Fin.init v))) *
              F' (i.insertNth (v (Fin.last (n + 1))) (Fin.init (Fin.init v)))
    Measurable g ∧ Bornology.IsBounded (Set.range g) ∧
      ∀ᵐ v ∂Measure.pi (fun _ : Fin (n + 1 + 1) => ν), ContinuousAt g v := by
  intro g
  let E := Fin (m + 1) → ℝ
  let Y := Fin n → E
  let η := Measure.pi (fun _ : Fin (n + 1) => ν)
  let η0 := Measure.pi (fun _ : Fin n => ν)
  let J : Y × E → (Fin (n + 1) → E) := fun p => i.insertNth p.2 p.1
  have jmeas : Measurable J := by dsimp [J]; fun_prop
  have jc : Continuous J := by dsimp [J]; fun_prop
  have jp : MeasurePreserving J ((Measure.pi (fun _ : Fin n => ν)).prod ν) η :=
    measurePreserving_insertNth ν i
  let d2 : (Fin (n + 1 + 1) → E) → (Y × E) × E := fun x =>
     ((Fin.init (Fin.init x), x (Fin.last n).castSucc), x (Fin.last (n + 1)))
  have d2m : Measurable d2 := by dsimp [d2]; fun_prop
  have d2c : Continuous d2 := by dsimp [d2]; fun_prop
  have d2p : MeasurePreserving d2 (Measure.pi (fun _ : Fin (n + 1 + 1) => ν))
      ((η0.prod ν).prod ν) := by
    convert ((measurePreserving_init_last (n := n) ν).prod (MeasurePreserving.id ν)).comp
      (measurePreserving_init_last (n := (n + 1)) ν) using 1
    rfl
  let sk : (Y × E) × E → Y × E := fun q => (q.1.1, q.2)
  have skC : Continuous sk := by dsimp [sk]; fun_prop
  have skM : Measurable sk := by dsimp [sk]; fun_prop
  have skp : Measure.QuasiMeasurePreserving sk ((η0.prod ν).prod ν) (η0.prod ν) := by
    convert (MeasureTheory.QuasiMeasurePreserving.prodMap
        (Measure.quasiMeasurePreserving_fst (μ := η0) (ν := ν))
        (Measure.QuasiMeasurePreserving.id ν)) using 1
    rfl
  let pp : (Y × E) × E → ℝ := fun q => F (J q.1) * F' (J (sk q))
  have ppm : Measurable pp := (hF.comp (jmeas.comp measurable_fst)).mul
    (hF'.comp (jmeas.comp skM))
  have ppb := isBounded_range_mul_comp hbF hbF' (J ∘ Prod.fst) (J ∘ sk)
  have mc : ∀ᵐ p ∂η0.prod ν, ContinuousAt (F ∘ J) p := by
    filter_upwards [jp.quasiMeasurePreserving.tendsto_ae cF] with p hp
    exact hp.comp jc.continuousAt
  have mc' : ∀ᵐ p ∂η0.prod ν, ContinuousAt (F' ∘ J) p := by
    filter_upwards [jp.quasiMeasurePreserving.tendsto_ae cF'] with p hp
    exact hp.comp jc.continuousAt
  have cpP : ∀ᵐ r ∂((η0.prod ν).prod ν), ContinuousAt pp r := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := η0.prod ν) (ν := ν)).tendsto_ae mc,
      skp.tendsto_ae mc'] with p hp hq
    exact (hp.comp continuous_fst.continuousAt).mul (hq.comp skC.continuousAt)
  have hppD : ∀ᵐ r ∂Measure.pi (fun _ : Fin (n + 1 + 1) => ν), ContinuousAt (pp ∘ d2) r := by
    filter_upwards [d2p.quasiMeasurePreserving.tendsto_ae cpP] with t ht
    exact ht.comp d2c.continuousAt
  have bcom : Bornology.IsBounded (Set.range (pp ∘ d2)) :=
    ppb.subset (Set.range_comp_subset_range d2 pp)
  change Measurable (pp ∘ d2) ∧ Bornology.IsBounded (Set.range (pp ∘ d2)) ∧
    ∀ᵐ r ∂Measure.pi (fun _ : Fin (n + 1 + 1) => ν), ContinuousAt (pp ∘ d2) r
  exact ⟨ppm.comp d2m, bcom, hppD⟩

theorem sum_insertNth_product_map_eq {E : Type*} {n : ℕ} (i : Fin (n + 1))
    (F F' : (Fin (n + 1) → E) → ℝ)
    (V : ℕ → E) (Q : Finset ℕ) :
    (∑ r ∈ Fintype.piFinset (fun _ : Fin (n + 1 + 1) => Q), (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
      (if Squarefree (∏ j : Fin (n + 1), r j.castSucc) ∧
          Squarefree ((∏ j : Fin n, r j.castSucc.castSucc) * r (Fin.last (n + 1))) then
        (F (fun l => V (i.insertNth (α := fun _ => ℕ) (r (Fin.last n).castSucc)
                (Fin.init (Fin.init r)) l)) *
            F' (fun l => V (i.insertNth (α := fun _ => ℕ) (r (Fin.last (n + 1)))
                (Fin.init (Fin.init r)) l))) else 0)) =
    (∑ r ∈ Fintype.piFinset (fun _ : Fin (n + 1 + 1) => Q), (∏ j, (Nat.totient (r j) : ℝ)⁻¹) *
      (if Squarefree (∏ j : Fin (n + 1), r j.castSucc) ∧
          Squarefree ((∏ j : Fin n, r j.castSucc.castSucc) * r (Fin.last (n + 1))) then
        (F (i.insertNth (V (r (Fin.last n).castSucc)) (Fin.init (Fin.init (fun j => V (r j))))) *
            F' (i.insertNth (V (r (Fin.last (n + 1)))) (Fin.init (Fin.init (fun j => V (r j))))))
        else 0)) := by
  simp only [Fin.init_def, insertNth_comp]

theorem tendsto_double_marginal_harmonic_sum {m n : ℕ} (Hs : Finset ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (i : Fin (n + 1)) (κ : ℝ) (hκ : 0 < κ) (a : Fin (m + 2) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = κ)
    (F F' : (Fin (n + 1) → Fin (m + 1) → ℝ) → ℝ) (hF : Measurable F) (hF' : Measurable F')
    (hbF : Bornology.IsBounded (Set.range F)) (hbF' : Bornology.IsBounded (Set.range F')) :
    let ν : Measure (Fin (m + 1) → ℝ) := ENNReal.ofReal
        (Real.exp Real.eulerMascheroniConstant * κ) •
          Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin (n + 1) => ν), ContinuousAt F X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin (n + 1) => ν), ContinuousAt F' X) →
    let W := presievingModulus Hs
    let R := fun x : ℝ => x ^ ρ
    let B := fun x : ℝ => fragmentNormalization (W x) (R x)
    let Q := fun x : ℝ => (∏ p ∈ fragmentPrimes (W x) (R x) κ, p).divisors
    let U := fun x : ℝ => fun s : ℕ =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    Tendsto (fun x : ℝ => ((B x) ^ (n + 1 + 1))⁻¹ *
      (∑ v ∈ Fintype.piFinset (fun _ : Fin (n + 1 + 1) => Q x),
        (∏ j, (Nat.totient (v j) : ℝ)⁻¹) *
          (if Squarefree (∏ j : Fin (n + 1), v j.castSucc) ∧
              Squarefree ((∏ j : Fin n, v j.castSucc.castSucc) * v (Fin.last (n + 1))) then
            F (fun l => U x (i.insertNth (α := fun _ => ℕ) (v (Fin.last n).castSucc)
                (Fin.init (Fin.init v)) l)) *
            F' (fun l => U x (i.insertNth (α := fun _ => ℕ) (v (Fin.last (n + 1)))
              (Fin.init (Fin.init v)) l)) else 0))) atTop
        (𝓝 (∫ v, F (i.insertNth (v (Fin.last n).castSucc) (Fin.init (Fin.init v))) *
             F' (i.insertNth (v (Fin.last (n + 1))) (Fin.init (Fin.init v)))
          ∂Measure.pi (fun _ : Fin (n + 1 + 1) => ν))) := by
  intro ν cF cF' W R B Q U
  let : IsProbabilityMeasure (fragmentLaw κ) :=
    fragmentLaw_isProbabilityMeasure κ
  let : IsFiniteMeasure ν := by
    dsimp [ν]
    exact (Measure.map (fragmentBandMasses a)
      (fragmentLaw κ)).smul_finite (by simp)
  let g := fun v : Fin (n + 1 + 1) → Fin (m + 1) → ℝ =>
    F (i.insertNth (v (Fin.last n).castSucc) (Fin.init (Fin.init v))) *
             F' (i.insertNth (v (Fin.last (n + 1))) (Fin.init (Fin.init v)))
  obtain ⟨pm, pb, pcont⟩ := measurable_bounded_ae_continuous_insertNth_product ν i F F' hF hF'
    hbF hbF' cF cF'
  have h := tendsto_restricted_harmonic_pi_sum (n := n + 1 + 1) Hs ρ κ a hρ hκ ha ha0 haLast
    (fun v : Fin (n + 1 + 1) → ℕ => Squarefree (∏ j : Fin (n + 1), v j.castSucc) ∧
      Squarefree ((∏ j : Fin n, v j.castSucc.castSucc) * v (Fin.last (n + 1))))
    exists_shared_prime_of_not_squarefree_overlapping_products
    g pm pb pcont
  refine h.congr' ?_
  exact Filter.Eventually.of_forall (fun x => by
    change (((B x) ^ (n + 1 + 1))⁻¹ * _) = (((B x) ^ (n + 1 + 1))⁻¹ * _)
    congr 1
    exact (sum_insertNth_product_map_eq i F F' (U x) (Q x)).symm)

theorem tendsto_polarized_harmonic_sum
    {m : ℕ} (Hs : Finset ℕ) (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 39) (κ : ℝ) (hκ : 0 < κ)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = κ)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hG' : Measurable G')
    (hF : Measurable F) (hF' : Measurable F')
    (hbG : Bornology.IsBounded (Set.range G))
    (hbG' : Bornology.IsBounded (Set.range G'))
    (hbF : Bornology.IsBounded (Set.range F))
    (hbF' : Bornology.IsBounded (Set.range F')) :
    let ν : Measure (Fin (m + 1) → ℝ) := ENNReal.ofReal
        (Real.exp Real.eulerMascheroniConstant * κ) •
          Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt G X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt G' X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F' X) →
    let W := presievingModulus Hs
    let R := fun x : ℝ => x ^ ρ
    let B := fun x : ℝ => fragmentNormalization (W x) (R x)
    let Q := fun x : ℝ => (∏ p ∈ fragmentPrimes (W x) (R x) κ, p).divisors
    let U := fun x : ℝ => fun s : ℕ =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    let HH := fun y => G y + ∫ t, F (i.insertNth t y) ∂ν
    let HH' := fun y => G' y + ∫ t, F' (i.insertNth t y) ∂ν
    Tendsto (fun x : ℝ =>
      ((B x) ^ 38)⁻¹ * (∑ t ∈ Fintype.piFinset (fun _ : Fin 38 => Q x),
        (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
          (if Squarefree (∏ j, t j) then
            G (fun j => U x (t j)) * G' (fun j => U x (t j)) else 0)) +
      ((B x) ^ 39)⁻¹ * (∑ t ∈ Fintype.piFinset (fun _ : Fin 39 => Q x),
        (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
          (if Squarefree (∏ j, t j) then
            G (fun j => U x (t j.castSucc)) *
            F' (fun l => U x (i.insertNth (α := fun _ => ℕ) (t (Fin.last 38))
              (Fin.init t) l)) else 0)) +
      ((B x) ^ 39)⁻¹ * (∑ t ∈ Fintype.piFinset (fun _ : Fin 39 => Q x),
        (∏ j, (Nat.totient (t j) : ℝ)⁻¹) *
          (if Squarefree (∏ j, t j) then
            G' (fun j => U x (t j.castSucc)) *
              F (fun l => U x (i.insertNth (α := fun _ => ℕ) (t (Fin.last 38))
                (Fin.init t) l)) else 0)) +
      ((B x) ^ 40)⁻¹ * (∑ v ∈ Fintype.piFinset (fun _ : Fin 40 => Q x),
        (∏ j, (Nat.totient (v j) : ℝ)⁻¹) *
          (if Squarefree (∏ j : Fin 39, v j.castSucc) ∧
              Squarefree ((∏ j : Fin 38, v j.castSucc.castSucc) * v (Fin.last 39)) then
            F (fun l => U x (i.insertNth (α := fun _ => ℕ) (v (Fin.last 38).castSucc)
                (Fin.init (Fin.init v)) l)) *
            F' (fun l => U x (i.insertNth (α := fun _ => ℕ) (v (Fin.last 39))
              (Fin.init (Fin.init v)) l)) else 0))) atTop
      (𝓝 (∫ y, HH y * HH' y ∂Measure.pi (fun _ : Fin 38 => ν))) := by
  classical
  intro ν cG cG' cF cF' W R B Q U HH HH'
  let : IsProbabilityMeasure (fragmentLaw κ) :=
    fragmentLaw_isProbabilityMeasure κ
  let : IsFiniteMeasure ν := by
    dsimp [ν]
    exact (Measure.map (fragmentBandMasses a)
      (fragmentLaw κ)).smul_finite (by simp)
  have cc : ∀ᵐ t ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt (fun y => G y * G' y) t := by
    filter_upwards [cG, cG'] with t ht ht'
    exact ht.mul ht'
  have cb := isBounded_range_mul_comp hbG hbG' id id
  have h0 := tendsto_restricted_harmonic_pi_sum (n := 38) Hs ρ κ a hρ hκ ha ha0 haLast
    (fun r : Fin 38 → ℕ => Squarefree (∏ j, r j)) (fun S hS r hr h =>
      exists_shared_prime_of_not_squarefree_prod S hS r hr h)
    (fun y => G y * G' y) (hG.mul hG') cb cc
  have h1 := tendsto_mixed_harmonic_sum Hs ρ hρ i κ hκ a ha ha0 haLast G F' hG hF' hbG hbF' cG cF'
  have h2 := tendsto_mixed_harmonic_sum Hs ρ hρ i κ hκ a ha ha0 haLast G' F hG' hF hbG' hbF cG' cF
  have h3 := tendsto_double_marginal_harmonic_sum (n := 38) Hs ρ hρ i
    κ hκ a ha ha0 haLast F F' hF hF' hbF hbF' cF cF'
  have contr := integral_pi_product_of_sums_with_marginals ν i G G' F F'
    hG hG' hF hF' hbG hbG' hbF hbF'
  rw [contr]
  exact ((h0.add h1).add h2).add h3

open Classical in
theorem canonical_and_erased_polarized_harmonic_tendsto
    {𝓗 : Finset ℕ}
    {m : ℕ} (i : Fin 39) (κ : ℝ) (hκ : 0 < κ)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = κ)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hG' : Measurable G')
    (hF : Measurable F) (hF' : Measurable F')
    (hbG : Bornology.IsBounded (Set.range G))
    (hbG' : Bornology.IsBounded (Set.range G'))
    (hbF : Bornology.IsBounded (Set.range F))
    (hbF' : Bornology.IsBounded (Set.range F')) :
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a)
          (fragmentLaw κ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt G X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt G' X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F' X) →
    let ρ : ℝ := 2624989 / 10000000
    let W : ℝ → ℕ := presievingModulus 𝓗
    let R : ℝ → ℝ := fun x => x ^ ρ
    let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) κ, p
    let T39 : ℝ → Finset (Fin 38 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 38 => (q x).divisors)).filter
        (fun r => Squarefree (∏ j, r j))
    let T40 : ℝ → Finset (Fin 39 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
        (fun r => Squarefree (∏ j, r j))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s =>
      fragmentBandMasses a
        (primeLogConfiguration (R x) s)
    let w : ((Fin 38 → Fin (m + 1) → ℝ) → ℝ) →
        ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun K x =>
      ∑ r ∈ T39 x, Finsupp.single r (K (fun j => X x (r j)) / B x ^ 38)
    let y : ((Fin 39 → Fin (m + 1) → ℝ) → ℝ) →
        ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun K x =>
      ∑ r ∈ T40 x, Finsupp.single r (K (fun j => X x (r j)) / B x ^ 39)
    let erase : ((Fin 39 → ℕ) →₀ ℝ) → ((Fin 38 → ℕ) →₀ ℝ) := fun v =>
      v.sum (fun r vr => Finsupp.single (fun j => r (i.succAbove j))
        (vr / ((r i).totient : ℝ)))
    let z : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x => w G x + erase (y F x)
    let z' : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x => w G' x + erase (y F' x)
    let H : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun Y =>
      G Y + ∫ t : Fin (m + 1) → ℝ, F (i.insertNth t Y) ∂ν
    let H' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun Y =>
      G' Y + ∫ t : Fin (m + 1) → ℝ, F' (i.insertNth t Y) ∂ν
    Filter.Tendsto
      (fun x : ℝ => B x ^ 38 *
        (z x).sum (fun r zr => zr * z' x r / (∏ j, ((r j).totient : ℝ))))
      Filter.atTop
      (nhds (∫ Y : Fin 38 → Fin (m + 1) → ℝ, H Y * H' Y
        ∂Measure.pi (fun _ : Fin 38 => ν))) := by
  intro ν cG cG' cF cF' ρ W R B q Ta Tb X w y erase z z' H H'
  have hρ : 0 < ρ := by norm_num [ρ]
  have hlim := tendsto_polarized_harmonic_sum 𝓗 ρ hρ i κ hκ a ha ha0 haLast
      G G' F F' hG hG' hF hF' hbG hbG' hbF hbF' cG cG' cF cF'
  apply hlim.congr'
  filter_upwards [(tendsto_rpow_atTop hρ).eventually_gt_atTop 1] with x hx
  have hB : B x ≠ 0 := (fragmentNormalization_pos 𝓗 x (R x) hx).ne'
  exact (polarized_harmonic_sum_expansion i (q x).divisors (B x) hB (X x) G G' F F').symm

end

open Classical in
theorem selberg_divisor_root_abs_le_primeFactor_power
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ)
    (D : Finset (ι → ℕ)) (v : ι → ℕ) (hv : ∀ i, v i ≠ 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ d ∈ D,
      |selbergCoefficient y d| ≤
        K * ((∏ i, d i : ℕ) : ℝ) / ((∏ i, d i : ℕ).totient : ℝ)) :
    |∑ d ∈ D, if ∀ i, d i ∣ v i then selbergCoefficient y d else 0| ≤
      K * ((2 : ℝ) ^ (∏ i, v i : ℕ).primeFactors.card) ^ (Fintype.card ι + 1) := by
  let N := ∏ i, v i
  let S := N.divisors.filter Squarefree
  let T := D.filter (fun d => (∀ i, d i ∣ v i) ∧ Squarefree (∏ i, d i))
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
  have hcardS : (S.card : ℝ) = (2 : ℝ) ^ N.primeFactors.card := by
    simpa [S, Nat.factors_eq] using
      (Nat.sum_divisors_filter_squarefree hN (f := fun _ => (1 : ℝ)))
  have htuple : T ⊆ Fintype.piFinset (fun _ : ι => S) := by
    intro d hd
    obtain ⟨_, hdiv, hsq⟩ := Finset.mem_filter.mp hd
    apply Fintype.mem_piFinset.mpr
    intro i
    have hdi : d i ∣ ∏ j, d j := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr
        ⟨(hdiv i).trans (Finset.dvd_prod_of_mem v (Finset.mem_univ i)), hN⟩,
        Squarefree.squarefree_of_dvd hdi hsq⟩
  have hcardT : (T.card : ℝ) ≤ (S.card : ℝ) ^ Fintype.card ι := by
    have hc := Finset.card_le_card htuple
    simpa using (Nat.cast_le.mpr hc : (T.card : ℝ) ≤ _)
  have hcoeff : ∀ d ∈ T, |selbergCoefficient y d| ≤ K * (S.card : ℝ) := by
    intro d hd
    obtain ⟨hdD, hdiv, hsq⟩ := Finset.mem_filter.mp hd
    have hprod : (∏ i, d i) ∣ N :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hdiv i)
    have hsubset : (∏ i, d i : ℕ).divisors ⊆ S := by
      simpa only [S, Nat.divisors_filter_squarefree_of_squarefree hsq] using
        (Finset.filter_subset_filter Squarefree (Nat.divisors_subset_of_dvd hN hprod))
    calc
      |selbergCoefficient y d| ≤
          K * (((∏ i, d i : ℕ) : ℝ) / ((∏ i, d i : ℕ).totient : ℝ)) := by
        simpa only [mul_div_assoc] using hbound d hdD
      _ ≤ K * (((∏ i, d i : ℕ).divisors.card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (div_totient_le_card_divisors _) hK
      _ ≤ K * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsubset)) hK
  have hroot : (∑ d ∈ D, if ∀ i, d i ∣ v i then selbergCoefficient y d else 0) =
      ∑ d ∈ T, selbergCoefficient y d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hs : Squarefree (∏ i, d i)
    · simp [hs]
    · simp [hs, selbergCoefficient,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  calc
    |∑ d ∈ D, if ∀ i, d i ∣ v i then selbergCoefficient y d else 0| =
        |∑ d ∈ T, selbergCoefficient y d| := congrArg abs hroot
    _ ≤ (T.card : ℝ) * (K * (S.card : ℝ)) := by
      simpa [Real.norm_eq_abs] using (norm_sum_le_of_le T (f := selbergCoefficient y) hcoeff)
    _ ≤ (S.card : ℝ) ^ Fintype.card ι * (K * (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardT (mul_nonneg hK (Nat.cast_nonneg _))
    _ = K * ((2 : ℝ) ^ N.primeFactors.card) ^ (Fintype.card ι + 1) := by
      rw [pow_succ, hcardS]
      ring

open Classical in
theorem selberg_divisor_root_uniform_subpower
    {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (y : (ι → ℕ) →₀ ℝ) (D : Finset (ι → ℕ)) (n : ℕ),
        n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
        (∀ d ∈ D,
          |selbergCoefficient y d| ≤
            K * ((∏ i, d i : ℕ) : ℝ) / ((∏ i, d i : ℕ).totient : ℝ)) →
        |∑ d ∈ D, if ∀ i, d i ∣ n + h i then selbergCoefficient y d else 0| ≤
          C * x ^ ε := by
  let η : ℝ := ε / ((Fintype.card ι : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨C, hC, hCbound⟩ := exists_primeFactors_power_bound
    (a := (2 : ℝ) ^ (Fintype.card ι + 1)) (one_le_pow₀ (by norm_num)) hη
  let t : ℝ := (Fintype.card ι : ℝ) * η
  have ht : t ≤ ε := by
    dsimp [t, η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨(K + 1) * C * (3 : ℝ) ^ t, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop
    (max (1 : ℝ) ((Finset.univ.sup h : ℕ) : ℝ))] with x hx
  intro y D n hn hbound
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hnx : x ≤ (n : ℝ) := Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1
  have hnx2 : (n : ℝ) ≤ 2 * x :=
    (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
  have hshift : ∀ i, (h i : ℝ) ≤ x := by
    intro i
    exact (Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ i))).trans
      ((le_max_right _ _).trans hx)
  let v : ι → ℕ := fun i => n + h i
  have hv : ∀ i, v i ≠ 0 := by
    intro i
    have hn0 : 0 < n := Nat.cast_pos.mp (hx0.trans_le hnx)
    exact (Nat.add_pos_left hn0 _).ne'
  have hvmax : ∀ i, (v i : ℝ) ≤ 3 * x := by
    intro i
    dsimp [v]
    push_cast
    linarith [hshift i]
  let N := ∏ i, v i
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
  have hprod : (N : ℝ) ≤ (3 * x) ^ Fintype.card ι := by
    calc
      (N : ℝ) = ∏ i, (v i : ℝ) := by simp [N]
      _ ≤ ∏ _i : ι, 3 * x :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hvmax i)
      _ = _ := by simp
  have hpw := Real.rpow_le_rpow (Nat.cast_nonneg N) hprod hη.le
  rw [← Real.rpow_natCast_mul (by positivity) (Fintype.card ι) η,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hx0.le] at hpw
  have hpw' : (N : ℝ) ^ η ≤ (3 : ℝ) ^ t * x ^ ε :=
    hpw.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1 ht) (by positivity))
  calc
    |∑ d ∈ D, if ∀ i, d i ∣ n + h i then selbergCoefficient y d else 0| ≤
        K * ((2 : ℝ) ^ N.primeFactors.card) ^ (Fintype.card ι + 1) :=
      selberg_divisor_root_abs_le_primeFactor_power y D v hv K hK hbound
    _ ≤ K * (C * (N : ℝ) ^ η) := by
      rw [pow_right_comm]
      exact mul_le_mul_of_nonneg_left (hCbound N hN) hK
    _ ≤ K * (C * ((3 : ℝ) ^ t * x ^ ε)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpw' hC.le) hK
    _ = K * (C * (3 : ℝ) ^ t * x ^ ε) := by ring
    _ ≤ (K + 1) * (C * (3 : ℝ) ^ t * x ^ ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ((K + 1) * C * (3 : ℝ) ^ t) * x ^ ε := by ring

theorem weighted_primePower_error_le {S : Finset ℕ} {X : ℝ}
    {w : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hS : S ⊆ Finset.Ioc 0 ⌊X⌋₊) (hw : ∀ n ∈ S, |w n| ≤ M) :
    |∑ n ∈ S, (ArithmeticFunction.vonMangoldt n -
        (if Nat.Prime n then Real.log (n : ℝ) else 0)) * w n| ≤
      M * (Chebyshev.psi X - Chebyshev.theta X) := by
  classical
  have heq : (∑ n ∈ S, (ArithmeticFunction.vonMangoldt n -
      (if Nat.Prime n then Real.log (n : ℝ) else 0)) * w n) =
      ∑ n ∈ S.filter (fun n => ¬Nat.Prime n), ArithmeticFunction.vonMangoldt n * w n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : Nat.Prime n
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp]
  rw [heq]
  calc
    |∑ n ∈ S.filter (fun n => ¬Nat.Prime n), ArithmeticFunction.vonMangoldt n * w n| ≤
        ∑ n ∈ S.filter (fun n => ¬Nat.Prime n),
          |ArithmeticFunction.vonMangoldt n * w n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S.filter (fun n => ¬Nat.Prime n), ArithmeticFunction.vonMangoldt n * M := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (hw n (Finset.mem_filter.mp hn).1)
        ArithmeticFunction.vonMangoldt_nonneg
    _ = M * ∑ n ∈ S.filter (fun n => ¬Nat.Prime n),
        ArithmeticFunction.vonMangoldt n := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ M * ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬Nat.Prime n),
        ArithmeticFunction.vonMangoldt n := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset_filter _ hS
      · intro n _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = M * (Chebyshev.psi X - Chebyshev.theta X) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]

open Classical in
theorem selberg_mixed_primePower_correction_uniform_log_saving
    {k : ℕ} (h : Fin (k + 1) → ℕ) (i : Fin (k + 1))
    (K₁ K₂ A : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (y : (Fin (k + 1) → ℕ) →₀ ℝ) (z : (Fin k → ℕ) →₀ ℝ)
        (D : Finset (Fin (k + 1) → ℕ)) (E : Finset (Fin k → ℕ))
        (W v : ℕ),
        (∀ d ∈ D,
          |selbergCoefficient y d| ≤
            K₁ * ((∏ j, d j : ℕ) : ℝ) / ((∏ j, d j : ℕ).totient : ℝ)) →
        (∀ e ∈ E,
          |selbergCoefficient z e| ≤
            K₂ * ((∏ j, e j : ℕ) : ℝ) / ((∏ j, e j : ℕ).totient : ℝ)) →
        let I := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
        let Dface := D.filter (fun d => d i = 1)
        let outerRoot : ℕ → ℝ := fun n =>
          ∑ d ∈ D, if ∀ j, d j ∣ n + h j then selbergCoefficient y d else 0
        let faceRoot : ℕ → ℝ := fun n =>
          ∑ d ∈ Dface,
            if ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)
            then selbergCoefficient y d else 0
        let innerRoot : ℕ → ℝ := fun n =>
          ∑ e ∈ E, if ∀ j, e j ∣ n + h (i.succAbove j)
            then selbergCoefficient z e else 0
        (Real.log x) ^ A / x *
          |∑ n ∈ I, if Nat.ModEq W n v then
            (ArithmeticFunction.vonMangoldt (n + h i) -
              (if Nat.Prime (n + h i) then Real.log ((n + h i : ℕ) : ℝ) else 0)) *
              (outerRoot n - faceRoot n) * innerRoot n else 0| ≤ ε := by
  intro ε hε
  obtain ⟨C₁, hC₁, hroot₁⟩ :=
    selberg_divisor_root_uniform_subpower h K₁ (1 / 8) hK₁ (by norm_num)
  obtain ⟨C₂, hC₂, hroot₂⟩ :=
    selberg_divisor_root_uniform_subpower (fun j => h (i.succAbove j))
      K₂ (1 / 8) hK₂ (by norm_num)
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  let M := 2 * C₁ * C₂
  have hM : 0 ≤ M := by positivity
  let B := M * C * Real.sqrt 3
  have hB : 0 ≤ B := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 1 / 4)).def
    (div_pos hε (by positivity : 0 < B + 1))
  filter_upwards [hroot₁, hroot₂, Filter.eventually_ge_atTop (max (2 : ℝ) (h i : ℝ)),
    hlog] with x hx₁ hx₂ hx hxlog
  intro y z D E W v hy hz
  let I := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let Dface := D.filter (fun d => d i = 1)
  let U : ℕ → ℝ := fun n =>
    ∑ d ∈ D, if ∀ j, d j ∣ n + h j then selbergCoefficient y d else 0
  let V : ℕ → ℝ := fun n =>
    ∑ d ∈ Dface, if ∀ j : Fin k, d (i.succAbove j) ∣ n + h (i.succAbove j)
      then selbergCoefficient y d else 0
  let T : ℕ → ℝ := fun n =>
    ∑ e ∈ E, if ∀ j, e j ∣ n + h (i.succAbove j) then selbergCoefficient z e else 0
  let w : ℕ → ℝ := fun n => if Nat.ModEq W n v then (U n - V n) * T n else 0
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hshift : (h i : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hface : ∀ n, V n =
      ∑ d ∈ Dface, if ∀ j, d j ∣ n + h j then selbergCoefficient y d else 0 := by
    intro n
    apply Finset.sum_congr rfl
    intro d hd
    have hdi := (Finset.mem_filter.mp hd).2
    simp only [Fin.forall_iff_succAbove i, hdi, one_dvd, true_and]
  have hw : ∀ n ∈ I, |w n| ≤ M * x ^ (1 / 4 : ℝ) := by
    intro n hn
    have hu : |U n| ≤ C₁ * x ^ (1 / 8 : ℝ) := by
      convert hx₁ y D n hn hy using 1
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => (ite_eq_ite _ _ _).mpr True.intro)
    have hv : |V n| ≤ C₁ * x ^ (1 / 8 : ℝ) := by
      rw [hface]
      convert hx₁ y Dface n hn (fun d hd => hy d (Finset.mem_filter.mp hd).1) using 1
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => (ite_eq_ite _ _ _).mpr True.intro)
    have ht : |T n| ≤ C₂ * x ^ (1 / 8 : ℝ) := by
      convert hx₂ z E n hn hz using 1
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => (ite_eq_ite _ _ _).mpr True.intro)
    have huv : |U n - V n| ≤ 2 * C₁ * x ^ (1 / 8 : ℝ) := by
      linarith [abs_sub (U n) (V n)]
    dsimp only [w]
    split_ifs
    · rw [abs_mul]
      calc
        |U n - V n| * |T n| ≤
            (2 * C₁ * x ^ (1 / 8 : ℝ)) * (C₂ * x ^ (1 / 8 : ℝ)) :=
          mul_le_mul huv ht (abs_nonneg _) (by positivity)
        _ = M * (x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ)) := by dsimp [M]; ring
        _ = M * x ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
    · simpa using mul_nonneg hM (Real.rpow_nonneg hx0.le (1 / 4))
  let S := I.image (fun n => n + h i)
  have hS : S ⊆ Finset.Ioc 0 ⌊3 * x⌋₊ := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hnlo : x ≤ (n : ℝ) := Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1
    have hnhi : (n : ℝ) ≤ 2 * x :=
      (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
    apply Finset.mem_Ioc.mpr
    constructor
    · exact Nat.add_pos_left (Nat.cast_pos.mp (hx0.trans_le hnlo)) _
    · apply Nat.le_floor
      push_cast
      linarith
  have hwS : ∀ m ∈ S, |w (m - h i)| ≤ M * x ^ (1 / 4 : ℝ) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    simpa only [Nat.add_sub_cancel] using hw n hn
  have hsum : (∑ n ∈ I, if Nat.ModEq W n v then
      (ArithmeticFunction.vonMangoldt (n + h i) -
        (if Nat.Prime (n + h i) then Real.log ((n + h i : ℕ) : ℝ) else 0)) *
        (U n - V n) * T n else 0) =
      ∑ m ∈ S, (ArithmeticFunction.vonMangoldt m -
        (if Nat.Prime m then Real.log (m : ℝ) else 0)) * w (m - h i) := by
    dsimp only [S]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n _
      simp only [Nat.add_sub_cancel, w, mul_ite, mul_zero, mul_assoc]
    · intro a _ b _ hab
      exact Nat.add_right_cancel hab
  have herr := weighted_primePower_error_le
    (mul_nonneg hM (Real.rpow_nonneg hx0.le (1 / 4))) hS hwS
  have hcheb : Chebyshev.psi (3 * x) - Chebyshev.theta (3 * x) ≤
      C * Real.sqrt (3 * x) :=
    (hC₀ (3 * x)).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.sqrt_nonneg _))
  have herr' : |∑ m ∈ S, (ArithmeticFunction.vonMangoldt m -
      (if Nat.Prime m then Real.log (m : ℝ) else 0)) * w (m - h i)| ≤
      B * x ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ (M * x ^ (1 / 4 : ℝ)) * (C * Real.sqrt (3 * x)) :=
        herr.trans (mul_le_mul_of_nonneg_left hcheb (by positivity))
      _ = B * (x ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_eq_rpow x]
        dsimp [B]
        ring
      _ = B * x ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  have hlog0 : 0 ≤ (Real.log x) ^ A :=
    Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hlogbound : (Real.log x) ^ A ≤ ε / (B + 1) * x ^ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hx0.le (1 / 4))] using hxlog
  have hscale : ε / (B + 1) * B ≤ ε := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < B + 1)).mpr
    nlinarith
  change (Real.log x) ^ A / x * |∑ n ∈ I, if Nat.ModEq W n v then
    (ArithmeticFunction.vonMangoldt (n + h i) -
      (if Nat.Prime (n + h i) then Real.log ((n + h i : ℕ) : ℝ) else 0)) *
      (U n - V n) * T n else 0| ≤ ε
  rw [hsum, div_mul_eq_mul_div]
  apply (div_le_iff₀ hx0).mpr
  calc
    _ ≤ (ε / (B + 1) * x ^ (1 / 4 : ℝ)) * (B * x ^ (3 / 4 : ℝ)) :=
      mul_le_mul hlogbound herr' (abs_nonneg _) (by positivity)
    _ = (ε / (B + 1) * B) * (x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) := by ring
    _ = (ε / (B + 1) * B) * x := by rw [← Real.rpow_add hx0]; norm_num
    _ ≤ ε * x := mul_le_mul_of_nonneg_right hscale hx0.le

open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

theorem selbergCoefficient_abs_le_totient_ratio
    {ι : Type*} [Fintype ι] (Q : ℕ) (hQ : Squarefree Q)
    (y : (ι → ℕ) →₀ ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hy : ∀ r ∈ y.support,
      Squarefree (∏ j, r j) ∧ ∀ j, r j ∣ Q)
    (hbound : ∀ r, |y r| ≤ B) (d : ι → ℕ) :
    let D : ℕ := ∏ j, d j
    |selbergCoefficient y d| ≤
      B * ((D : ℝ) / (D.totient : ℝ)) *
        (∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹) ^ Fintype.card ι := by
  classical
  intro D
  by_cases hD : Squarefree D
  · let S := y.support.filter (fun r => ∀ j, d j ∣ r j)
    let U := Fintype.piFinset (fun _ : ι => Q.divisors)
    let q : (ι → ℕ) → ι → ℕ := fun r j => r j / d j
    have hphiD : (D.totient : ℝ) = ∏ j, ((d j).totient : ℝ) := by
      have h := ArithmeticFunction.IsMultiplicative.map_prod d
        (f := (⟨Nat.totient, Nat.totient_zero⟩ : ArithmeticFunction ℕ))
        ⟨Nat.totient_one, fun {m n} hc => Nat.totient_mul hc⟩ Finset.univ
        (fun i _ j _ hij => coprime_of_squarefree_fintype_prod d hD hij)
      exact_mod_cast h
    have hsplit (r : ι → ℕ) (hr : r ∈ S) :
        (∏ j, ((r j).totient : ℝ)) =
          (D.totient : ℝ) * ∏ j, ((q r j).totient : ℝ) := by
      have hrs := (Finset.mem_filter.mp hr).1
      have hdr := (Finset.mem_filter.mp hr).2
      calc
        (∏ j, ((r j).totient : ℝ)) =
            ∏ j, (((d j).totient : ℝ) * ((q r j).totient : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          have hrec : d j * q r j = r j := Nat.mul_div_cancel' (hdr j)
          have hrj : Squarefree (r j) :=
            (hy r hrs).1.squarefree_of_dvd (Finset.dvd_prod_of_mem r (Finset.mem_univ j))
          have hc : Nat.Coprime (d j) (q r j) := by
            apply Nat.coprime_of_squarefree_mul
            rwa [hrec]
          exact_mod_cast
            (congrArg Nat.totient hrec).symm.trans (Nat.totient_mul hc)
        _ = (D.totient : ℝ) * ∏ j, ((q r j).totient : ℝ) := by
          rw [Finset.prod_mul_distrib, ← hphiD]
    have hq : Set.InjOn q (S : Set (ι → ℕ)) := by
      intro r hr s hs hrs
      funext j
      calc
        r j = d j * q r j :=
          (Nat.mul_div_cancel' ((Finset.mem_filter.mp hr).2 j)).symm
        _ = d j * q s j := by rw [hrs]
        _ = s j := Nat.mul_div_cancel' ((Finset.mem_filter.mp hs).2 j)
    have hqU : S.image q ⊆ U := Finset.image_subset_iff.mpr fun r hr => by
      apply Fintype.mem_piFinset.mpr
      intro j
      exact Nat.mem_divisors.mpr
        ⟨(Nat.div_dvd_of_dvd ((Finset.mem_filter.mp hr).2 j)).trans
          ((hy r (Finset.mem_filter.mp hr).1).2 j), hQ.ne_zero⟩
    have hweight :
        (∑ r ∈ S, ∏ j, ((q r j).totient : ℝ)⁻¹) ≤
          ∑ s ∈ U, ∏ j, ((s j).totient : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_injOn q hq hqU
      · intro r _
        exact le_rfl
      · intro s _ _
        exact Finset.prod_nonneg fun j _ => inv_nonneg.mpr (Nat.cast_nonneg _)
    have hbox :
        (∑ s ∈ U, ∏ j, ((s j).totient : ℝ)⁻¹) =
          (∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹) ^ Fintype.card ι := by
      simpa [U] using (Finset.sum_prod_piFinset Q.divisors
        (fun (_ : ι) (r : ℕ) => (r.totient : ℝ)⁻¹))
    have hsum :
        y.sum (fun r yr =>
          if ∀ j, d j ∣ r j then yr / (∏ j, ((r j).totient : ℝ)) else 0) =
          ∑ r ∈ S, y r / (∏ j, ((r j).totient : ℝ)) := by
      simp only [S, Finset.sum_filter, Finsupp.sum]
    have hinner :
        |∑ r ∈ S, y r / (∏ j, ((r j).totient : ℝ))| ≤
          (B / (D.totient : ℝ)) *
            (∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹) ^ Fintype.card ι := by
      calc
        |∑ r ∈ S, y r / (∏ j, ((r j).totient : ℝ))| ≤
            ∑ r ∈ S, |y r / (∏ j, ((r j).totient : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ S,
            (B / (D.totient : ℝ)) * ∏ j, ((q r j).totient : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro r hr
          rw [abs_div, abs_of_nonneg
            (show 0 ≤ ∏ j, ((r j).totient : ℝ) from
              Finset.prod_nonneg (fun j _ => Nat.cast_nonneg ((r j).totient))), hsplit r hr]
          calc
            |y r| / ((D.totient : ℝ) * ∏ j, ((q r j).totient : ℝ)) ≤
                B / ((D.totient : ℝ) * ∏ j, ((q r j).totient : ℝ)) :=
              div_le_div_of_nonneg_right (hbound r)
                (mul_nonneg (Nat.cast_nonneg _)
                  (Finset.prod_nonneg fun j _ => Nat.cast_nonneg ((q r j).totient)))
            _ = (B / (D.totient : ℝ)) * ∏ j, ((q r j).totient : ℝ)⁻¹ := by
              simp only [Finset.prod_inv_distrib, div_mul_eq_div_mul_one_div, one_div]
        _ = (B / (D.totient : ℝ)) *
            ∑ r ∈ S, ∏ j, ((q r j).totient : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
        _ ≤ (B / (D.totient : ℝ)) *
            (∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹) ^ Fintype.card ι := by
          simpa only [hbox] using
            mul_le_mul_of_nonneg_left hweight (div_nonneg hB (Nat.cast_nonneg _))
    have hmu : |(ArithmeticFunction.moebius D : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hD
    calc
      |selbergCoefficient y d| =
          (D : ℝ) * |∑ r ∈ S, y r / (∏ j, ((r j).totient : ℝ))| := by
        unfold selbergCoefficient
        rw [hsum, ← Nat.cast_prod d Finset.univ, abs_mul, abs_mul, hmu,
          abs_of_nonneg (Nat.cast_nonneg D), one_mul]
      _ ≤ (D : ℝ) * ((B / (D.totient : ℝ)) *
          (∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹) ^ Fintype.card ι) :=
        mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg D)
      _ = B * ((D : ℝ) / (D.totient : ℝ)) *
          (∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹) ^ Fintype.card ι := by
        ring
  · have hmu : ArithmeticFunction.moebius (∏ j, d j) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hD
    simpa only [selbergCoefficient, hmu, Int.cast_zero, zero_mul, abs_zero] using
      (show 0 ≤ B * ((D : ℝ) / (D.totient : ℝ)) *
        (∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹) ^ Fintype.card ι by positivity)

open Classical in
theorem selberg39_canonical_erased_coefficient_bound
    {𝓗 : Finset ℕ}
    (M : ℝ) (hM : 0 ≤ M) :
    let ρ : ℝ := 2624989 / 10000000
    let ξ₀ : ℝ := 19037 / 100000
    let κ : ℝ := ξ₀ / ρ
    let C : ℝ := Real.exp Real.eulerMascheroniConstant * κ + 1
    ∀ᶠ x : ℝ in Filter.atTop,
      let W := presievingModulus 𝓗 x
      let R := x ^ ρ
      let B := fragmentNormalization W R
      let M_R := harmonicFragmentMass W R κ
      let P := fragmentPrimes W R κ
      let Q := ∏ p ∈ P, p
      let T := (Fintype.piFinset (fun _ : Fin 39 => Q.divisors)).filter
        (fun r => Squarefree (∏ j, r j))
      1 < x ∧ 0 < B ∧ 0 < M_R ∧ M_R / B ≤ C ∧
        R ^ κ = x ^ ξ₀ ∧
        ∀ F : (Fin 39 → MeasureTheory.FiniteMeasure ℝ) → ℝ,
          (∀ X, |F X| ≤ M) →
          let y : (Fin 39 → ℕ) →₀ ℝ :=
            ∑ r ∈ T, Finsupp.single r
              (F (fun j => primeLogConfiguration R (r j)) / B ^ 39)
          (∀ d : Fin 39 → ℕ,
            let D : ℕ := ∏ j, d j
            |selbergCoefficient y d| ≤
                M * (M_R / B) ^ 39 * ((D : ℝ) / (D.totient : ℝ)) ∧
              |selbergCoefficient y d| ≤
                M * C ^ 39 * ((D : ℝ) / (D.totient : ℝ))) ∧
          ∀ i : Fin 39,
            let z : (Fin 38 → ℕ) →₀ ℝ :=
              y.sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
                (yr / ((r i).totient : ℝ)))
            ∀ d : Fin 38 → ℕ,
              let D : ℕ := ∏ j, d j
              selbergCoefficient z d = selbergCoefficient y (i.insertNth 1 d) ∧
                |selbergCoefficient z d| ≤
                  M * (M_R / B) ^ 39 * ((D : ℝ) / (D.totient : ℝ)) ∧
                |selbergCoefficient z d| ≤
                  M * C ^ 39 * ((D : ℝ) / (D.totient : ℝ)) := by
  intro ρ ξ₀ κ C
  have hρ : 0 < ρ := by norm_num [ρ]
  have hκ : 0 < κ := by norm_num [κ, ξ₀, ρ]
  have hm := harmonic_fragment_normalizer_tendsto
    𝓗 ρ κ hρ hκ
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hm.eventually_le_const (lt_add_one _)] with x hx hm
  intro W R B M_R P Q T
  have hW : 0 < W := presieving_pos 𝓗 x
  have hB : 0 < B := by
    apply mul_pos
    · exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
    · exact Real.log_pos (Real.one_lt_rpow hx hρ)
  have hQ : Squarefree Q :=
    squarefree_prime_prod P
      (fun _ hp => Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
  have hmass_eq : M_R = ∑ r ∈ Q.divisors, (r.totient : ℝ)⁻¹ := rfl
  have hmass : 0 < M_R := by
    rw [hmass_eq]
    exact Finset.sum_pos' (fun r _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      ⟨1, Nat.one_mem_divisors.mpr hQ.ne_zero, by norm_num⟩
  change M_R / B ≤ C at hm
  have hcap : R ^ κ = x ^ ξ₀ := by
    change (x ^ ρ) ^ κ = x ^ ξ₀
    rw [← Real.rpow_mul (zero_lt_one.trans hx).le]
    norm_num [κ, ξ₀, ρ]
  refine ⟨hx, hB, hmass, hm, hcap, ?_⟩
  intro F hF y
  have hyIndicator : y = Finsupp.indicator T (fun r _ =>
      F (fun j => primeLogConfiguration R (r j)) / B ^ 39) :=
    (Finsupp.indicator_eq_sum_single T _).symm
  have hySupport (r : Fin 39 → ℕ) (hr : r ∈ y.support) :
      Squarefree (∏ j, r j) ∧ ∀ j, r j ∣ Q := by
    rw [hyIndicator] at hr
    obtain ⟨hrbox, hrsquarefree⟩ := Finset.mem_filter.mp
      (Finsupp.support_indicator_subset _ _ hr)
    exact ⟨hrsquarefree, fun j =>
      Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hrbox j)⟩
  have hyBound (r : Fin 39 → ℕ) : |y r| ≤ M / B ^ 39 := by
    rw [hyIndicator, Finsupp.indicator_apply]
    split_ifs
    · rw [abs_div, abs_of_pos (pow_pos hB 39)]
      exact div_le_div_of_nonneg_right (hF _) (pow_nonneg hB.le 39)
    · simpa only [abs_zero] using div_nonneg hM (pow_nonneg hB.le 39)
  have hbound40 (d : Fin 39 → ℕ) :
      let D : ℕ := ∏ j, d j
      |selbergCoefficient y d| ≤
          M * (M_R / B) ^ 39 * ((D : ℝ) / (D.totient : ℝ)) ∧
        |selbergCoefficient y d| ≤
          M * C ^ 39 * ((D : ℝ) / (D.totient : ℝ)) := by
    intro D
    have hfinite : |selbergCoefficient y d| ≤
        (M / B ^ 39) * ((D : ℝ) / (D.totient : ℝ)) * M_R ^ 39 := by
      rw [hmass_eq]
      dsimp only [D]
      simpa only [Fintype.card_fin] using
        selbergCoefficient_abs_le_totient_ratio Q hQ y (M / B ^ 39)
          (div_nonneg hM (pow_nonneg hB.le 39)) hySupport hyBound d
    have hratio : |selbergCoefficient y d| ≤
        M * (M_R / B) ^ 39 * ((D : ℝ) / (D.totient : ℝ)) :=
      hfinite.trans_eq (by simp only [div_eq_mul_inv]; ring)
    refine ⟨hratio, hratio.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hmass.le hB.le) hm 39) hM)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine ⟨hbound40, ?_⟩
  intro i z d D
  have heq : selbergCoefficient z d = selbergCoefficient y (i.insertNth 1 d) :=
    selbergCoefficient_weighted_erase i y d
  refine ⟨heq, ?_⟩
  simpa only [heq, Fin.prod_insertNth, one_mul] using hbound40 (i.insertNth 1 d)

end PrimeGap182.Selberg

theorem PrimeGap182.Selberg.selberg_actual_modulus_totient_eq
    {k : ℕ} (W : ℕ) (hW : 0 < W) (d e : Fin k → ℕ)
    (hd : Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W)
    (he : Squarefree (∏ i, e i) ∧ Nat.Coprime (∏ i, e i) W)
    (hcross : ∀ i j : Fin k, i ≠ j → Nat.Coprime (d i) (e j)) :
    Nat.totient (Nat.lcm W (Nat.lcm (∏ i, d i) (∏ i, e i))) =
      Nat.totient W * ∏ i, Nat.totient (Nat.lcm (d i) (e i)) := by
  classical
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hW.ne'
  rw [PrimeGap182.Selberg.actual_modulus_eq_product w.succ d e hd he hcross,
    Nat.totient_mul (PrimeGap182.Selberg.actual_modulus_coprime_W_prod_lcm
      w.succ d e hd.2 he.2)]
  congr 1
  let φ : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
  have hφ : φ.IsMultiplicative :=
    ⟨Nat.totient_one, fun {_ _} h => Nat.totient_mul h⟩
  exact ArithmeticFunction.IsMultiplicative.map_prod
    (fun i : Fin k => Nat.lcm (d i) (e i)) hφ Finset.univ
    (PrimeGap182.Selberg.actual_modulus_pairwise_coprime_lcm d e hd.1 he.1 hcross)

section
open scoped ContDiff

theorem PrimeGap182.Selberg.selberg_diagonal_support_le_of_coefficient_le
    {ι : Type*} [Fintype ι] (y : (ι → ℕ) →₀ ℝ)
    (hy : ∀ r ∈ y.support, Squarefree (∏ j, r j))
    (B : ℝ)
    (hcoeff : ∀ d : ι → ℕ, PrimeGap182.Selberg.selbergCoefficient y d ≠ 0 →
      ((∏ j, d j : ℕ) : ℝ) ≤ B) :
    ∀ r ∈ y.support, ((∏ j, r j : ℕ) : ℝ) ≤ B := by
  intro r hr
  have hnz : y r ≠ 0 := Finsupp.mem_support_iff.mp hr
  rw [← PrimeGap182.Selberg.selberg_forward_inverse y hy r] at hnz
  obtain ⟨d, _, hterm⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (mul_ne_zero_iff.mp hnz).2
  obtain ⟨hrd, hquot⟩ := ite_ne_right_iff.mp hterm
  have hdpos : 0 < ∏ j, d j :=
    Nat.pos_of_ne_zero (by exact_mod_cast (div_ne_zero_iff.mp hquot).2)
  have hle : (∏ j, r j) ≤ ∏ j, d j :=
    Nat.le_of_dvd hdpos
      (Finset.prod_dvd_prod_of_dvd r d (fun j _ => hrd j))
  exact (Nat.cast_le.mpr hle).trans (hcoeff d (div_ne_zero_iff.mp hquot).1)

theorem PrimeGap182.Selberg.selberg_eventually_eq_zero_of_coefficient_radius_neg
    {ι : Type*} [Fintype ι] (y : ℝ → ((ι → ℕ) →₀ ℝ))
    (r_c : ℝ) (hr_c : r_c < 0)
    (hy : ∀ᶠ x : ℝ in Filter.atTop,
      ∀ r ∈ (y x).support, Squarefree (∏ j, r j))
    (hcoeff : ∀ᶠ x : ℝ in Filter.atTop,
      ∀ d : ι → ℕ, PrimeGap182.Selberg.selbergCoefficient (y x) d ≠ 0 →
        ((∏ j, d j : ℕ) : ℝ) ≤ x ^ r_c) :
    ∀ᶠ x : ℝ in Filter.atTop, y x = 0 := by
  filter_upwards [hy, hcoeff, Filter.eventually_gt_atTop (1 : ℝ)] with x hyx hcx hx
  apply Finsupp.support_eq_empty.mp
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  have hpos : (1 : ℝ) ≤ ((∏ j, r j : ℕ) : ℝ) :=
    Nat.one_le_cast_iff_ne_zero.mpr (hyx r hr).ne_zero
  exact (not_lt_of_ge hpos)
    ((PrimeGap182.Selberg.selberg_diagonal_support_le_of_coefficient_le
      (y x) hyx (x ^ r_c) hcx r hr).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hx hr_c))

end

namespace PrimeGap182.Selberg

section
open scoped ContDiff

theorem selbergCoefficient_add
    {ι : Type*} [Fintype ι]
    (y z : (ι → ℕ) →₀ ℝ) (d : ι → ℕ) :
    selbergCoefficient (y + z) d =
      selbergCoefficient y d + selbergCoefficient z d := by
  unfold selbergCoefficient
  rw [Finsupp.sum_add_index' (fun r => by simp)
    (fun r a b => by split_ifs <;> simp [add_div]), mul_add]

open Classical in
theorem canonical_and_erased_diagonal_amplitude
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {m : ℕ} (i : Fin 39) (κ : ℝ) (hκ : 0 < κ)
    (a : Fin (m + 2) → ℝ)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hbG : Bornology.IsBounded (Set.range G))
    (hbF : Bornology.IsBounded (Set.range F)) :
    ∃ M : ℝ, 0 < M ∧
      ∀ᶠ x : ℝ in Filter.atTop,
      let ρ : ℝ := 2624989 / 10000000
      let W := presievingModulus 𝓗 x
      let R := x ^ ρ
      let B := fragmentNormalization W R
      let q : ℕ := ∏ p ∈ fragmentPrimes W R κ, p
      let T39 := (Fintype.piFinset (fun _ : Fin 38 => q.divisors)).filter
        (fun r => Squarefree (∏ j, r j))
      let T40 := (Fintype.piFinset (fun _ : Fin 39 => q.divisors)).filter
        (fun r => Squarefree (∏ j, r j))
      let X : ℕ → Fin (m + 1) → ℝ := fun s =>
        fragmentBandMasses a (primeLogConfiguration R s)
      let w : (Fin 38 → ℕ) →₀ ℝ :=
        ∑ r ∈ T39, Finsupp.single r (G (fun j => X (r j)) / B ^ 38)
      let y : (Fin 39 → ℕ) →₀ ℝ :=
        ∑ r ∈ T40, Finsupp.single r (F (fun j => X (r j)) / B ^ 39)
      let e : (Fin 38 → ℕ) →₀ ℝ :=
        y.sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
          (yr / ((r i).totient : ℝ)))
      let z : (Fin 38 → ℕ) →₀ ℝ := w + e
      1 < x ∧ 0 < B ∧
      (∀ r : Fin 38 → ℕ,
        w r = if r ∈ T39 then G (fun j => X (r j)) / B ^ 38 else 0) ∧
      (∀ r : Fin 38 → ℕ,
        r ∈ w.support ↔ r ∈ T39 ∧ G (fun j => X (r j)) ≠ 0) ∧
      (∀ r ∈ w.support,
        Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) ∧
      (∀ r ∈ y.support,
        Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) ∧
      (∀ d : Fin 38 → ℕ,
        selbergCoefficient e d = selbergCoefficient y (i.insertNth 1 d)) ∧
      (∀ d : Fin 38 → ℕ,
        selbergCoefficient z d =
          selbergCoefficient w d + selbergCoefficient y (i.insertNth 1 d)) ∧
      (∀ r ∈ z.support,
        Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) ∧
      (∀ r : Fin 38 → ℕ, |z r| ≤ M / B ^ 38) := by
  obtain ⟨MG, hMG, hGb⟩ := hbG.exists_pos_norm_le
  obtain ⟨MF, hMF, hFb⟩ := hbF.exists_pos_norm_le
  simp only [Real.norm_eq_abs] at hGb hFb
  let Cκ := Real.exp Real.eulerMascheroniConstant * κ + 1
  refine ⟨MG + MF * Cκ, by dsimp [Cκ]; positivity, ?_⟩
  filter_upwards [selberg39_canonical_erased_face
    (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ MF hκ hMF.le] with x hx
  intro ρ W R B q T39 T40 X w y e z
  obtain ⟨hx, hB, hface⟩ := hx
  obtain ⟨hy, _, hecoeff, _, hesupp, hebound⟩ :=
    hface (fun Y => F (fun j => fragmentBandMasses a (Y j)))
      (fun Y => hFb _ ⟨fun j => fragmentBandMasses a (Y j), rfl⟩)
  have hB39 : 0 < B ^ 38 := pow_pos hB 38
  have hw (r : Fin 38 → ℕ) :
      w r = if r ∈ T39 then G (fun j => X (r j)) / B ^ 38 else 0 := by
    simp [w, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hwmem (r : Fin 38 → ℕ) :
      r ∈ w.support ↔ r ∈ T39 ∧ G (fun j => X (r j)) ≠ 0 := by
    rw [Finsupp.mem_support_iff, hw]
    split_ifs with hr <;> simp [hr, hB39.ne']
  have hwsupp : ∀ r ∈ w.support,
      Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors := by
    intro r hr
    have ht := Finset.mem_filter.mp ((hwmem r).mp hr).1
    exact ⟨ht.2, Fintype.mem_piFinset.mp ht.1⟩
  refine ⟨hx, hB, hw, hwmem, hwsupp, ?_, hecoeff, ?_, ?_, ?_⟩
  · intro r hr
    have ht : r ∈ T40 := by
      by_contra hnot
      apply Finsupp.mem_support_iff.mp hr
      exact (hy r).trans (ite_eq_right hnot)
    exact ⟨(Finset.mem_filter.mp ht).2,
      Fintype.mem_piFinset.mp (Finset.mem_filter.mp ht).1⟩
  · intro d
    change selbergCoefficient (w + e) d = _
    rw [selbergCoefficient_add, hecoeff]
  · intro r hr
    rcases Finset.mem_union.mp (Finsupp.support_add hr) with hrw | hre
    · exact hwsupp r hrw
    · exact ⟨(hesupp r hre).1, (hesupp r hre).2.1⟩
  · intro r
    have hwbound : |w r| ≤ MG / B ^ 38 := by
      rw [hw]
      split_ifs
      · rw [abs_div, abs_of_pos hB39]
        exact div_le_div_of_nonneg_right (hGb _ ⟨fun j => X (r j), rfl⟩) hB39.le
      · simpa only [abs_zero] using div_nonneg hMG.le hB39.le
    calc
      |z r| = |w r + e r| := rfl
      _ ≤ |w r| + |e r| := abs_add_le _ _
      _ ≤ MG / B ^ 38 + MF * Cκ / B ^ 38 := add_le_add hwbound (hebound r).2
      _ = (MG + MF * Cκ) / B ^ 38 := (add_div _ _ _).symm

theorem uniform_scaled_error_of_normalized_tendsto
    {α : Type*} {l : Filter α} (S : α → ℕ → ℝ) (a b e : α → ℝ) (L : ℝ)
    (hpos : ∀ᶠ x in l, 0 ≤ a x ∧ 0 < b x)
    (hlim : Tendsto (fun x => b x * e x) l (nhds L))
    (herr : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ n : ℕ,
      |S x n - a x * e x| ≤ ε * (a x / b x)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ n : ℕ,
      |S x n - (a x / b x) * L| ≤ ε * (a x / b x) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall : ∀ᶠ x in l, |b x * e x - L| < ε / 2 := by
    simpa only [Real.norm_eq_abs] using
      hlim.eventually (eventually_norm_sub_lt L hhalf)
  filter_upwards [hpos, herr (ε / 2) hhalf, hsmall] with x hx he hs
  intro n
  have hscale : 0 ≤ a x / b x := div_nonneg hx.1 hx.2.le
  have hid : S x n - (a x / b x) * L =
      (S x n - a x * e x) + (a x / b x) * (b x * e x - L) := by
    field_simp [ne_of_gt hx.2]
    ring
  rw [hid]
  calc
    _ ≤ |S x n - a x * e x| + |(a x / b x) * (b x * e x - L)| :=
      abs_add_le _ _
    _ = |S x n - a x * e x| + (a x / b x) * |b x * e x - L| := by
      rw [abs_mul, abs_of_nonneg hscale]
    _ ≤ (ε / 2) * (a x / b x) + (a x / b x) * (ε / 2) :=
      add_le_add (he n) (mul_le_mul_of_nonneg_left hs.le hscale)
    _ = ε * (a x / b x) := by ring

end

section
open scoped ContDiff
open Classical in
theorem canonical_diagonal_finset_smul
    {J : Type*} {n m : ℕ} (s : Finset J) (c : J → ℝ)
    (T : Finset (Fin n → ℕ)) (U : ℕ → Fin (m + 1) → ℝ) (B : ℝ)
    (G : J → (Fin n → Fin (m + 1) → ℝ) → ℝ) :
    (∑ r ∈ T, Finsupp.single r
      ((∑ j ∈ s, c j * G j (fun k => U (r k))) / B ^ n)) =
      ∑ j ∈ s, c j •
        (∑ r ∈ T, Finsupp.single r (G j (fun k => U (r k)) / B ^ n)) := by
  simp_rw [Finset.sum_div, Finsupp.single_finsetSum]
  rw [Finset.sum_comm]
  simp_rw [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_div_assoc]

open Classical in
theorem weighted_erasure_finset_smul
    {J : Type*} {n : ℕ} (s : Finset J) (c : J → ℝ)
    (i : Fin (n + 1)) (y : J → ((Fin (n + 1) → ℕ) →₀ ℝ)) :
    (∑ j ∈ s, c j • y j).sum
        (fun r yr => Finsupp.single (fun k => r (i.succAbove k))
          (yr / ((r i).totient : ℝ))) =
      ∑ j ∈ s, c j • (y j).sum
        (fun r yr => Finsupp.single (fun k => r (i.succAbove k))
          (yr / ((r i).totient : ℝ))) := by
  rw [Finsupp.sum_finsetSum _ _ _ (fun _ => by simp)
    (fun _ _ _ => by simp [add_div, Finsupp.single_add])]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.sum_smul_index (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_div_assoc]

theorem selbergCoefficient_smul
    {ι : Type*} [Fintype ι] (a : ℝ) (y : (ι → ℕ) →₀ ℝ) (d : ι → ℕ) :
    selbergCoefficient (a • y) d = a * selbergCoefficient y d := by
  unfold selbergCoefficient
  rw [Finsupp.sum_smul_index (fun _ => by simp), mul_left_comm a]
  congr 1
  rw [Finsupp.mul_sum]
  simp only [Finsupp.sum, mul_ite, mul_div_assoc, mul_zero]

open Classical in
theorem selbergCoefficient_finset_combination
    {ι J : Type*} [Fintype ι] (s : Finset J) (c : J → ℝ)
    (y : J → ((ι → ℕ) →₀ ℝ)) :
    (∀ d : ι → ℕ,
      selbergCoefficient (∑ j ∈ s, c j • y j) d =
        ∑ j ∈ s, c j * selbergCoefficient (y j) d) ∧
    (∀ d : ι → ℕ,
      selbergCoefficient (∑ j ∈ s, c j • y j) d ≠ 0 →
        ∃ j ∈ s, c j ≠ 0 ∧ selbergCoefficient (y j) d ≠ 0) := by
  have hlinear (d : ι → ℕ) :
      selbergCoefficient (∑ j ∈ s, c j • y j) d =
        ∑ j ∈ s, c j * selbergCoefficient (y j) d := by
    induction s using Finset.induction_on with
    | empty => simp [selbergCoefficient]
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj, selbergCoefficient_add, selbergCoefficient_smul, ih]
  refine ⟨hlinear, ?_⟩
  intro d hd
  rw [hlinear] at hd
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  exact ⟨j, hj, mul_ne_zero_iff.mp hne⟩

open Classical in
theorem selbergCoefficient_finset_radius
    {ι J : Type*} [Fintype ι] (s : Finset J) (c : J → ℝ)
    (y : J → ((ι → ℕ) →₀ ℝ)) (d : ι → ℕ) (B : ℝ)
    (hindividual : ∀ j ∈ s, selbergCoefficient (y j) d ≠ 0 →
      ((∏ k, d k : ℕ) : ℝ) ≤ B)
    (haggregate : selbergCoefficient (∑ j ∈ s, c j • y j) d ≠ 0) :
    ((∏ k, d k : ℕ) : ℝ) ≤ B := by
  obtain ⟨j, hj, _, hd⟩ :=
    (selbergCoefficient_finset_combination s c y).2 d haggregate
  exact hindividual j hj hd

theorem finite_profile_combination_regular
    {E J : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) (s : Finset J) (c : J → ℝ) (G : J → E → ℝ)
    (hG : ∀ j ∈ s, Measurable (G j))
    (hbG : ∀ j ∈ s, Bornology.IsBounded (Set.range (G j)))
    (hcG : ∀ j ∈ s, ∀ᵐ X ∂μ, ContinuousAt (G j) X) :
    Measurable (fun X => ∑ j ∈ s, c j * G j X) ∧
      Bornology.IsBounded (Set.range (fun X => ∑ j ∈ s, c j * G j X)) ∧
      (∀ᵐ X ∂μ, ContinuousAt (fun Y => ∑ j ∈ s, c j * G j Y) X) := by
  classical
  refine ⟨Finset.measurable_fun_sum _ (fun j hj => measurable_const.mul (hG j hj)), ?_, ?_⟩
  · clear hG hcG
    revert hbG
    induction s using Finset.induction_on with
    | empty =>
      intro _
      apply isBounded_iff_forall_norm_le.mpr
      exact ⟨0, by rintro _ ⟨X, rfl⟩; simp⟩
    | @insert j s hj ih =>
      intro hbG
      have hsmall := ih (fun k hk => hbG k (Finset.mem_insert_of_mem hk))
      have hsingle : Bornology.IsBounded (Set.range (fun X => c j * G j X)) := by
        simpa only [← smul_eq_mul, Set.range_smul] using
          (hbG j (Finset.mem_insert_self j s)).smul₀ (c j)
      apply (isBounded_add hsingle hsmall).subset
      rintro _ ⟨X, rfl⟩
      exact Set.mem_add.mpr ⟨c j * G j X, ⟨X, rfl⟩,
        ∑ k ∈ s, c k * G k X, ⟨X, rfl⟩, by simp only [Finset.sum_insert hj]⟩
  · filter_upwards [(Filter.eventually_all_finset s).2 hcG] with X hX
    exact tendsto_finsetSum s (fun j hj => continuousAt_const.mul (hX j hj))

open Classical in
theorem fixed_band_erased_finset_integral
    {J : Type*} {n m : ℕ} (s : Finset J) (c : J → ℝ)
    (i : Fin (n + 1)) (κ : ℝ) (a : Fin (m + 2) → ℝ)
    (F : J → (Fin (n + 1) → Fin (m + 1) → ℝ) → ℝ)
    (hF : ∀ j ∈ s, Measurable (F j))
    (hbF : ∀ j ∈ s, Bornology.IsBounded (Set.range (F j))) :
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    IsFiniteMeasure ν ∧
      (∀ j ∈ s, ∀ Y : Fin n → Fin (m + 1) → ℝ,
        Integrable (fun t => F j (i.insertNth t Y)) ν) ∧
      (∀ Y : Fin n → Fin (m + 1) → ℝ,
        Integrable (fun t => ∑ j ∈ s, c j * F j (i.insertNth t Y)) ν) ∧
      (∀ Y : Fin n → Fin (m + 1) → ℝ,
        (∫ t, (∑ j ∈ s, c j * F j (i.insertNth t Y)) ∂ν) =
          ∑ j ∈ s, c j * ∫ t, F j (i.insertNth t Y) ∂ν) := by
  intro ν
  let : IsProbabilityMeasure (fragmentLaw κ) :=
    fragmentLaw_isProbabilityMeasure κ
  let : IsFiniteMeasure ν := by
    dsimp [ν]
    exact (Measure.map (fragmentBandMasses a)
      (fragmentLaw κ)).smul_finite (by simp)
  have hslice (j : J) (hj : j ∈ s) (Y : Fin n → Fin (m + 1) → ℝ) :
      Integrable (fun t => F j (i.insertNth t Y)) ν := by
    exact integrable_of_measurable_of_bounded_range ν (fun t => F j (i.insertNth t Y))
      ((hF j hj).comp (by fun_prop))
      ((hbF j hj).subset (Set.range_comp_subset_range _ _))
  refine ⟨inferInstance, hslice, ?_, ?_⟩
  · intro Y
    exact integrable_finsetSum s (fun j hj => (hslice j hj Y).const_mul (c j))
  · intro Y
    rw [integral_finsetSum s (fun j hj => (hslice j hj Y).const_mul (c j))]
    simp only [integral_const_mul]

open Classical in
theorem selberg_divisor_root_finset_combination
    {ι J : Type*} [Fintype ι] (s : Finset J) (c : J → ℝ)
    (y : J → ((ι → ℕ) →₀ ℝ)) (v : ι → ℕ) :
    let z := ∑ j ∈ s, c j • y j
    let D := fun w : (ι → ℕ) →₀ ℝ =>
      w.support.biUnion (fun r => Fintype.piFinset (fun k => (r k).divisors))
    (∑ d ∈ D z, if ∀ k, d k ∣ v k then selbergCoefficient z d else 0) =
      ∑ j ∈ s, c j *
        (∑ d ∈ D (y j), if ∀ k, d k ∣ v k then selbergCoefficient (y j) d else 0) := by
  intro z D
  let K := D z ∪ s.biUnion (fun j => D (y j))
  have hroot (w : (ι → ℕ) →₀ ℝ) (hsub : D w ⊆ K) :
      (∑ d ∈ D w, if ∀ k, d k ∣ v k then selbergCoefficient w d else 0) =
        ∑ d ∈ K, if ∀ k, d k ∣ v k then selbergCoefficient w d else 0 := by
    apply Finset.sum_subset hsub
    intro d _ hd
    have hc : selbergCoefficient w d = 0 := by
      by_contra hne
      exact hd (selbergCoefficient_mem_divisorClosure w d hne)
    simp only [hc, ite_self]
  calc
    _ = ∑ d ∈ K, if ∀ k, d k ∣ v k then selbergCoefficient z d else 0 :=
      hroot z Finset.subset_union_left
    _ = ∑ d ∈ K, ∑ j ∈ s,
        c j * (if ∀ k, d k ∣ v k then selbergCoefficient (y j) d else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : ∀ k, d k ∣ v k
      · simp only [ite_eq_left hd]
        exact (selbergCoefficient_finset_combination s c y).1 d
      · simp only [ite_eq_right hd, mul_zero, Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum, ← hroot (y j) (fun d hd =>
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hd⟩))]

open Classical in
theorem canonical_and_erased_coefficient_root_subpower
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {m : ℕ} (i : Fin 39) (κ : ℝ) (hκ : 0 < κ)
    (a : Fin (m + 2) → ℝ)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hbG : Bornology.IsBounded (Set.range G))
    (hbF : Bornology.IsBounded (Set.range F)) :
    let ρ : ℝ := 2624989 / 10000000
    let Cκ : ℝ := Real.exp Real.eulerMascheroniConstant * κ + 1
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W : ℝ → ℕ := fun x =>
      presievingModulus 𝓗 x
    let R : ℝ → ℝ := fun x => x ^ ρ
    let B : ℝ → ℝ := fun x =>
      fragmentNormalization (W x) (R x)
    let M_R : ℝ → ℝ := fun x =>
      harmonicFragmentMass (W x) (R x) κ
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) κ, p
    let T39 := fun x => (Fintype.piFinset (fun _ : Fin 38 => (q x).divisors)).filter
      (fun r => Squarefree (∏ j, r j))
    let T40 := fun x => (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
      (fun r => Squarefree (∏ j, r j))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    let w : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T39 x, Finsupp.single r (G (fun j => X x (r j)) / B x ^ 38)
    let y : ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T40 x, Finsupp.single r (F (fun j => X x (r j)) / B x ^ 39)
    let e : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
      (y x).sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
        (yr / ((r i).totient : ℝ)))
    let z : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x => w x + e x
    let D : ℝ → Finset (Fin 38 → ℕ) := fun x =>
      (z x).support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors))
    ∃ M : ℝ, 0 < M ∧
      (∀ᶠ x : ℝ in Filter.atTop,
        1 < x ∧ 0 < B x ∧
        ∀ d : Fin 38 → ℕ,
          let D₀ : ℕ := ∏ j, d j
          |selbergCoefficient (z x) d| ≤
              M * (M_R x / B x) ^ 38 * ((D₀ : ℝ) / (D₀.totient : ℝ)) ∧
            |selbergCoefficient (z x) d| ≤
              M * Cκ ^ 38 * ((D₀ : ℝ) / (D₀.totient : ℝ))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ᶠ x : ℝ in Filter.atTop,
          ∀ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            |∑ d ∈ D x, if ∀ j, d j ∣ n + h (i.succAbove j) then
                selbergCoefficient (z x) d else 0| ≤ A * x ^ ε := by
  intro ρ Cκ h W R B M_R q T39 T40 X w y e z D
  obtain ⟨M, hM, hamp⟩ :=
    canonical_and_erased_diagonal_amplitude (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ hκ a G F hbG hbF
  have hnorm := harmonic_fragment_normalizer_tendsto
    𝓗 ρ κ (by norm_num [ρ]) hκ
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      1 < x ∧ 0 < B x ∧
      ∀ d : Fin 38 → ℕ,
        let D₀ : ℕ := ∏ j, d j
        |selbergCoefficient (z x) d| ≤
            M * (M_R x / B x) ^ 38 * ((D₀ : ℝ) / (D₀.totient : ℝ)) ∧
          |selbergCoefficient (z x) d| ≤
            M * Cκ ^ 38 * ((D₀ : ℝ) / (D₀.totient : ℝ)) := by
    filter_upwards [hamp, hnorm.eventually_le_const (lt_add_one _)] with x hx hm
    obtain ⟨hx, hB, _, _, _, _, _, _, hzsupport, hzbound⟩ := hx
    change 0 < B x at hB
    change (∀ r ∈ (z x).support,
      Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ (q x).divisors) at hzsupport
    change (∀ r, |(z x) r| ≤ M / B x ^ 38) at hzbound
    have hq : Squarefree (q x) := by
      apply (squarefree_primorial ⌊R x ^ κ⌋₊).squarefree_of_dvd
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    have hmass_eq : M_R x = ∑ r ∈ (q x).divisors, (r.totient : ℝ)⁻¹ := rfl
    have hmass : 0 ≤ M_R x := by
      rw [hmass_eq]
      exact Finset.sum_nonneg fun r _ => inv_nonneg.mpr (Nat.cast_nonneg _)
    change M_R x / B x ≤ Cκ at hm
    refine ⟨hx, hB, ?_⟩
    intro d D₀
    have hfinite : |selbergCoefficient (z x) d| ≤
        (M / B x ^ 38) * ((D₀ : ℝ) / (D₀.totient : ℝ)) * M_R x ^ 38 := by
      rw [hmass_eq]
      dsimp only [D₀]
      simpa only [Fintype.card_fin] using
        selbergCoefficient_abs_le_totient_ratio (q x) hq (z x) (M / B x ^ 38)
          (div_nonneg hM.le (pow_nonneg hB.le 38))
          (fun r hr => ⟨(hzsupport r hr).1, fun j =>
            Nat.dvd_of_mem_divisors ((hzsupport r hr).2 j)⟩) hzbound d
    have hratio : |selbergCoefficient (z x) d| ≤
        M * (M_R x / B x) ^ 38 * ((D₀ : ℝ) / (D₀.totient : ℝ)) :=
      hfinite.trans_eq (by
        rw [div_pow]
        simp only [div_eq_mul_inv]
        ac_rfl)
    refine ⟨hratio, hratio.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hmass hB.le) hm 38) hM.le)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine ⟨M, hM, hbound, ?_⟩
  intro ε hε
  obtain ⟨A, hA, hroot⟩ := selberg_divisor_root_uniform_subpower
    (fun j : Fin 38 => h (i.succAbove j)) (M * Cκ ^ 38) ε
    (by dsimp [Cκ]; positivity) hε
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound, hroot] with x hb hr
  intro n hn
  have hcoeff : ∀ d ∈ D x,
      |selbergCoefficient (z x) d| ≤
        M * Cκ ^ 38 * ((∏ j, d j : ℕ) : ℝ) / ((∏ j, d j : ℕ).totient : ℝ) := by
    intro d _
    simpa only [mul_div_assoc] using (hb.2.2 d).2
  have hvalue := hr (z x) (D x) n hn hcoeff
  refine le_trans ?_ hvalue
  apply le_of_eq
  apply congrArg abs
  apply Finset.sum_congr rfl
  intro d _
  exact @ite_cond_congr ℝ _ _ _ Fintype.decidableForallFintype _ _ rfl

end

section
open scoped ContDiff

end

open Asymptotics Topology Real Finset _root_.Filter Asymptotics.Filter

theorem selberg39_marked_count_error_small
    {𝓗 : Finset ℕ}
    (r σ M N : ℝ) (J : ℕ) (hmargin : σ + 2 * r < 1) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        let ρ : ℝ := 2624989 / 10000000
        let W := presievingModulus 𝓗 x
        let Bx := fragmentNormalization W x
        let B := fragmentNormalization W (x ^ ρ)
        1 < x ∧ 0 < Bx ∧ 0 < B ∧
          x ^ σ * ((2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
            x ^ (2 * r) * (Real.log x) ^ (2 * J)) ≤
              ε * (x / (W : ℝ) / Bx / B ^ 38) := by
  intro ε hε
  let ρ₀ : ℝ := 2624989 / 10000000
  let a : ℝ := r + σ / 2
  have hρ : 0 < ρ₀ := by norm_num [ρ₀]
  have hδ : 0 < 1 - 2 * a := by dsimp only [a]; linarith
  have hlogLimit : Tendsto
      (fun x : ℝ => Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a))
      atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((2 * J + 1 : ℕ) : ℝ) hδ).tendsto_div_nhds_zero
  have hlimit : Tendsto
      (fun x : ℝ => 2 * (M * N) ^ 2 * Real.log x ^ (2 * J + 1) /
        x ^ (1 - 2 * a)) atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using hlogLimit.const_mul (2 * (M * N) ^ 2)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    presieving_le_mul_log_eventually 𝓗 1 zero_lt_one,
    presieving_le_mul_log_eventually 𝓗 ρ₀ hρ,
    hlimit.eventually_le_const hε] with x hx hWlog hWρ hsmall
  intro ρ W Bx B
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hW : 0 < W := presieving_pos 𝓗 x
  have hWR : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hφ : (1 : ℝ) ≤ (Nat.totient W : ℝ) :=
    Nat.one_le_cast.mpr (Nat.totient_pos.mpr hW)
  have hWlog' : (W : ℝ) ≤ Real.log x := by simpa only [one_mul] using hWlog
  have hBx1 : 1 ≤ Bx := by
    change 1 ≤ ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log x
    rw [div_mul_eq_mul_div]
    exact (one_le_div hWR).mpr
      (hWlog'.trans (le_mul_of_one_le_left hlog hφ))
  have hB1 : 1 ≤ B := by
    change 1 ≤ ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log (x ^ ρ₀)
    rw [Real.log_rpow hx0, div_mul_eq_mul_div]
    exact (one_le_div hWR).mpr
      (hWρ.trans (le_mul_of_one_le_left (mul_nonneg hρ.le hlog) hφ))
  have hBx : 0 < Bx := zero_lt_one.trans_le hBx1
  have hB : 0 < B := zero_lt_one.trans_le hB1
  refine ⟨hx, hBx, hB, ?_⟩
  let A : ℝ := x / (W : ℝ) / Bx / B ^ 38
  let raw : ℝ := (2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
    x ^ (2 * r) * (Real.log x) ^ (2 * J)
  have hA : 0 < A := div_pos (div_pos (div_pos hx0 hWR) hBx) (pow_pos hB 38)
  have hpow : x ^ σ * x ^ (2 * r) = (x ^ a) ^ 2 := by
    calc
      _ = x ^ (σ + 2 * r) := (Real.rpow_add hx0 _ _).symm
      _ = x ^ (a * 2) := by congr 1; dsimp only [a]; ring
      _ = _ := Real.rpow_mul_natCast hx0.le a 2
  have hlogpow : Real.log x ^ (2 * J) = (Real.log x ^ J) ^ 2 :=
    pow_mul' (Real.log x) 2 J
  have hden : 1 ≤ Bx * B ^ 38 :=
    one_le_mul_of_one_le_of_one_le hBx1 (one_le_pow₀ hB1)
  have hWscaled : (W : ℝ) / (Bx * B ^ 38) ≤ Real.log x :=
    (div_le_self (Nat.cast_nonneg W) hden).trans hWlog'
  have hrawNorm : x ^ σ * raw / A ≤
      2 * (M * N) ^ 2 * Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a) := by
    calc
      x ^ σ * raw / A =
          (2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
            (x ^ σ * x ^ (2 * r)) * Real.log x ^ (2 * J) / A := by
        dsimp only [raw]
        ring
      _ = (2 * (M * N) ^ 2 * (x ^ a) ^ 2 * (Real.log x ^ J) ^ 2 / x) *
          ((W : ℝ) / (Bx * B ^ 38)) := by
        rw [hpow, hlogpow]
        dsimp only [A]
        field_simp [hBx.ne', hB.ne', hx0.ne', hWR.ne']
      _ ≤ (2 * (M * N) ^ 2 * (x ^ a) ^ 2 * (Real.log x ^ J) ^ 2 / x) *
          Real.log x :=
        mul_le_mul_of_nonneg_left hWscaled (by positivity)
      _ = 2 * (M * N) ^ 2 * Real.log x * (x ^ a) ^ 2 *
          (Real.log x ^ J) ^ 2 / x := by ring
      _ = _ := crt_power_identity (M * N) x a J hx0
  exact (div_le_iff₀ hA).mp (hrawNorm.trans hsmall)

open Classical in
theorem selberg39_auxiliary_marked_bin_uniform
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ r_c ζ_a M N ξ a l s : ℝ)
    (hκ : 0 < κ) (hζ_a : 0 < ζ_a) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hξ : 0 < ξ) (hξa : ξ ≤ a) (hs : 0 ≤ s)
    (hcap : ((2624989 : ℝ) / 10000000) * κ < ξ)
    (hmargin : s + 2 * (r_c + ζ_a) < 1) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop,
        let ρ : ℝ := 2624989 / 10000000
        let h : Fin 39 → ℕ :=
          𝓗.orderEmbOfFin h𝓗_card
        let W := presievingModulus 𝓗 x
        let R := x ^ ρ
        let Bx := fragmentNormalization W x
        let B := fragmentNormalization W R
        let P := fragmentPrimes W R κ
        let q : ℕ := ∏ p ∈ P, p
        let T := markedPrimePairBin x ξ a l s
        let pairMass : ℝ := ∑ v ∈ T, 1 / ((v.1 * v.2 : ℕ) : ℝ)
        1 < x ∧ 0 < Bx ∧ 0 < B ∧
          ∀ (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ),
            (∀ t ∈ u.support,
              t 0 ∈ q.divisors ∧ (t 0 : ℝ) ≤ x ^ ζ_a) →
            (∀ r ∈ z.support,
              Squarefree (∏ j, r j) ∧ (∀ j, r j ∈ q.divisors) ∧
                ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r_c) →
            (∀ t, |u t| ≤ N / Bx) →
            (∀ r, |z r| ≤ M / B ^ 38) →
            let Du := u.support.biUnion
              (fun t => Fintype.piFinset (fun j => (t j).divisors))
            let Dz := z.support.biUnion
              (fun r => Fintype.piFinset (fun j => (r j).divisors))
            let L : ℕ → ℝ := fun t =>
              ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
            let C : ℕ → ℝ := fun n =>
              ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
                selbergCoefficient z d else 0
            let harmonic : ℝ :=
              u.sum (fun t ut => ut ^ 2 / ((t 0).totient : ℝ)) *
                z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))
            ∀ b : ℕ,
              |(∑ v ∈ T, ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                  if Nat.ModEq W n b ∧ v.1 * v.2 ∣ n + h i then
                    (L (n + h i) * C n) ^ 2 else 0) -
                pairMass * (x / (W : ℝ) * harmonic)| ≤
                  ε * (x / (W : ℝ) / Bx / B ^ 38) := by
  intro ε hε
  obtain ⟨K, hK, hmass⟩ := markedPrimePairBin_reciprocal_eventually_bounded ξ a hξ hξa
  let η : ℝ := ε / (2 * K + 1)
  have hden : 0 < 2 * K + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  have hradius : 2 * (r_c + ζ_a) < 1 := by linarith
  let J : ℕ := 7 + (2 ^ (38 + 2) - 1)
  have hlogcap : ∀ᶠ x : ℝ in atTop,
      0 ≤ r_c → 1 + Real.log (⌊x ^ (r_c + ζ_a)⌋₊ : ℝ) ≤ Real.log x := by
    by_cases hrc : 0 ≤ r_c
    · have ha0 : 0 < r_c + ζ_a := add_pos_of_nonneg_of_pos hrc hζ_a
      have ha1 : r_c + ζ_a < 1 := by linarith
      exact (floor_rpow_log_envelope (r_c + ζ_a) ha0 ha1).mono
        fun _ hx _ => hx.2.2
    · exact Filter.Eventually.of_forall fun _ hc => (hrc hc).elim
  filter_upwards [hmass, hlogcap,
    markedPrimePairBin_coprime_eventually 𝓗
      ((2624989 : ℝ) / 10000000) κ ξ a l s hξ hcap,
    selberg39_marked_count_error_small (𝓗 := 𝓗) (r_c + ζ_a) s M N J hmargin η hη,
    selberg39_auxiliary_uniform_real_harmonic (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ r_c ζ_a M N
      hκ hζ_a hradius hM hN η hη] with x hmassx hlog hcop hsmallx hphysical
  intro ρ h W R Bx B P q T pairMass
  rcases hsmallx with ⟨hx, hBx, hB, hsmall⟩
  have hx0 : 0 < x := zero_lt_one.trans hx
  refine ⟨hx, hBx, hB, ?_⟩
  intro u z hu hz huBound hzBound Du Dz L C harmonic b
  let A : ℝ := x / (W : ℝ) / Bx / B ^ 38
  let E : ℝ := (2 * M ^ 2 * N ^ 2 / (Bx ^ 2 * B ^ 76)) *
    x ^ (2 * (r_c + ζ_a)) * Real.log x ^ (2 * J)
  let mean : ℝ := (1 / (q : ℝ)) *
    ∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2
  let S₀ : ℝ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if Nat.ModEq W n b then (L (n + h i) * C n) ^ 2 else 0
  let S : (ℕ × ℕ) → ℝ := fun v =>
    ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq W n b ∧ v.1 * v.2 ∣ n + h i then
        (L (n + h i) * C n) ^ 2 else 0
  have hE : 0 ≤ E := by
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
    dsimp only [E]
    positivity
  have hcountSmall : x ^ s * E ≤ η * A := hsmall
  have hEsmall : E ≤ η * A :=
    (le_mul_of_one_le_left hE (Real.one_le_rpow hx.le hs)).trans hcountSmall
  have hmass0 : 0 ≤ pairMass := (hmassx l s).1
  have hmassK : pairMass ≤ K := (hmassx l s).2
  have huMem : ∀ t ∈ u.support, t 0 ∈ q.divisors := fun t ht => (hu t ht).1
  have hzMem : ∀ r ∈ z.support,
      Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors :=
    fun r hr => ⟨(hz r hr).1, (hz r hr).2.1⟩
  have hl1 : 2 * (∑ e ∈ Du, |selbergCoefficient u e|) ^ 2 *
      (∑ d ∈ Dz, |selbergCoefficient z d|) ^ 2 ≤ E := by
    by_cases hrc : 0 ≤ r_c
    · have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
        Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
      have hqsf : Squarefree q := squarefree_prime_prod P hP
      exact auxiliary_two_radius_l1_bound u z q x r_c ζ_a M N Bx B
        hx hrc hζ_a.le hM hN hBx hB hqsf hu
        (fun r hr => ⟨(hz r hr).1, (hz r hr).2.2⟩) huBound hzBound (hlog hrc)
    · have hz0 : z = 0 := by
        ext r
        by_contra hzr
        have hr : r ∈ z.support := Finsupp.mem_support_iff.mpr hzr
        have hp : (1 : ℝ) ≤ ((∏ j, r j : ℕ) : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero (hz r hr).1.ne_zero)
        have hlt : x ^ r_c < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg hx (lt_of_not_ge hrc)
        exact (not_lt_of_ge hp) ((hz r hr).2.2.trans_lt hlt)
      have hDz : Dz = ∅ := by
        simp only [Dz, hz0, Finsupp.support_zero, Finset.biUnion_empty]
      simpa only [hDz, Finset.sum_empty, zero_pow (by decide : (2 : ℕ) ≠ 0),
        mul_zero] using hE
  have hmarked (v : ℕ × ℕ) (hv : v ∈ T) :
      |S v - (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean)| ≤ E := by
    have hbox := (Finset.mem_filter.mp hv).1
    have hp : Nat.Prime v.1 :=
      Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).1
    have hq : Nat.Prime v.2 :=
      Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).2
    have hmpos : 0 < v.1 * v.2 := Nat.mul_pos hp.pos hq.pos
    have hc := hcop.2 v hv
    have huM : ∀ t ∈ u.support, Nat.Coprime (t 0) (v.1 * v.2) :=
      fun t ht => hc.2.symm.of_dvd_left (Nat.mem_divisors.mp (hu t ht).1).1
    have hzM : ∀ r ∈ z.support, Nat.Coprime (∏ j, r j) (v.1 * v.2) := by
      intro r hr
      exact Nat.Coprime.prod_left fun j _ =>
        hc.2.symm.of_dvd_left (Nat.mem_divisors.mp ((hz r hr).2.1 j)).1
    have hcrt := selberg39_auxiliary_marked_real_interval_crt
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ
      u z huMem hzMem (v.1 * v.2) hmpos hc.1.symm huM hzM b
    have hmain : x / ((W : ℝ) * ((v.1 * v.2 : ℕ) : ℝ)) * mean =
        (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    change |S v - x / ((W : ℝ) * ((v.1 * v.2 : ℕ) : ℝ)) * mean| ≤ _ at hcrt
    rw [hmain] at hcrt
    exact hcrt.trans hl1
  have hbin : |(∑ v ∈ T, S v) - pairMass * (x / (W : ℝ) * mean)| ≤ η * A := by
    calc
      _ = |∑ v ∈ T,
          (S v - (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean))| := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ ≤ ∑ v ∈ T,
          |S v - (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ T, E := Finset.sum_le_sum hmarked
      _ = (T.card : ℝ) * E := by simp
      _ ≤ x ^ s * E :=
        mul_le_mul_of_nonneg_right (markedPrimePairBin_card_le x ξ a l s hx) hE
      _ ≤ η * A := hcountSmall
  have hordinary := hphysical.2.2 u z hu hz huBound hzBound b
  have hordinary' : |S₀ - x / (W : ℝ) * mean| ≤ E ∧
      |S₀ - x / (W : ℝ) * harmonic| ≤ η * A := hordinary
  have hmean : |x / (W : ℝ) * mean - x / (W : ℝ) * harmonic| ≤ 2 * η * A := by
    calc
      _ ≤ |x / (W : ℝ) * mean - S₀| + |S₀ - x / (W : ℝ) * harmonic| :=
        abs_sub_le _ _ _
      _ ≤ E + η * A := add_le_add (by
        simpa only [abs_sub_comm] using hordinary'.1) hordinary'.2
      _ ≤ η * A + η * A := add_le_add hEsmall le_rfl
      _ = 2 * η * A := by ring
  have hweighted :
      |pairMass * (x / (W : ℝ) * mean) - pairMass * (x / (W : ℝ) * harmonic)| ≤
        K * (2 * η * A) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hmass0]
    exact mul_le_mul hmassK hmean (abs_nonneg _) hK.le
  change |(∑ v ∈ T, S v) - pairMass * (x / (W : ℝ) * harmonic)| ≤ ε * A
  calc
    _ ≤ |(∑ v ∈ T, S v) - pairMass * (x / (W : ℝ) * mean)| +
        |pairMass * (x / (W : ℝ) * mean) - pairMass * (x / (W : ℝ) * harmonic)| :=
      abs_sub_le _ _ _
    _ ≤ η * A + K * (2 * η * A) := add_le_add hbin hweighted
    _ = ε * A := by
      dsimp only [η]
      field_simp [hden.ne']
      ring

end PrimeGap182.Selberg

section
open Set

namespace PrimeGap182.Selberg

theorem sharp_scalar_cutoff_eq (W : ℕ) (x κ : ℝ) (hx : 1 < x) (hκ : 0 < κ) :
    (((harmonicConfigurationMass W x κ).map
      (fragmentBandMasses (![0, κ] : Fin 2 → ℝ))).map
        (fun v : Fin 1 → ℝ => v 0) : Measure ℝ).real (Set.Iic κ) =
      ∑ a ∈ Finset.Icc 1 ⌊x ^ κ⌋₊,
        if Squarefree a ∧ a.Coprime W then 1 / (a.totient : ℝ) else 0 := by
  classical
  have hcap : 1 ≤ x ^ κ := Real.one_le_rpow hx.le hκ.le
  let D := (∏ p ∈ fragmentPrimes W x κ, p).divisors
  let b := fragmentBandMasses (![0, κ] : Fin 2 → ℝ)
  have hb : Measurable b := measurable_fragmentBandMasses _
  have hset : D.filter (fun s : ℕ => Real.log s / Real.log x ≤ κ) =
      (Finset.Icc 1 ⌊x ^ κ⌋₊).filter (fun s => Squarefree s ∧ s.Coprime W) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hs, hlog⟩
      have hd := (mem_fragment_divisors_iff W x κ hcap s).mp hs
      have hs0 : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
      have hle : (s : ℝ) ≤ x ^ κ :=
        (Real.le_rpow_iff_log_le hs0 (zero_lt_one.trans hx)).mpr
          ((div_le_iff₀ (Real.log_pos hx)).mp hlog)
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd.1.ne_zero,
        (Nat.le_floor_iff (zero_le_one.trans hcap)).mpr hle⟩, hd.1, hd.2.1⟩
    · rintro ⟨⟨hs1, hsle⟩, hsq, hcop⟩
      have hle : (s : ℝ) ≤ x ^ κ :=
        (Nat.le_floor_iff (zero_le_one.trans hcap)).mp hsle
      have hs0 : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hsq.ne_zero
      refine ⟨(mem_fragment_divisors_iff W x κ hcap s).mpr ⟨hsq, hcop, ?_⟩, ?_⟩
      · have hmax : max 1 (s.primeFactors.sup id) ≤ s :=
          max_le hs1 (Finset.sup_le fun _ hp => Nat.le_of_mem_primeFactors hp)
        exact (Nat.cast_le.mpr hmax).trans hle
      · rw [div_le_iff₀ (Real.log_pos hx)]
        exact (Real.le_rpow_iff_log_le hs0 (zero_lt_one.trans hx)).mp hle
  have heval (T : Set (FiniteMeasure ℝ)) (hT : MeasurableSet T) :
      (harmonicConfigurationMass W x κ : Measure (FiniteMeasure ℝ)).real T =
        ∑ s ∈ D, if primeLogConfiguration x s ∈ T then (s.totient : ℝ)⁻¹ else 0 := by
    unfold harmonicConfigurationMass
    rw [FiniteMeasure.toMeasure_sum, Measure.real, Measure.finsetSum_apply,
      ENNReal.toReal_sum (by intros; finiteness)]
    apply Finset.sum_congr rfl
    intro s _
    change ((((s.totient : ℝ)⁻¹).toNNReal : ℝ≥0∞) *
      Measure.dirac (primeLogConfiguration x s) T).toReal = _
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
      Real.coe_toNNReal _ (by positivity : 0 ≤ (s.totient : ℝ)⁻¹),
      Measure.dirac_apply' _ hT]
    by_cases hs : primeLogConfiguration x s ∈ T <;> simp [hs]
  change (((harmonicConfigurationMass W x κ).map b).map
    (fun v : Fin 1 → ℝ => v 0) : Measure ℝ).real (Set.Iic κ) = _
  rw [FiniteMeasure.toMeasure_map,
    map_measureReal_apply (measurable_pi_apply 0) measurableSet_Iic,
    FiniteMeasure.toMeasure_map,
    map_measureReal_apply hb ((measurable_pi_apply 0) measurableSet_Iic),
    heval _ (hb ((measurable_pi_apply 0) measurableSet_Iic))]
  calc
    _ = ∑ s ∈ D, if Real.log s / Real.log x ≤ κ then (s.totient : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      have hm := fragment_divisor_configuration_mass W x κ hx hκ s hs
      simp only [Set.mem_preimage, Set.mem_Iic, b, fragmentBandMasses,
        Fin.castSucc_zero, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, hm]
    _ = _ := by
      rw [← Finset.sum_filter, hset, Finset.sum_filter]
      simp only [one_div]

theorem sharp_scalar_measure_tendsto (H : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun x : ℝ =>
      (((((fragmentNormalization (presievingModulus H x) x)⁻¹).toNNReal •
        (harmonicConfigurationMass (presievingModulus H x) x κ).map
          (fragmentBandMasses (![0, κ] : Fin 2 → ℝ))).map
            (fun v : Fin 1 → ℝ => v 0) : FiniteMeasure ℝ) : Measure ℝ).real (Iic κ))
      atTop (𝓝 κ) := by
  let a : Fin 2 → ℝ := ![0, κ]
  have ha : StrictMono a := by simpa [Fin.strictMono_iff_lt_succ, a] using hκ
  have hm : Measurable (fragmentBandMasses a) := measurable_fragmentBandMasses a
  let P : ProbabilityMeasure (FiniteMeasure ℝ) :=
    ⟨fragmentLaw κ, fragmentLaw_isProbabilityMeasure κ⟩
  let ν := ((Real.exp Real.eulerMascheroniConstant * κ).toNNReal •
    P.toFiniteMeasure.map (fragmentBandMasses a)).map (fun v : Fin 1 → ℝ => v 0)
  let μ (x : ℝ) :=
    (((fragmentNormalization (presievingModulus H x) x)⁻¹).toNNReal •
      (harmonicConfigurationMass (presievingModulus H x) x κ).map
        (fragmentBandMasses a)).map (fun v : Fin 1 → ℝ => v 0)
  have hw : Tendsto μ atTop (𝓝 ν) := by
    apply FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ _ (continuous_apply 0)
    simpa only [Real.rpow_one] using
      (harmonic_fragment_band_vector_tendsto H 1 κ a zero_lt_one hκ ha rfl rfl).snd_nhds
  have hν : (ν : Measure ℝ) =
      (volume.restrict (Ici (0 : ℝ))).withDensity
        (fun t => ENNReal.ofReal (dickmanRho (t / κ))) := by
    dsimp only [ν]
    rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_smul,
      FiniteMeasure.toMeasure_map,
      Measure.map_smul _ (f := fun v : Fin 1 → ℝ => v 0)
        (measurable_pi_apply 0).aemeasurable,
      Measure.map_map (by fun_prop) hm]
    change ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
      Measure.map (fun c : FiniteMeasure ℝ => ((c.restrict (Ioc (0 : ℝ) κ)).mass : ℝ))
        (fragmentLaw κ) = _
    rw [Measure.map_congr (by
      filter_upwards [ae_restrict_Ioc_fragmentLaw κ] with c hc
      rw [hc])]
    exact normalized_fragmentLaw_mass_eq_dickman κ hκ
  have hνκ : (ν : Measure ℝ) (Iic κ) = ENNReal.ofReal κ := by
    rw [hν, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    rw [Set.inter_comm, Set.Ici_inter_Iic]
    calc
      (∫⁻ t in Icc (0 : ℝ) κ,
          ENNReal.ofReal (dickmanRho (t / κ))) =
          ∫⁻ _ in Icc (0 : ℝ) κ, (1 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [dickmanRho_analytic.2.1 _
          ⟨div_nonneg ht.1 hκ.le, (div_le_one hκ).2 ht.2⟩]
        simp
      _ = ENNReal.ofReal κ := by simp
  have hn : ν ≠ 0 := by
    intro hn
    have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal κ := by simpa [hn] using hνκ
    exact (ENNReal.ofReal_pos.mpr hκ).ne' h0.symm
  have hb : (ν : Measure ℝ) (frontier (Iic κ)) = 0 := by
    rw [hν, frontier_Iic]
    exact measure_singleton κ
  have hb' : (ν.normalize : Measure ℝ) (frontier (Iic κ)) = 0 := by
    rw [ν.toMeasure_normalize_eq_of_nonzero hn,
      Measure.coe_nnreal_smul_apply, hb, mul_zero]
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (FiniteMeasure.tendsto_normalize_of_tendsto hw hn)
    ((ProbabilityMeasure.null_iff_toMeasure_null _ _).2 hb')
  have ht' : Tendsto (fun x => μ x (Iic κ)) atTop (𝓝 (ν (Iic κ))) := by
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using hw.mass.mul hp
  have ht : Tendsto (fun x => (μ x : Measure ℝ).real (Iic κ)) atTop
      (𝓝 ((ν : Measure ℝ).real (Iic κ))) :=
    (NNReal.continuous_coe.tendsto (ν (Iic κ))).comp ht'
  have hr : (ν : Measure ℝ).real (Iic κ) = κ := by
    rw [measureReal_def, hνκ, ENNReal.toReal_ofReal hκ.le]
  simpa only [μ, a, hr] using ht

end PrimeGap182.Selberg

theorem PrimeGap182.Selberg.sharp_harmonic_normalizer_tendsto
    (H : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    Filter.Tendsto
      (fun x : ℝ =>
        (∑ a ∈ Finset.Icc 1 ⌊x ^ κ⌋₊,
          if Squarefree a ∧ a.Coprime (PrimeGap186.presievingModulus H x) then
            1 / (a.totient : ℝ) else 0) /
          PrimeGap186.fragmentNormalization (PrimeGap186.presievingModulus H x) x)
      Filter.atTop (𝓝 κ) := by
  classical
  have ht := PrimeGap182.Selberg.sharp_scalar_measure_tendsto H κ hκ
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [FiniteMeasure.map_smul _ (f := fun v : Fin 1 → ℝ => v 0)
      (measurable_pi_apply 0).aemeasurable,
    FiniteMeasure.toMeasure_smul,
    measureReal_nnreal_smul_apply, PrimeGap182.Selberg.sharp_scalar_cutoff_eq _ x κ hx hκ]
  have hB : 0 ≤ PrimeGap186.fragmentNormalization (PrimeGap186.presievingModulus H x) x :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.log_nonneg hx.le)
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hB)]
  exact (div_eq_inv_mul _ _).symm

end

namespace PrimeGap182.Selberg

open Classical in
/-- The exact finite identities for the sharp array in Lemma 3.9 of the main paper.
The summation set is the squarefree, coprime integers at most `Z`, not all divisors
of a primorial. The cutoff is assumed nonempty by `1 ≤ Z`. -/
theorem sharp_cutoff_selberg (W : ℕ) (Z : ℝ) (hZ : 1 ≤ Z) :
    let A := (Finset.Icc 1 ⌊Z⌋₊).filter fun a => Squarefree a ∧ Nat.Coprime a W
    let G : ℝ := ∑ a ∈ A, 1 / (a.totient : ℝ)
    let y : (Fin 1 → ℕ) →₀ ℝ :=
      ∑ a ∈ A, Finsupp.single (fun _ : Fin 1 => a) (1 / G)
    let lam : ℕ → ℝ := fun d => selbergCoefficient y (fun _ : Fin 1 => d)
    0 < G ∧ lam 1 = 1 ∧
      (∀ d, lam d = (ArithmeticFunction.moebius d : ℝ) * d / G *
        ∑ a ∈ A, if d ∣ a then 1 / (a.totient : ℝ) else 0) ∧
      (∀ d, d ∉ A → lam d = 0) ∧
      (∀ a, (ArithmeticFunction.moebius a : ℝ) * (a.totient : ℝ) *
        (∑ d ∈ A, if a ∣ d then lam d / (d : ℝ) else 0) =
          if a ∈ A then 1 / G else 0) ∧
      (∑ d ∈ A, ∑ e ∈ A, lam d * lam e / (Nat.lcm d e : ℝ)) = 1 / G ∧
      y.sum (fun r yr => yr ^ 2 / ((r 0).totient : ℝ)) = 1 / G ∧
      y.support = A.image (fun a => fun _ : Fin 1 => a) ∧
      y.support.biUnion (fun r => Fintype.piFinset fun i => (r i).divisors) =
        A.image (fun a => fun _ : Fin 1 => a) ∧
      (∀ r, y r = (if r 0 ∈ A then 1 / G else 0) ∧ |y r| ≤ 1 / G) ∧
      (∀ t : ℕ, 0 < t →
        (∀ p : ℕ, p.Prime → p ∣ t → Z < (p : ℝ)) →
          (∑ d ∈ t.divisors, lam d) = 1) := by
  let : DecidableEq (Fin 1) := fun a b => Classical.propDecidable (a = b)
  intro A G y lam
  let c (a : ℕ) : Fin 1 → ℕ := fun _ => a
  have hc : Function.Injective c := fun _ _ h => congrFun h 0
  have hcr (r : Fin 1 → ℕ) : c (r 0) = r := by
    funext i
    exact congrArg r (Subsingleton.elim 0 i)
  have hA1 : 1 ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_Icc, le_refl, true_and,
      squarefree_one, Nat.coprime_one_left_iff, and_true]
    exact (Nat.one_le_floor_iff Z).mpr hZ
  have hG : 0 < G := by
    apply Finset.sum_pos' (fun a _ => by positivity)
    exact ⟨1, hA1, by norm_num⟩
  have hdown {a d : ℕ} (ha : a ∈ A) (hda : d ∣ a) : d ∈ A := by
    obtain ⟨haI, hsf, hcop⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      hsf.squarefree_of_dvd hda, hcop.coprime_dvd_left hda⟩
    · exact Nat.one_le_iff_ne_zero.mpr (ne_zero_of_dvd_ne_zero hsf.ne_zero hda)
    · exact (Nat.le_of_dvd hsf.ne_zero.bot_lt hda).trans (Finset.mem_Icc.mp haI).2
  have hyapply (r : Fin 1 → ℕ) :
      y r = if r 0 ∈ A then 1 / G else 0 := by
    have heq (a : ℕ) : (fun _ : Fin 1 => a) = r ↔ a = r 0 := by
      change c a = r ↔ a = r 0
      rw [← hcr r]
      exact hc.eq_iff
    simp only [y, Finsupp.finsetSum_apply, Finsupp.single_apply, heq, Finset.sum_ite_eq']
  have hsupp : y.support = A.image c := by
    ext r
    rw [Finsupp.mem_support_iff, hyapply]
    constructor
    · intro hr
      have hmem : r 0 ∈ A := by
        by_contra hnot
        simp [hnot] at hr
      exact Finset.mem_image.mpr ⟨r 0, hmem, hcr r⟩
    · intro hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      simp [c, ha, hG.ne']
  have hysf : ∀ r ∈ y.support, Squarefree (∏ i, r i) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hsupp ▸ hr)
    simpa [c] using (Finset.mem_filter.mp ha).2.1
  have hD : y.support.biUnion
      (fun r => Fintype.piFinset fun i => (r i).divisors) = A.image c := by
    ext d
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨r, hr, hdr⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hsupp ▸ hr)
      exact Finset.mem_image.mpr ⟨d 0,
        hdown ha (Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr 0)), hcr d⟩
    · intro hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      refine ⟨c a, hsupp.symm ▸ Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        Fintype.mem_piFinset.mpr ?_⟩
      intro i
      exact Nat.mem_divisors.mpr ⟨dvd_rfl, (Finset.mem_filter.mp ha).2.1.ne_zero⟩
  have hlam (d : ℕ) : lam d = (ArithmeticFunction.moebius d : ℝ) * d / G *
      ∑ a ∈ A, if d ∣ a then 1 / (a.totient : ℝ) else 0 := by
    dsimp only [lam]
    simp only [selbergCoefficient, Fin.prod_univ_one, Finsupp.sum]
    rw [hsupp, Finset.sum_image hc.injOn, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hyapply]
    simp only [c, ha, ite_true, forall_const]
    split_ifs <;> ring
  have hlam1 : lam 1 = 1 := by
    rw [hlam]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one,
      one_mul, one_dvd, ite_true]
    change 1 / G * G = 1
    field_simp [hG.ne']
  have hdiag : y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ))) =
      1 / G := by
    calc
      _ = ∑ a ∈ A, (1 / G) ^ 2 / (a.totient : ℝ) := by
        rw [Finsupp.sum, hsupp, Finset.sum_image hc.injOn]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hyapply]
        simp [c, ha]
      _ = (1 / G) ^ 2 * G := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 1 / G := by field_simp [hG.ne']
  have hvanish (d : ℕ) (hd : d ∉ A) : lam d = 0 := by
    rw [hlam]
    have hz : (∑ a ∈ A, if d ∣ a then 1 / (a.totient : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact ite_eq_right (fun hda => hd (hdown ha hda))
    rw [hz, mul_zero]
  refine ⟨hG, hlam1, hlam, hvanish, ?_, ?_, ?_, hsupp, ?_, ?_, ?_⟩
  · intro a
    have h := selberg_forward_inverse y hysf (c a)
    dsimp only at h
    rw [hD, Finset.sum_image hc.injOn, hyapply] at h
    simpa only [Fin.prod_univ_one, c, forall_const] using h
  · have h := selberg_unrestricted_lcm_diagonal y hysf
    dsimp only at h
    rw [hD, Finset.sum_image hc.injOn] at h
    simp_rw [Finset.sum_image hc.injOn] at h
    simpa only [Fin.prod_univ_one, c] using h.trans hdiag
  · simpa only [Fin.prod_univ_one] using hdiag
  · convert hD using 1
    ext r
    simp only [Finset.mem_biUnion, Fintype.mem_piFinset]
  · intro r
    refine ⟨hyapply r, ?_⟩
    rw [hyapply]
    split_ifs
    · exact le_of_eq (abs_of_pos (one_div_pos.mpr hG))
    · simpa only [abs_zero] using (one_div_pos.mpr hG).le
  · intro t ht hrough
    rw [Finset.sum_eq_single 1]
    · exact hlam1
    · intro d hd hd1
      apply hvanish d
      intro ha
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      have hsf := (Finset.mem_filter.mp ha).2.1
      have hdZ : (d : ℝ) ≤ Z :=
        (Nat.le_floor_iff (zero_le_one.trans hZ)).mp
          (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
      have hpZ : (p : ℝ) ≤ Z :=
        (Nat.cast_le.mpr (Nat.le_of_dvd hsf.ne_zero.bot_lt hpd)).trans hdZ
      exact (not_lt_of_ge hpZ)
        (hrough p hp (hpd.trans (Nat.dvd_of_mem_divisors hd)))
    · intro hnot
      exact False.elim (hnot (Nat.one_mem_divisors.mpr ht.ne'))

open Classical in
/-- The sharp Selberg family used by the marked-bin bound and the exceptional term. -/
theorem sharp_auxiliary_family (H : Finset ℕ) (κ ξ : ℝ)
    (hκ : 0 < κ) (hκξ : κ < ξ) :
    let W : ℝ → ℕ := presievingModulus H
    let Bx : ℝ → ℝ := fun x => fragmentNormalization (W x) x
    let qa : ℝ → ℕ := fun x => ∏ p ∈ fragmentPrimes (W x) x κ, p
    let A : ℝ → Finset ℕ := fun x =>
      (Finset.Icc 1 ⌊x ^ κ⌋₊).filter fun a => Squarefree a ∧ Nat.Coprime a (W x)
    let G : ℝ → ℝ := fun x => ∑ a ∈ A x, 1 / (a.totient : ℝ)
    let u : ℝ → ((Fin 1 → ℕ) →₀ ℝ) := fun x =>
      ∑ a ∈ A x, Finsupp.single (fun _ : Fin 1 => a) (1 / G x)
    let Du : ℝ → Finset (Fin 1 → ℕ) := fun x => (u x).support.biUnion
      (fun r => Fintype.piFinset fun j => (r j).divisors)
    let L : ℝ → ℕ → ℝ := fun x t =>
      ∑ e ∈ Du x, if e 0 ∣ t then selbergCoefficient (u x) e else 0
    Tendsto (fun x => Bx x * (u x).sum (fun r ur => ur ^ 2 / ((r 0).totient : ℝ)))
        atTop (𝓝 (1 / κ)) ∧
      (∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ x : ℝ in atTop,
        1 < x ∧ 0 < Bx x ∧ (∀ r, |u x r| ≤ N / Bx x) ∧
          ∀ r ∈ (u x).support, r 0 ∈ (qa x).divisors ∧ (r 0 : ℝ) ≤ x ^ κ) ∧
      ∀ᶠ x : ℝ in atTop, ∀ t : ℕ,
        (∀ p : ℕ, p.Prime → p ∣ t → x ^ ξ ≤ (p : ℝ)) → L x t = 1 := by
  intro W Bx qa A G u Du L
  have hnormal : Tendsto (fun x => G x / Bx x) atTop (𝓝 κ) := by
    simpa only [G, A, Bx, W, Finset.sum_filter] using
      sharp_harmonic_normalizer_tendsto H κ hκ
  have hfinite (x : ℝ) (hx : 1 < x) :=
    sharp_cutoff_selberg (W x) (x ^ κ) (Real.one_le_rpow hx.le hκ.le)
  have hlower : ∀ᶠ x : ℝ in atTop, κ / 2 < G x / Bx x :=
    hnormal.eventually (lt_mem_nhds (half_lt_self hκ))
  refine ⟨?_, ?_, ?_⟩
  · have hinv : Tendsto (fun x => Bx x / G x) atTop (𝓝 (1 / κ)) := by
      simpa only [inv_div, one_div] using hnormal.inv₀ hκ.ne'
    apply hinv.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    obtain ⟨_, _, _, _, _, _, hdiag, _, _, _, _⟩ := hfinite x hx
    change (u x).sum (fun r ur => ur ^ 2 / ((r 0).totient : ℝ)) = 1 / G x at hdiag
    rw [hdiag]
    ring
  · refine ⟨2 / κ, div_nonneg (by norm_num) hκ.le, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ), hlower] with x hx hlowerx
    obtain ⟨hG, _, _, _, _, _, _, hsupp, _, harray, _⟩ := hfinite x hx
    change 0 < G x at hG
    have hBx : 0 < Bx x :=
      (div_pos_iff_of_pos_left hG).mp ((half_pos hκ).trans hlowerx)
    have hrecip : 1 / G x ≤ (2 / κ) / Bx x := by
      calc
        _ ≤ 1 / ((κ / 2) * Bx x) :=
          one_div_le_one_div_of_le (mul_pos (half_pos hκ) hBx)
            ((lt_div_iff₀ hBx).mp hlowerx).le
        _ = (2 / κ) / Bx x := by field_simp
    refine ⟨hx, hBx, fun r => ((harray r).2).trans hrecip, ?_⟩
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hsupp ▸ hr)
    obtain ⟨haI, hsf, hcop⟩ := Finset.mem_filter.mp ha
    have hcap : 1 ≤ x ^ κ := Real.one_le_rpow hx.le hκ.le
    have haZ : (a : ℝ) ≤ x ^ κ :=
      (Nat.le_floor_iff (zero_le_one.trans hcap)).mp (Finset.mem_Icc.mp haI).2
    refine ⟨(mem_fragment_divisors_iff (W x) x κ hcap a).mpr ⟨hsf, hcop, ?_⟩, haZ⟩
    have hmax : max 1 (a.primeFactors.sup id) ≤ a :=
      max_le (Finset.mem_Icc.mp haI).1
        (Finset.sup_le fun _ hp => Nat.le_of_mem_primeFactors hp)
    exact (Nat.cast_le.mpr hmax).trans haZ
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_rpow_atTop (hκ.trans hκξ)).eventually_gt_atTop 2] with x hx hlarge
    obtain ⟨_, _, _, hvanish, _, _, _, _, hD, _, hrough⟩ := hfinite x hx
    intro t ht
    have htpos : 0 < t := by
      apply Nat.pos_of_ne_zero
      intro ht0
      subst t
      exact (not_le_of_gt hlarge) (ht 2 Nat.prime_two (dvd_zero 2))
    have hsharp : ∀ p : ℕ, p.Prime → p ∣ t → x ^ κ < (p : ℝ) :=
      fun p hp hpt => (Real.rpow_lt_rpow_of_exponent_lt hx hκξ).trans_le (ht p hp hpt)
    have hsum := hrough t htpos hsharp
    let lam (d : ℕ) : ℝ := selbergCoefficient (u x) (fun _ : Fin 1 => d)
    change (∑ d ∈ t.divisors, lam d) = 1 at hsum
    change (∑ e ∈ Du x, if e 0 ∣ t then selbergCoefficient (u x) e else 0) = 1
    dsimp only [Du]
    rw [hD, Finset.sum_image (fun a _ b _ hab => congrFun hab 0)]
    change (∑ d ∈ A x, if d ∣ t then lam d else 0) = 1
    rw [← Finset.sum_filter]
    calc
      _ = ∑ d ∈ t.divisors, lam d := by
        apply Finset.sum_subset
        · intro d hd
          exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, htpos.ne'⟩
        · intro d hd hnot
          apply hvanish d
          intro hdA
          exact hnot (Finset.mem_filter.mpr ⟨hdA, Nat.dvd_of_mem_divisors hd⟩)
      _ = 1 := hsum

open scoped ContDiff
open Classical in
theorem canonical_and_erased_auxiliary_marked_bin_physical_square
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {m : ℕ} (i : Fin 39) (r_c ζ_a l s : ℝ)
    (hζ_a : 0 < ζ_a) (hζrough : ζ_a < (9519 : ℝ) / 50000)
    (hl : 2 * ((9519 : ℝ) / 50000) ≤ l) (hls : l < s)
    (hs : s ≤ (40481 : ℝ) / 100000)
    (hmargin : s + 2 * (r_c + ζ_a) < 1)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) =
      ((19037 : ℝ) / 100000) / ((2624989 : ℝ) / 10000000))
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G))
    (hbF : Bornology.IsBounded (Set.range F))
    (u : ℝ → ((Fin 1 → ℕ) →₀ ℝ)) (E_a : ℝ) :
    let ρ : ℝ := 2624989 / 10000000
    let ξ₀ : ℝ := 19037 / 100000
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
          |(∑ v ∈ markedPrimePairBin x ((9519 : ℝ) / 50000)
                ((40481 : ℝ) / 100000) l s,
              ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
                  L x (n + h i) ^ 2 * C x n ^ 2 else 0) -
            (x / (W x : ℝ) / Bx x / BR x ^ 38) *
              ((∫ t in l..s,
                  Real.log ((t - (9519 : ℝ) / 50000) / ((9519 : ℝ) / 50000)) / t) *
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
  have hcap : ρ * κ < (9519 : ℝ) / 50000 := by
    dsimp only [κ]
    rw [mul_max_of_nonneg _ _ hρ.le]
    apply max_lt
    · norm_num [ζ, ξ₀, ρ]
    · rw [← mul_div_assoc, mul_div_cancel_left₀ _ hρ.ne']
      exact hζrough
  obtain ⟨M, hM, hamp⟩ :=
    canonical_and_erased_diagonal_amplitude (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i ζ hζ a G F hbG hbF
  obtain ⟨N, hN, haux⟩ := hauxData
  have hzlim : Tendsto
      (fun x => BR x ^ 38 * (z x).sum
        (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))) atTop
      (nhds (∫ Y, H Y ^ 2 ∂Measure.pi (fun _ : Fin 38 => ν))) := by
    have hraw := canonical_and_erased_polarized_harmonic_tendsto (𝓗 := 𝓗)
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
    ∑ v ∈ markedPrimePairBin x ((9519 : ℝ) / 50000)
        ((40481 : ℝ) / 100000) l s, (((v.1 * v.2 : ℕ) : ℝ))⁻¹
  let pairI : ℝ := ∫ t in l..s,
    Real.log ((t - (9519 : ℝ) / 50000) / ((9519 : ℝ) / 50000)) / t
  have hpair : Tendsto pairMass atTop (nhds pairI) :=
    markedPrimePairBin_harmonic_tendsto l s hl hls hs
  let S : ℝ → ℕ → ℝ := fun x b =>
    ∑ v ∈ markedPrimePairBin x ((9519 : ℝ) / 50000)
        ((40481 : ℝ) / 100000) l s,
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
    have hcomparison := selberg39_auxiliary_marked_bin_uniform (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      i κ r_c ζ_a M N ((9519 : ℝ) / 50000) ((40481 : ℝ) / 100000) l s
      hκ hζ_a hM.le hN (by norm_num) (by norm_num) (by linarith) hcap hmargin ε hε
    filter_upwards [hamp, haux, hsourceRadius, hcomparison]
      with x hampx hauxx hradx hcompx
    obtain ⟨hx, _, _, _, _, _, _, hzcoeff, hzsupport, hzbound⟩ := hampx
    obtain ⟨_, _, hubound, husupport⟩ := hauxx
    have hcommon := fragment_divisors_common_cap
      (W x) x ρ ζ ζ_a hx hρ
    have hzradius : ∀ r ∈ (z x).support,
        ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r_c := by
      apply selberg_diagonal_support_le_of_coefficient_le
        (z x) (fun r hr => (hzsupport r hr).1) (x ^ r_c)
      intro d hd
      apply hradx d
      by_cases hwzero : selbergCoefficient (w x) d = 0
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
  have hfinal := uniform_scaled_error_of_normalized_tendsto
    S A B E I hpos hlim harithmetic
  simpa only [S, A, B, I, I₀, pairI, div_mul_eq_div_div] using hfinal

open Classical in
theorem canonical_and_erased_auxiliary_marked_bin_physical_square_finset
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {J : Type*} {m : ℕ} (𝒥 : Finset J) (c : J → ℝ)
    (i : Fin 39) (r_c ζ_a l s : ℝ)
    (hζ_a : 0 < ζ_a) (hζrough : ζ_a < (9519 : ℝ) / 50000)
    (hl : 2 * ((9519 : ℝ) / 50000) ≤ l) (hls : l < s)
    (hs : s ≤ (40481 : ℝ) / 100000)
    (hmargin : s + 2 * (r_c + ζ_a) < 1)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) =
      ((19037 : ℝ) / 100000) / ((2624989 : ℝ) / 10000000))
    (G : J → (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : J → (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : ∀ j ∈ 𝒥, Measurable (G j)) (hF : ∀ j ∈ 𝒥, Measurable (F j))
    (hbG : ∀ j ∈ 𝒥, Bornology.IsBounded (Set.range (G j)))
    (hbF : ∀ j ∈ 𝒥, Bornology.IsBounded (Set.range (F j)))
    (u : ℝ → ((Fin 1 → ℕ) →₀ ℝ)) (E_a : ℝ) :
    let ρ : ℝ := 2624989 / 10000000
    let ξ₀ : ℝ := 19037 / 100000
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
          |(∑ v ∈ markedPrimePairBin x ((9519 : ℝ) / 50000)
                ((40481 : ℝ) / 100000) l s,
              ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
                  L x (n + h i) ^ 2 * C x n ^ 2 else 0) -
            (x / (W x : ℝ) / Bx x / BR x ^ 38) *
              ((∫ t in l..s,
                  Real.log ((t - (9519 : ℝ) / 50000) / ((9519 : ℝ) / 50000)) / t) *
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
  obtain ⟨hGsum, hbGsum, hcGsum⟩ := finite_profile_combination_regular
    (Measure.pi (fun _ : Fin 38 => ν)) 𝒥 c G hG hbG cG
  obtain ⟨hFsum, hbFsum, hcFsum⟩ := finite_profile_combination_regular
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
      if ∀ k, d k ∣ n + h (i.succAbove k) then selbergCoefficient (zsum x) d else 0
  let Hsum : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun Y =>
    Gsum Y + ∫ t : Fin (m + 1) → ℝ, Fsum (i.insertNth t Y) ∂ν
  have hw (x : ℝ) : wsum x = ∑ j ∈ 𝒥, c j • w j x :=
    canonical_diagonal_finset_smul 𝒥 c (T39 x) (X x) (BR x) G
  have hy (x : ℝ) : ysum x = ∑ j ∈ 𝒥, c j • y j x :=
    canonical_diagonal_finset_smul 𝒥 c (T40 x) (X x) (BR x) F
  have hz (x : ℝ) : zsum x = ∑ j ∈ 𝒥, c j • z j x := by
    dsimp only [zsum, z]
    rw [hw x, hy x, weighted_erasure_finset_smul]
    simp only [smul_add, Finset.sum_add_distrib]
  have hC : Csum = C := by
    funext x n
    dsimp only [Csum, C, Dz]
    rw [hz x]
    have hroot := selberg_divisor_root_finset_combination 𝒥 c (fun j => z j x)
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
    rw [(fixed_band_erased_finset_integral 𝒥 c i ζ a F hF hbF).2.2.2 Y]
    simp only [mul_add, Finset.sum_add_distrib, ν]
  have hradSum : ∀ᶠ x : ℝ in atTop, ∀ d : Fin 38 → ℕ,
      (selbergCoefficient (wsum x) d ≠ 0 ∨
        selbergCoefficient (ysum x) (i.insertNth 1 d) ≠ 0) →
      ((∏ k, d k : ℕ) : ℝ) ≤ x ^ r_c := by
    filter_upwards [(Filter.eventually_all_finset 𝒥).2 hsourceRadius] with x hx
    intro d hd
    rcases hd with hd | hd
    · rw [hw x] at hd
      exact selbergCoefficient_finset_radius 𝒥 c (fun j => w j x) d (x ^ r_c)
        (fun j hj hne => hx j hj d (Or.inl hne)) hd
    · rw [hy x] at hd
      obtain ⟨j, hj, _, hne⟩ :=
        (selbergCoefficient_finset_combination 𝒥 c (fun j => y j x)).2 (i.insertNth 1 d) hd
      exact hx j hj d (Or.inr hne)
  have hmain := canonical_and_erased_auxiliary_marked_bin_physical_square
    (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
    i r_c ζ_a l s hζ_a hζrough hl hls hs hmargin a ha ha0 haLast Gsum Fsum
    hGsum hFsum hbGsum hbFsum u E_a hcGsum hcFsum hauxData hulim hradSum
  change (∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ b : ℕ,
    |(∑ v ∈ markedPrimePairBin x ((9519 : ℝ) / 50000)
          ((40481 : ℝ) / 100000) l s,
        ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
            L x (n + h i) ^ 2 * Csum x n ^ 2 else 0) -
      (x / (W x : ℝ) / Bx x / BR x ^ 38) *
        ((∫ t in l..s,
            Real.log ((t - (9519 : ℝ) / 50000) / ((9519 : ℝ) / 50000)) / t) *
          ((∫ Y : Fin 38 → Fin (m + 1) → ℝ, Hsum Y ^ 2
              ∂Measure.pi (fun _ : Fin 38 => ν)) *
            E_a))| ≤
      ε * (x / (W x : ℝ) / Bx x / BR x ^ 38)) at hmain
  simpa only [hC, hH] using hmain

end PrimeGap182.Selberg

section
open scoped ContDiff

end

namespace PrimeGap182.Selberg

section
open Real Finset Filter Asymptotics

theorem selberg39_power_saving_error_small
    {𝓗 : Finset ℕ}
    (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hf : f =O[atTop] (fun x : ℝ => x ^ (1 - δ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      let ρ : ℝ := 2624989 / 10000000
      let W := presievingModulus 𝓗 x
      let Bx := fragmentNormalization W x
      let B := fragmentNormalization W (x ^ ρ)
      let A : ℝ := x / (W : ℝ) / Bx / B ^ 38
      1 < x ∧ 0 < A ∧ |f x| ≤ ε * A := by
  obtain ⟨C, hC, hbound⟩ := hf.exists_pos
  intro ε hε
  let ρ₀ : ℝ := 2624989 / 10000000
  have hρ : 0 < ρ₀ := by norm_num [ρ₀]
  have hρ1 : ρ₀ ≤ 1 := by norm_num [ρ₀]
  have hlogLimit : Tendsto (fun x : ℝ => Real.log x ^ 40 / x ^ δ)
      atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((40 : ℕ) : ℝ) hδ).tendsto_div_nhds_zero
  have hlimit : Tendsto (fun x : ℝ => C * Real.log x ^ 40 / x ^ δ)
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using hlogLimit.const_mul C
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    presieving_le_mul_log_eventually 𝓗 1 zero_lt_one,
    hbound.bound, hlimit.eventually_le_const hε] with x hx hWlog hfx hsmall
  intro ρ W Bx B A
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hW : 0 < W := presieving_pos 𝓗 x
  have hWR : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hφ : (0 : ℝ) < Nat.totient W := Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)
  have hratio0 : 0 < (Nat.totient W : ℝ) / (W : ℝ) := div_pos hφ hWR
  have hratio1 : (Nat.totient W : ℝ) / (W : ℝ) ≤ 1 :=
    (div_le_one hWR).mpr (Nat.cast_le.mpr (Nat.totient_le W))
  have hBx : 0 < Bx := mul_pos hratio0 hlog
  have hBxle : Bx ≤ Real.log x := mul_le_of_le_one_left hlog.le hratio1
  have hBscale : B = ρ₀ * Bx := by
    change fragmentNormalization W (x ^ ρ₀) = ρ₀ * fragmentNormalization W x
    unfold fragmentNormalization
    rw [Real.log_rpow hx0]
    ring
  have hB : 0 < B := by rw [hBscale]; exact mul_pos hρ hBx
  have hBle : B ≤ Real.log x := by
    rw [hBscale]
    exact (mul_le_of_le_one_left hBx.le hρ1).trans hBxle
  have hA : 0 < A := div_pos (div_pos (div_pos hx0 hWR) hBx) (pow_pos hB 38)
  have hWlog' : (W : ℝ) ≤ Real.log x := by simpa only [one_mul] using hWlog
  have hden : (W : ℝ) * Bx * B ^ 38 ≤ Real.log x ^ 40 := by
    calc
      _ ≤ Real.log x * Real.log x * Real.log x ^ 38 :=
        mul_le_mul
          (mul_le_mul hWlog' hBxle hBx.le hlog.le)
          (pow_le_pow_left₀ hB.le hBle 38) (pow_nonneg hB.le 38)
          (mul_nonneg hlog.le hlog.le)
      _ = _ := by ring
  have hxδ : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hfx' : |f x| ≤ C * x ^ (1 - δ) := by
    simpa only [Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx0 (1 - δ))] using hfx
  refine ⟨hx, hA, (div_le_iff₀ hA).mp ?_⟩
  calc
    |f x| / A ≤ (C * x ^ (1 - δ)) / A := div_le_div_of_nonneg_right hfx' hA.le
    _ = C * ((W : ℝ) * Bx * B ^ 38) / x ^ δ := by
      dsimp only [A]
      rw [Real.rpow_sub hx0, Real.rpow_one]
      field_simp [hWR.ne', hBx.ne', hB.ne', hx0.ne', hxδ.ne']
    _ ≤ C * Real.log x ^ 40 / x ^ δ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hC.le) hxδ.le
    _ ≤ ε := hsmall

end

open Classical in
theorem canonical_and_erased_finite_coefficient_log_root_subpower
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {m : ℕ} {J : Type*} [Fintype J]
    (i : Fin 39) (κ : ℝ) (hκ : 0 < κ)
    (a : Fin (m + 2) → ℝ) (c : J → ℝ)
    (G : J → (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : J → (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hbG : ∀ j, Bornology.IsBounded (Set.range (G j)))
    (hbF : ∀ j, Bornology.IsBounded (Set.range (F j))) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W : ℝ → ℕ := fun x =>
      presievingModulus 𝓗 x
    let R : ℝ → ℝ := fun x => x ^ ρ
    let B : ℝ → ℝ := fun x =>
      fragmentNormalization (W x) (R x)
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) κ, p
    let T39 := fun x => (Fintype.piFinset (fun _ : Fin 38 => (q x).divisors)).filter
      (fun r => Squarefree (∏ k, r k))
    let T40 := fun x => (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
      (fun r => Squarefree (∏ k, r k))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    let w : J → ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun j x =>
      ∑ r ∈ T39 x, Finsupp.single r (G j (fun k => X x (r k)) / B x ^ 38)
    let y : J → ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun j x =>
      ∑ r ∈ T40 x, Finsupp.single r (F j (fun k => X x (r k)) / B x ^ 39)
    let e : J → ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun j x =>
      (y j x).sum (fun r yr => Finsupp.single (fun k => r (i.succAbove k))
        (yr / ((r i).totient : ℝ)))
    let z : J → ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun j x => w j x + e j x
    let Z : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x => ∑ j, c j • z j x
    let D : J → ℝ → Finset (Fin 38 → ℕ) := fun j x =>
      (z j x).support.biUnion (fun r => Fintype.piFinset (fun k => (r k).divisors))
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      1 < x ∧ ∀ d : Fin 38 → ℕ, |selbergCoefficient (Z x) d| ≤ C * Real.log x) ∧
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ᶠ x : ℝ in Filter.atTop,
        ∀ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          |∑ j, c j *
            (∑ d ∈ D j x, if ∀ k, d k ∣ n + h (i.succAbove k) then
              selbergCoefficient (z j x) d else 0)| ≤ A * x ^ ε := by
  intro ρ h W R B q T39 T40 X w y e z Z D
  let Cκ : ℝ := Real.exp Real.eulerMascheroniConstant * κ + 1
  let M_R : ℝ → ℝ := fun x =>
    harmonicFragmentMass (W x) (R x) κ
  have hρ : 0 < ρ := by norm_num [ρ]
  have hCκ : 0 < Cκ := by dsimp [Cκ]; positivity
  have hsum_bound (b K : J → ℝ) (t : ℝ) (ht : 0 ≤ t)
      (hb : ∀ j, |b j| ≤ K j * t) :
      |∑ j, c j * b j| ≤ (1 + ∑ j, |c j| * K j) * t := by
    calc
      |∑ j, c j * b j| ≤ ∑ j, |c j * b j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |c j| * (K j * t) := Finset.sum_le_sum fun j _ => by
        simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hb j) (abs_nonneg (c j))
      _ = (∑ j, |c j| * K j) * t := by simp only [Finset.sum_mul, mul_assoc]
      _ ≤ (1 + ∑ j, |c j| * K j) * t :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ht
  have hnorm := harmonic_fragment_normalizer_tendsto
    𝓗 ρ κ hρ hκ
  have hindividual (j : J) :
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
        1 < x ∧ ∀ d : Fin 38 → ℕ,
          |selbergCoefficient (z j x) d| ≤ C * Real.log x) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ᶠ x : ℝ in Filter.atTop,
          ∀ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            |∑ d ∈ D j x, if ∀ k, d k ∣ n + h (i.succAbove k) then
              selbergCoefficient (z j x) d else 0| ≤ A * x ^ ε := by
    obtain ⟨M, hM, hcoeff, hroot⟩ :=
      canonical_and_erased_coefficient_root_subpower
        (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ hκ a (G j) (F j) (hbG j) (hbF j)
    obtain ⟨_, _, hamp⟩ :=
      canonical_and_erased_diagonal_amplitude
        (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ hκ a (G j) (F j) (hbG j) (hbF j)
    let K : ℝ := M * Cκ ^ 38
    have hK : 0 < K := mul_pos hM (pow_pos hCκ 38)
    refine ⟨⟨K * Cκ * ρ, mul_pos (mul_pos hK hCκ) hρ, ?_⟩, hroot⟩
    filter_upwards [hcoeff, hamp, hnorm.eventually_le_const (lt_add_one _)] with x hc ha hm
    obtain ⟨hx, hB, hc⟩ := hc
    change 0 < B x at hB
    change M_R x / B x ≤ Cκ at hm
    obtain ⟨_, _, _, _, _, _, _, _, hzsupport, _⟩ := ha
    change (∀ r ∈ (z j x).support,
      Squarefree (∏ k, r k) ∧ ∀ k, r k ∈ (q x).divisors) at hzsupport
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hBupper : B x ≤ ρ * Real.log x := by
      change ((Nat.totient (W x) : ℝ) / (W x : ℝ)) * Real.log (x ^ ρ) ≤ _
      rw [Real.log_rpow (lt_trans zero_lt_one hx)]
      apply mul_le_of_le_one_left (mul_nonneg hρ.le hlog)
      exact div_le_one_of_le₀ (Nat.cast_le.mpr (Nat.totient_le (W x))) (Nat.cast_nonneg _)
    have hq : Squarefree (q x) := by
      apply (squarefree_primorial ⌊R x ^ κ⌋₊).squarefree_of_dvd
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    have hsupport : ∀ r ∈ (z j x).support, (∏ k, r k) ∣ q x := by
      intro r hr
      obtain ⟨hsq, hd⟩ := hzsupport r hr
      apply hsq.isRadical 38 (q x)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Finset.prod_dvd_prod_of_dvd (s := Finset.univ) r (fun _ => q x)
          (fun k _ => Nat.dvd_of_mem_divisors (hd k))
    refine ⟨hx, ?_⟩
    intro d
    by_cases hd : selbergCoefficient (z j x) d = 0
    · rw [hd, abs_zero]
      exact mul_nonneg (mul_pos (mul_pos hK hCκ) hρ).le hlog
    · let D₀ : ℕ := ∏ k, d k
      have hDq : D₀ ∣ q x :=
        selbergCoefficient_mem_hereditary (z j x) (fun d => (∏ k, d k) ∣ q x)
          (fun d r hdr hr =>
            (Finset.prod_dvd_prod_of_dvd d r (fun k _ => hdr k)).trans hr)
          hsupport d hd
      have hratio : (D₀ : ℝ) / (D₀.totient : ℝ) ≤ M_R x := by
        rw [squarefree_div_totient_eq_sum_divisors_inv_totient
          (hq.squarefree_of_dvd hDq)]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Nat.divisors_subset_of_dvd hq.ne_zero hDq)
          (fun r _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      calc
        |selbergCoefficient (z j x) d| ≤ K * ((D₀ : ℝ) / (D₀.totient : ℝ)) := (hc d).2
        _ ≤ K * M_R x := mul_le_mul_of_nonneg_left hratio hK.le
        _ ≤ K * (Cκ * B x) := mul_le_mul_of_nonneg_left ((div_le_iff₀ hB).mp hm) hK.le
        _ ≤ K * (Cκ * (ρ * Real.log x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBupper hCκ.le) hK.le
        _ = (K * Cκ * ρ) * Real.log x := by ac_rfl
  constructor
  · choose C hC hbound using fun j => (hindividual j).1
    refine ⟨1 + ∑ j, |c j| * C j,
      add_pos_of_pos_of_nonneg zero_lt_one
        (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hC j).le), ?_⟩
    filter_upwards [Filter.eventually_all.mpr hbound,
      Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
    refine ⟨hx1, ?_⟩
    intro d
    have hlinear :=
      (selbergCoefficient_finset_combination Finset.univ c (fun j => z j x)).1 d
    change selbergCoefficient (Z x) d = ∑ j, c j * selbergCoefficient (z j x) d at hlinear
    rw [hlinear]
    exact hsum_bound (fun j => selbergCoefficient (z j x) d) C (Real.log x)
      (Real.log_nonneg hx1.le) (fun j => (hx j).2 d)
  · intro ε hε
    choose A hA hroot using fun j => (hindividual j).2 ε hε
    refine ⟨1 + ∑ j, |c j| * A j,
      add_pos_of_pos_of_nonneg zero_lt_one
        (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hA j).le), ?_⟩
    filter_upwards [Filter.eventually_all.mpr hroot,
      Filter.eventually_gt_atTop (0 : ℝ)] with x hx hx0
    intro n hn
    exact hsum_bound
      (fun j => ∑ d ∈ D j x, if ∀ k, d k ∣ n + h (i.succAbove k) then
        selbergCoefficient (z j x) d else 0)
      A (x ^ ε) (Real.rpow_nonneg hx0.le _) (fun j => hx j n hn)

section
open Real Filter Asymptotics
open scoped ContDiff
open Classical in
theorem canonical_and_erased_exceptional_square
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {J : Type*} {m : ℕ} (𝒥 : Finset J) (c : J → ℝ) (i : Fin 39)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) =
      ((19037 : ℝ) / 100000) / ((2624989 : ℝ) / 10000000))
    (G : J → (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : J → (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : ∀ j ∈ 𝒥, Measurable (G j)) (hF : ∀ j ∈ 𝒥, Measurable (F j))
    (hbG : ∀ j ∈ 𝒥, Bornology.IsBounded (Set.range (G j)))
    (hbF : ∀ j ∈ 𝒥, Bornology.IsBounded (Set.range (F j))) :
    let ρ : ℝ := 2624989 / 10000000
    let ξ₀ : ℝ := 19037 / 100000
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
    let Dz : J → ℝ → Finset (Fin 38 → ℕ) := fun j x =>
      (z j x).support.biUnion
        (fun r => Fintype.piFinset (fun k => (r k).divisors))
    let C : ℝ → ℕ → ℝ := fun x n =>
      ∑ j ∈ 𝒥, c j *
        (∑ d ∈ Dz j x, if ∀ k, d k ∣ n + h (i.succAbove k) then
          PrimeGap182.Selberg.selbergCoefficient (z j x) d else 0)
    let H : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun Y =>
      ∑ j ∈ 𝒥, c j *
        (G j Y + ∫ t : Fin (m + 1) → ℝ, F j (i.insertNth t Y) ∂ν)
    (∀ j ∈ 𝒥, ∀ᶠ x : ℝ in Filter.atTop,
      ∀ d : Fin 38 → ℕ,
        (PrimeGap182.Selberg.selbergCoefficient (w j x) d ≠ 0 ∨
          PrimeGap182.Selberg.selbergCoefficient (y j x) (i.insertNth 1 d) ≠ 0) →
        ((∏ k, d k : ℕ) : ℝ) ≤ x ^ (11 / 40 : ℝ)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop, ∀ b : ℕ,
      (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq (W x) n b then
          (exceptionalPrimeDefect x 0 (n + h i) +
            exceptionalPrimeDefect x 1 (n + h i)) * C x n ^ 2 else 0) ≤
        (((17 : ℝ) / 50) * (ρ ^ 38)⁻¹ *
            (∫ Y : Fin 38 → Fin (m + 1) → ℝ, H Y ^ 2
              ∂Measure.pi (fun _ : Fin 38 => ν)) + ε) *
          (x / (W x : ℝ) / Bx x ^ 39) := by
  intro ρ ξ₀ ζ ν cG cF h W R Bx BR q T39 T40 X w y z Dz C H hsourceRadius
  have hρ : 0 < ρ := by norm_num [ρ]
  have hζ : 0 < ζ := by norm_num [ζ, ξ₀, ρ]
  let ξ : ℝ := 9519 / 50000
  let s : Fin 1024 → ℝ := fun j => (exceptionalBinRight j : ℝ)
  let l : Fin 1024 → ℝ := fun j => s j - (exceptionalBinStep : ℝ)
  let ζa : Fin 1024 → ℝ := fun j => (exceptionalBinAuxRadius j : ℝ)
  have hbin (j : Fin 1024) :
      0 < ζa j ∧ ζa j < ξ ∧ 2 * ξ ≤ l j ∧ l j < s j ∧
        s j ≤ (40481 : ℝ) / 100000 ∧ s j + 2 * ((11 : ℝ) / 40 + ζa j) < 1 := by
    obtain ⟨hstep, _, hs, hzlo, hzhi, hxi0, hxi, hgap, _⟩ := exceptionalBin_margins j
    have hstepR : (0 : ℝ) < (exceptionalBinStep : ℝ) := Rat.cast_pos.mpr hstep
    have hzposQ : (0 : ℚ) < exceptionalBinAuxRadius j :=
      (by norm_num : (0 : ℚ) < 4499 / 200000).trans_le hzlo
    have hzxiQ : exceptionalBinAuxRadius j < (9519 : ℚ) / 50000 :=
      hzhi.trans (hxi0.trans hxi)
    have hsR : s j ≤ (40481 : ℝ) / 100000 := by
      simpa only [s, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hs
    have hgapR : s j + 2 * (11 / 40 : ℝ) + 2 * ζa j = 1 - 1 / 5000 := by
      simpa only [s, ζa, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
        Rat.cast_ofNat, Rat.cast_one] using congrArg (fun r : ℚ => (r : ℝ)) hgap
    have hsEq : s j = 2 * ξ + ((j.val : ℝ) + 1) * (exceptionalBinStep : ℝ) := by
      dsimp only [s, exceptionalBinRight, ξ]
      push_cast
      rfl
    refine ⟨Rat.cast_pos.mpr hzposQ, ?_, ?_, ?_, hsR, ?_⟩
    · simpa only [ζa, ξ, Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr hzxiQ
    · dsimp only [l]
      rw [hsEq]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j.val) hstepR.le]
    · dsimp only [l]
      linarith
    · linarith
  let Aa : Fin 1024 → ℝ → Finset ℕ := fun j x =>
    (Finset.Icc 1 ⌊x ^ (ζa j)⌋₊).filter
      (fun t => Squarefree t ∧ Nat.Coprime t (W x))
  let Gaux : Fin 1024 → ℝ → ℝ := fun j x =>
    ∑ t ∈ Aa j x, 1 / (t.totient : ℝ)
  let u : Fin 1024 → ℝ → ((Fin 1 → ℕ) →₀ ℝ) := fun j x =>
    ∑ t ∈ Aa j x, Finsupp.single (fun _ : Fin 1 => t) (1 / Gaux j x)
  let Du : Fin 1024 → ℝ → Finset (Fin 1 → ℕ) := fun j x =>
    (u j x).support.biUnion
      (fun t => Fintype.piFinset (fun k => (t k).divisors))
  let L : Fin 1024 → ℝ → ℕ → ℝ := fun j x t =>
    ∑ e ∈ Du j x, if e 0 ∣ t then selbergCoefficient (u j x) e else 0
  let I : ℝ := ∫ Y : Fin 38 → Fin (m + 1) → ℝ,
    H Y ^ 2 ∂Measure.pi (fun _ : Fin 38 => ν)
  let E : Fin 1024 → ℝ := fun j => 1 / ζa j
  let D : Fin 1024 → ℝ := fun j =>
    ∫ t in l j..s j, Real.log ((t - ξ) / ξ) / t
  let P : Fin 1024 → ℝ → Finset (ℕ × ℕ) := fun j x =>
    markedPrimePairBin x ξ ((40481 : ℝ) / 100000) (l j) (s j)
  let A : ℝ → ℝ := fun x => x / (W x : ℝ) / Bx x / BR x ^ 38
  let S : Fin 1024 → ℝ → ℕ → ℝ := fun j x b =>
    ∑ pq ∈ P j x, ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq (W x) n b ∧ pq.1 * pq.2 ∣ n + h i then
        L j x (n + h i) ^ 2 * C x n ^ 2 else 0
  have hI : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
  have hfamily (j : Fin 1024) := sharp_auxiliary_family
    𝓗 (ζa j) ξ (hbin j).1 (hbin j).2.1
  have henergyUpper : (12 / 5 : ℝ) * (∑ j, E j * D j) ≤
      (exceptionalBinRationalSum : ℝ) := by
    have hterm (j : Fin 1024) : (12 / 5 : ℝ) * E j * D j ≤
        (exceptionalBinCeiling j : ℝ) / (10 : ℝ) ^ 25 := by
      simpa only [E, D, l, s, ζa, ξ, one_div] using
        (exceptionalBin_integral_upper j).2
    calc
      _ = ∑ j : Fin 1024, (12 / 5 : ℝ) * E j * D j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
      _ ≤ ∑ j : Fin 1024, (exceptionalBinCeiling j : ℝ) / (10 : ℝ) ^ 25 :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = _ := by
        simp only [exceptionalBinRationalSum, Rat.cast_div, Rat.cast_sum,
          Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat, Finset.sum_div]
  have henergy : (12 / 5 : ℝ) * (∑ j, E j * D j) < 17 / 50 := by
    have hsumLt : (exceptionalBinRationalSum : ℝ) < (337 / 1000 : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr exceptionalBinRationalSum_value.2.1
    exact (henergyUpper.trans_lt hsumLt).trans (by norm_num)
  have hrough (j : Fin 1024) : ∀ᶠ x : ℝ in atTop,
      ∀ t : ℕ, (∀ p : ℕ, p.Prime → p ∣ t → x ^ ξ ≤ (p : ℝ)) → L j x t = 1 :=
    (hfamily j).2.2
  have hmarked (j : Fin 1024) (η : ℝ) (hη : 0 < η) :
      ∀ᶠ x : ℝ in atTop, ∀ b : ℕ,
        |S j x b - A x * (D j * (I * E j))| ≤ η * A x :=
    canonical_and_erased_auxiliary_marked_bin_physical_square_finset (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      𝒥 c i (11 / 40) (ζa j) (l j) (s j)
      (hbin j).1 (hbin j).2.1 (hbin j).2.2.1 (hbin j).2.2.2.1
      (hbin j).2.2.2.2.1 (hbin j).2.2.2.2.2
      a ha ha0 haLast G F hG hF hbG hbF (u j) (E j) cG cF
      (hfamily j).2.1 (hfamily j).1 hsourceRadius η hη
  have hsubpower (δ : ℝ) (hδ : 0 < δ) :
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
        ∀ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, |C x n| ≤ K * x ^ δ := by
    have ht := (canonical_and_erased_finite_coefficient_log_root_subpower
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      (J := 𝒥) i ζ hζ a (fun j => c j.val)
      (fun j => G j.val) (fun j => F j.val)
      (fun j => hbG j.val j.property) (fun j => hbF j.val j.property)).2 δ hδ
    obtain ⟨K, hK, ht⟩ := ht
    refine ⟨K, hK, ?_⟩
    filter_upwards [ht] with x hx
    intro n hn
    have hb := hx n hn
    change |∑ j : 𝒥, c j.val *
      (∑ d ∈ Dz j.val x, if ∀ k, d k ∣ n + h (i.succAbove k) then
        selbergCoefficient (z j.val x) d else 0)| ≤ K * x ^ δ at hb
    change |∑ j ∈ 𝒥, c j *
      (∑ d ∈ Dz j x, if ∀ k, d k ∣ n + h (i.succAbove k) then
        selbergCoefficient (z j x) d else 0)| ≤ K * x ^ δ
    rw [Finset.sum_subtype 𝒥 (fun _ => Iff.rfl)]
    exact hb
  let B : ℝ → ℕ → ℝ := fun x n =>
    exceptionalPrimeDefect x 0 (n + h i) +
      exceptionalPrimeDefect x 1 (n + h i)
  let ER : ℝ → ℝ := fun x => ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if ¬Squarefree (n + h i) ∧ ((n + h i : ℕ) : ℝ) ≤ 2 * x then
      B x n * C x n ^ 2 else 0
  let EE : ℝ → ℝ := fun x => ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if 2 * x < ((n + h i : ℕ) : ℝ) then B x n * C x n ^ 2 else 0
  have hER : ER =O[atTop] (fun x : ℝ => x ^ (1 - ξ / 2)) :=
    shifted_nonsquarefree_exceptional_weighted_isBigO (h i) C
      (hsubpower (ξ / 4) (by norm_num [ξ]))
  have hEE : EE =O[atTop] (fun x : ℝ => x ^ (1 - (1 / 2 : ℝ))) := by
    simpa only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] using
      exceptionalPrimeDefect_shifted_endpoint_error (h i) C
        (hsubpower (1 / 8) (by norm_num))
  have hB (x : ℝ) (n : ℕ) : 0 ≤ B x n :=
    add_nonneg (exceptionalPrimeDefect_nonneg x 0 _)
      (exceptionalPrimeDefect_nonneg x 1 _)
  intro ε hε
  let ε' : ℝ := ε * ρ ^ 38
  let η : ℝ := ε' / (3 * (12 / 5) * 1024)
  have hε' : 0 < ε' := mul_pos hε (pow_pos hρ 38)
  have hη : 0 < η := div_pos hε' (by norm_num)
  have hsmallR := selberg39_power_saving_error_small (𝓗 := 𝓗) ER (ξ / 2)
    (by norm_num [ξ]) hER (ε' / 3) (by positivity)
  have hsmallE := selberg39_power_saving_error_small (𝓗 := 𝓗) EE (1 / 2)
    (by norm_num) hEE (ε' / 3) (by positivity)
  filter_upwards [Filter.eventually_all.mpr (fun j => hmarked j η hη),
    Filter.eventually_all.mpr hrough,
    eventually_exceptionalPrimeDefect_bin_square_majorant,
    hsmallR, hsmallE] with x hmarkedx hroughx hmajorx hRx hEx
  have hx : 1 < x := hRx.1
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hA : 0 < A x := hRx.2.1
  have hRsmall : ER x ≤ (ε' / 3) * A x := (le_abs_self _).trans hRx.2.2
  have hEsmall : EE x ≤ (ε' / 3) * A x := (le_abs_self _).trans hEx.2.2
  intro b
  let U : ℕ → ℝ := fun n =>
    ∑ j : Fin 1024, ∑ pq ∈ P j x,
      if Nat.ModEq (W x) n b ∧ pq.1 * pq.2 ∣ n + h i then
        L j x (n + h i) ^ 2 * C x n ^ 2 else 0
  have hU (n : ℕ) : 0 ≤ U n := by
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) :
      (if Nat.ModEq (W x) n b then B x n * C x n ^ 2 else 0) ≤
        (12 / 5 : ℝ) * U n +
          (if ¬Squarefree (n + h i) ∧ ((n + h i : ℕ) : ℝ) ≤ 2 * x then
            B x n * C x n ^ 2 else 0) +
          (if 2 * x < ((n + h i : ℕ) : ℝ) then B x n * C x n ^ 2 else 0) := by
    have hb0 : 0 ≤ B x n * C x n ^ 2 := mul_nonneg (hB x n) (sq_nonneg _)
    by_cases hm : Nat.ModEq (W x) n b
    · rw [ite_eq_left hm]
      by_cases he : 2 * x < ((n + h i : ℕ) : ℝ)
      · simp only [not_le_of_gt he, and_false, ite_false, ite_eq_left he]
        nlinarith [hU n]
      · have hupper : ((n + h i : ℕ) : ℝ) ≤ 2 * x := le_of_not_gt he
        by_cases hsf : Squarefree (n + h i)
        · have hlower : x ≤ ((n + h i : ℕ) : ℝ) :=
            (Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1).trans
              (Nat.cast_le.mpr (Nat.le_add_right n (h i)))
          have hgood := hmajorx (fun j => L j x)
            (fun j t _ ht => hroughx j t ht) (n + h i) (C x n) hlower hupper hsf
          have hu : U n = ∑ j : Fin 1024, ∑ pq ∈ P j x,
              if pq.1 * pq.2 ∣ n + h i then (L j x (n + h i) * C x n) ^ 2 else 0 := by
            simp only [U, hm, true_and, mul_pow]
          rw [hu]
          simpa only [hsf, not_true_eq_false, false_and, he, ite_false, add_zero] using hgood
        · simp only [hsf, not_false_eq_true, hupper, true_and, ite_true, he, ite_false,
            add_zero]
          nlinarith [hU n]
    · rw [ite_eq_right hm]
      exact add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (hU n)) (by split_ifs <;> positivity))
        (by split_ifs <;> positivity)
  have hsumU : (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, U n) = ∑ j : Fin 1024, S j x b := by
    dsimp only [U, S]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  have htotal :
      (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq (W x) n b then B x n * C x n ^ 2 else 0) ≤
        (12 / 5 : ℝ) * (∑ j : Fin 1024, S j x b) + ER x + EE x := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          ((12 / 5 : ℝ) * U n +
            (if ¬Squarefree (n + h i) ∧ ((n + h i : ℕ) : ℝ) ≤ 2 * x then
              B x n * C x n ^ 2 else 0) +
            (if 2 * x < ((n + h i : ℕ) : ℝ) then B x n * C x n ^ 2 else 0)) :=
        Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hsumU]
  have hsumMarked :
      (12 / 5 : ℝ) * (∑ j : Fin 1024, S j x b) ≤
        ((17 / 50 : ℝ) * I + ε' / 3) * A x := by
    have hupper (j : Fin 1024) : S j x b ≤ A x * (D j * (I * E j)) + η * A x :=
      le_add_of_sub_left_le (abs_le.mp (hmarkedx j b)).2
    calc
      _ ≤ (12 / 5 : ℝ) *
          (∑ j : Fin 1024, (A x * (D j * (I * E j)) + η * A x)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hupper j) (by norm_num)
      _ = (((12 / 5 : ℝ) * (∑ j : Fin 1024, E j * D j)) * I + ε' / 3) * A x := by
        rw [Finset.sum_add_distrib]
        have hmain : (∑ j : Fin 1024, A x * (D j * (I * E j))) =
            (A x * I) * (∑ j : Fin 1024, E j * D j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hmain, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp only [η]
        norm_num
        ring
      _ ≤ ((17 / 50 : ℝ) * I + ε' / 3) * A x :=
        mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_right henergy.le hI) le_rfl) hA.le
  have hfinal :
      (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq (W x) n b then B x n * C x n ^ 2 else 0) ≤
        ((17 / 50 : ℝ) * I + ε') * A x := by
    calc
      _ ≤ (12 / 5 : ℝ) * (∑ j : Fin 1024, S j x b) + ER x + EE x := htotal
      _ ≤ (((17 / 50 : ℝ) * I + ε' / 3) * A x) +
          (ε' / 3) * A x + (ε' / 3) * A x :=
        add_le_add (add_le_add hsumMarked hRsmall) hEsmall
      _ = _ := by ring
  have hBRscale : BR x = ρ * Bx x := by
    dsimp only [BR, R, Bx, fragmentNormalization]
    rw [Real.log_rpow hx0]
    ring
  have hAscale : A x = (ρ ^ 38)⁻¹ * (x / (W x : ℝ) / Bx x ^ 39) := by
    simp only [A, hBRscale, mul_pow, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring
  calc
    _ ≤ ((17 / 50 : ℝ) * I + ε') * A x := hfinal
    _ = _ := by
      rw [hAscale]
      dsimp only [ε']
      field_simp [hρ.ne']
      ring

end

theorem selberg_sampled_coefficient_root {ι : Type*} [Fintype ι]
    (T : Finset (ι → ℕ)) (f : (ι → ℕ) → ℝ) (Z : ℝ) (d : ι → ℕ)
    (hd : selbergCoefficient (∑ r ∈ T, Finsupp.single r (f r / Z)) d ≠ 0) :
    ∃ r ∈ T, f r ≠ 0 ∧ ∀ j, d j ∣ r j := by
  classical
  apply selbergCoefficient_mem_hereditary
    (∑ r ∈ T, Finsupp.single r (f r / Z))
    (fun e => ∃ r ∈ T, f r ≠ 0 ∧ ∀ j, e j ∣ r j) ?_ ?_ d hd
  · rintro e s hes ⟨r, hr, hfr, hsr⟩
    exact ⟨r, hr, hfr, fun j => (hes j).trans (hsr j)⟩
  · intro r hr
    obtain ⟨s, hs, hsingle⟩ := Finsupp.mem_support_finsetSum r hr
    obtain ⟨rfl, hne⟩ := (Finsupp.mem_support_single r s (f s / Z)).mp hsingle
    exact ⟨r, hs, (div_ne_zero_iff.mp hne).1, fun j => dvd_rfl⟩

open Classical in
theorem selberg_sampled_coefficient_presieve {ι : Type*} [Fintype ι]
    (W : ℕ) (R κ Z : ℝ) (f : (ι → ℕ) → ℝ) (d : ι → ℕ) :
    let q := ∏ p ∈ fragmentPrimes W R κ, p
    let T := (Fintype.piFinset (fun _ : ι => q.divisors)).filter
      (fun r => Squarefree (∏ j, r j))
    let y := ∑ r ∈ T, Finsupp.single r (f r / Z)
    selbergCoefficient y d ≠ 0 →
      Squarefree (∏ j, d j) ∧ (∏ j, d j).Coprime W ∧ (∏ j, d j) ∣ q ∧
        ∃ r ∈ T, f r ≠ 0 ∧ ∀ j, d j ∣ r j := by
  intro q T y hd
  obtain ⟨r, hr, hfr, hdr⟩ := selberg_sampled_coefficient_root T f Z d hd
  dsimp only [T] at hr
  have hrT := Finset.mem_filter.mp hr
  have hrq : ∀ j, r j ∣ q := fun j =>
    (Nat.mem_divisors.mp ((Fintype.mem_piFinset.mp hrT.1) j)).1
  have hqW : q.Coprime W := by
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨hp, hpW⟩ := Finset.mem_filter.mp hp
    exact (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primesLE hp)).mpr hpW
  have hprod : (∏ j, d j) ∣ ∏ j, r j :=
    Finset.prod_dvd_prod_of_dvd d r (fun j _ => hdr j)
  have hsq : Squarefree (∏ j, d j) := hrT.2.squarefree_of_dvd hprod
  have hwhole : (∏ j, d j) ∣ q := by
    apply hsq.isRadical (Fintype.card ι) q
    simpa only [Finset.prod_const, Finset.card_univ] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.univ) d (fun _ => q)
        (fun j _ => (hdr j).trans (hrq j))
  exact ⟨hsq, hqW.coprime_dvd_left hwhole, hwhole, r, hr, hfr, hdr⟩

theorem selberg_sampled_erased_coefficient_presieve
    (W : ℕ) (R κ Z : ℝ) (f : (Fin 39 → ℕ) → ℝ) (i : Fin 39)
    (d : Fin 38 → ℕ) :
    let q := ∏ p ∈ fragmentPrimes W R κ, p
    let T := (Fintype.piFinset (fun _ : Fin 39 => q.divisors)).filter
      (fun r => Squarefree (∏ j, r j))
    let y := ∑ r ∈ T, Finsupp.single r (f r / Z)
    let z : (Fin 38 → ℕ) →₀ ℝ :=
      y.sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
        (yr / ((r i).totient : ℝ)))
    selbergCoefficient z d ≠ 0 →
      Squarefree (∏ j, d j) ∧ (∏ j, d j).Coprime W ∧ (∏ j, d j) ∣ q ∧
        ∃ r ∈ T, f r ≠ 0 ∧ ∀ j, d j ∣ r (i.succAbove j) := by
  intro q T y z hd
  have hfull : selbergCoefficient y (i.insertNth 1 d) ≠ 0 := by
    rw [← selbergCoefficient_weighted_erase i y d]
    exact hd
  obtain ⟨r, hr, hfr, hdr⟩ :=
    selberg_sampled_coefficient_root T f Z (i.insertNth 1 d) hfull
  dsimp only [T] at hr
  have hrT := Finset.mem_filter.mp hr
  have hrq (j : Fin 39) : r j ∣ q :=
    (Nat.mem_divisors.mp ((Fintype.mem_piFinset.mp hrT.1) j)).1
  have hret (j : Fin 38) : d j ∣ r (i.succAbove j) := by
    simpa only [Fin.insertNth_apply_succAbove] using hdr (i.succAbove j)
  have hprod : (∏ j : Fin 38, d j) ∣ ∏ j : Fin 39, r j := by
    have hh := Finset.prod_dvd_prod_of_dvd (s := Finset.univ)
      (i.insertNth 1 d) r (fun j _ => hdr j)
    simpa only [Fin.prod_insertNth, one_mul] using hh
  have hsq : Squarefree (∏ j : Fin 38, d j) := hrT.2.squarefree_of_dvd hprod
  have hqW : q.Coprime W := by
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨hp, hpW⟩ := Finset.mem_filter.mp hp
    exact (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primesLE hp)).mpr hpW
  have hwhole : (∏ j : Fin 38, d j) ∣ q := by
    apply hsq.isRadical 38 q
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.univ) d (fun _ => q)
        (fun j _ => (hret j).trans (hrq (i.succAbove j)))
  exact ⟨hsq, hqW.coprime_dvd_left hwhole, hwhole, r, hr, hfr, hret⟩

theorem coherent_color_fiber_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ) (T : Finset ι) (f : ι → Fin c) :
    ((Finset.univ : Finset (ι → Fin c)).filter
      (fun g => ∀ i ∈ T, g i = f i)).card = c ^ Tᶜ.card := by
  classical
  have hfiber :
      (Finset.univ : Finset (ι → Fin c)).filter (fun g => ∀ i ∈ T, g i = f i) =
        Fintype.piFinset (fun i => if i ∈ T then {f i} else Finset.univ) := by
    ext g
    simp [Fintype.mem_piFinset, mem_ite]
  rw [hfiber, Fintype.card_piFinset]
  simp only [apply_ite, Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
  simpa only [Finset.mem_compl, ite_not, Finset.prod_const] using
    Finset.prod_ite_mem_eq Tᶜ (fun _ : ι => c)

theorem coherent_color_projection_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ) (hc : 0 < c) (T : Finset ι) (E : (ι → Fin c) → ℝ)
    (hE : ∀ g, 0 ≤ E g)
    (hlocal : ∀ f g, (∀ i ∈ T, f i = g i) → E f = E g)
    (f : ι → Fin c) :
    E f ≤ (c : ℝ) ^ T.card / (c : ℝ) ^ Fintype.card ι * ∑ g, E g := by
  classical
  let S : Finset (ι → Fin c) :=
    Finset.univ.filter (fun g => ∀ i ∈ T, g i = f i)
  have hcard : S.card = c ^ Tᶜ.card := coherent_color_fiber_card c T f
  have hfiber : ∑ g ∈ S, E g = (c : ℝ) ^ Tᶜ.card * E f := by
    calc
      ∑ g ∈ S, E g = ∑ _g ∈ S, E f := by
        apply Finset.sum_congr rfl
        intro g hg
        exact hlocal g f (Finset.mem_filter.mp hg).2
      _ = (S.card : ℝ) * E f := by simp
      _ = (c : ℝ) ^ Tᶜ.card * E f := by rw [hcard, Nat.cast_pow]
  have hsum : (c : ℝ) ^ Tᶜ.card * E f ≤ ∑ g, E g := by
    rw [← hfiber]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun g _ _ => hE g)
  have hcR : 0 < (c : ℝ) := Nat.cast_pos.mpr hc
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hcR _)).mpr
  calc
    E f * (c : ℝ) ^ Fintype.card ι =
        (c : ℝ) ^ T.card * ((c : ℝ) ^ Tᶜ.card * E f) := by
      rw [← Finset.card_add_card_compl T, pow_add]
      ring
    _ ≤ (c : ℝ) ^ T.card * ∑ g, E g :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hcR.le _)

theorem coherent_color_fullDiscrepancy_transfer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ) (hc : 0 < c) (Q : Finset ℕ) (T : ℕ → Finset ι) (J : ℕ)
    (u : ℕ →₀ ℂ) (a : (ι → Fin c) → ℕ)
    (hlocal : ∀ q ∈ Q, ∀ f g : ι → Fin c,
      (∀ i ∈ T q, f i = g i) → a f % q = a g % q)
    (f : ℕ → ι → Fin c) :
    (∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
      ‖fullDiscrepancy u q (a (f q))‖) ≤
      ((c : ℝ) ^ Fintype.card ι)⁻¹ *
        ∑ g : ι → Fin c, ∑ q ∈ Q,
          (q.divisors.card : ℝ) ^ J * (c : ℝ) ^ (T q).card *
            ‖fullDiscrepancy u q (a g)‖ := by
  classical
  have hprojection (q : ℕ) (hq : q ∈ Q) :
      ‖fullDiscrepancy u q (a (f q))‖ ≤
        (c : ℝ) ^ (T q).card / (c : ℝ) ^ Fintype.card ι *
          ∑ g : ι → Fin c, ‖fullDiscrepancy u q (a g)‖ := by
    apply coherent_color_projection_average c hc (T q)
      (fun g => ‖fullDiscrepancy u q (a g)‖)
      (fun g => norm_nonneg _) _ (f q)
    intro g g' hgg'
    simp only [fullDiscrepancy,
      progressionMass, hlocal q hq g g' hgg']
  calc
    (∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy u q (a (f q))‖) ≤
        ∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
          ((c : ℝ) ^ (T q).card / (c : ℝ) ^ Fintype.card ι *
            ∑ g : ι → Fin c, ‖fullDiscrepancy u q (a g)‖) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hprojection q hq)
        (pow_nonneg (Nat.cast_nonneg _) _)
    _ = ((c : ℝ) ^ Fintype.card ι)⁻¹ *
        ∑ g : ι → Fin c, ∑ q ∈ Q,
          (q.divisors.card : ℝ) ^ J * (c : ℝ) ^ (T q).card *
            ‖fullDiscrepancy u q (a g)‖ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem selberg_prime_face_residue_choice {k : ℕ}
    (h : Fin (k + 1) → ℕ) (i : Fin (k + 1)) (d e : Fin k → ℕ) (b : ℕ)
    (hd : ∀ j : Fin k, d j ∣ b + h (i.succAbove j))
    (he : ∀ j : Fin k, e j ∣ b + h (i.succAbove j))
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ ∏ j : Fin k, Nat.lcm (d j) (e j)) :
    ∃ j : Fin k, ((b + h i : ℕ) : ZMod p) =
      (h i : ZMod p) - (h (i.succAbove j) : ZMod p) := by
  classical
  obtain ⟨j, _, hpj⟩ :=
    (hp.prime.dvd_finsetProd_iff (fun j : Fin k => Nat.lcm (d j) (e j))).mp hpm
  have hzero : (b : ZMod p) + (h (i.succAbove j) : ZMod p) = 0 := by
    simpa only [Nat.cast_add] using
      (ZMod.natCast_eq_zero_iff (b + h (i.succAbove j)) p).mpr
        (hpj.trans (Nat.lcm_dvd (hd j) (he j)))
  refine ⟨j, ?_⟩
  push_cast
  linear_combination hzero

theorem selberg_prime_face_residue_alphabet {k : ℕ}
    (h : Fin (k + 1) → ℕ) (hinj : Function.Injective h) (i : Fin (k + 1))
    (W : ℕ)
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (p : ℕ) (hp : p.Prime) (hpW : ¬ p ∣ W) :
    (∀ j : Fin k, (h i : ZMod p) - (h (i.succAbove j) : ZMod p) ≠ 0) ∧
      Function.Injective
        (fun j : Fin k => (h i : ZMod p) - (h (i.succAbove j) : ZMod p)) := by
  have hmodinj : Function.Injective (fun j : Fin (k + 1) => (h j : ZMod p)) := by
    intro a b hab
    apply hinj
    by_contra hne
    apply hpW
    apply hcover a b hne p hp
    have hmod := (ZMod.natCast_eq_natCast_iff (h a) (h b) p).mp hab
    rcases le_total (h a) (h b) with hle | hle
    · simpa only [Nat.dist_eq_sub_of_le hle] using hmod.dvd'
    · simpa only [Nat.dist_eq_sub_of_le_right hle] using hmod.symm.dvd'
  constructor
  · intro j hj
    exact (Fin.ne_succAbove i j) (hmodinj (sub_eq_zero.mp hj))
  · intro j l hjl
    apply (i.succAboveEmb).injective
    apply hmodinj
    exact sub_right_injective hjl

theorem coherent_prime_color_crt (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : ℕ) (r : (p : P) → Fin c → ZMod (p : ℕ))
    (hr : ∀ (p : P) (j : Fin c), r p j ≠ 0) :
    ∃ a : (P → Fin c) → ℕ,
      (∀ f, a f < ∏ p ∈ P, p) ∧
      (∀ (f : P → Fin c) (p : P), (a f : ZMod (p : ℕ)) = r p (f p)) ∧
      (∀ q : ℕ, Squarefree q → q.primeFactors ⊆ P →
        ∀ f : P → Fin c, Nat.Coprime (a f) q) ∧
      (∀ q : ℕ, Squarefree q → q.primeFactors ⊆ P →
        ∀ f g : P → Fin c,
          (∀ p : P, (p : ℕ) ∈ q.primeFactors → r p (f p) = r p (g p)) →
          a f % q = a g % q) := by
  classical
  have hnz (p : P) (_hp : p ∈ (Finset.univ : Finset P)) : (p : ℕ) ≠ 0 :=
    (hP p p.property).ne_zero
  have hpair : Set.Pairwise (↑(Finset.univ : Finset P) : Set P)
      (fun p q => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p _ q _ hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  let a : (P → Fin c) → ℕ := fun f =>
    (Nat.chineseRemainderOfFinset (fun p : P => (r p (f p)).val)
      (fun p : P => (p : ℕ)) Finset.univ hnz hpair).val
  have hbound (f : P → Fin c) : a f < ∏ p ∈ P, p := by
    rw [← Finset.prod_coe_sort P (fun p : ℕ => p)]
    exact
      Nat.chineseRemainderOfFinset_lt_prod (fun p : P => (r p (f p)).val)
        (fun p : P => (p : ℕ)) hnz hpair
  have hres (f : P → Fin c) (p : P) : (a f : ZMod (p : ℕ)) = r p (f p) := by
    let : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
    have hclass : Nat.ModEq (p : ℕ) (a f) (r p (f p)).val :=
      (Nat.chineseRemainderOfFinset (fun p : P => (r p (f p)).val)
        (fun p : P => (p : ℕ)) Finset.univ hnz hpair).property p (Finset.mem_univ p)
    calc
      (a f : ZMod (p : ℕ)) = ((r p (f p)).val : ZMod (p : ℕ)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hclass
      _ = r p (f p) := ZMod.natCast_zmod_val _
  refine ⟨a, hbound, hres, ?_, ?_⟩
  · intro q hq hqP f
    apply Nat.coprime_of_dvd
    intro p hp hpa hpq
    have hpq' : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne_zero⟩
    let pp : P := ⟨p, hqP hpq'⟩
    have hz : (a f : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (a f) p).mpr hpa
    exact hr pp (f pp) ((hres f pp).symm.trans hz)
  · intro q hq hqP f g hfg
    have hprod : (∏ p : q.primeFactors, (p : ℕ)) = q :=
      (Finset.prod_coe_sort q.primeFactors (fun p : ℕ => p)).trans
        (Nat.prod_primeFactors_of_squarefree hq)
    have hpairq : Pairwise
        (fun p t : q.primeFactors => Nat.Coprime (p : ℕ) (t : ℕ)) := by
      intro p t hpt
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.property)
        (Nat.prime_of_mem_primeFactors t.property)).mpr
          (fun h => hpt (Subtype.ext h))
    have hz : (a f : ZMod (∏ p : q.primeFactors, (p : ℕ))) =
        (a g : ZMod (∏ p : q.primeFactors, (p : ℕ))) := by
      apply (ZMod.prodEquivPi (fun p : q.primeFactors => (p : ℕ)) hpairq).injective
      funext p
      simp only [ZMod.prodEquivPi_apply, map_natCast]
      let pp : P := ⟨p, hqP p.property⟩
      change (a f : ZMod (pp : ℕ)) = (a g : ZMod (pp : ℕ))
      rw [hres f pp, hres g pp, hfg pp p.property]
    have hm : Nat.ModEq (∏ p : q.primeFactors, (p : ℕ)) (a f) (a g) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
    change Nat.ModEq q (a f) (a g)
    simpa only [hprod] using hm

theorem coherent_prime_color_fullDiscrepancy_transfer
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : ℕ) (hc : 0 < c)
    (r : (p : P) → Fin c → ZMod (p : ℕ))
    (hr : ∀ (p : P) (j : Fin c), r p j ≠ 0)
    (U : Finset P) (hfixed : ∀ p : P, p ∉ U → ∀ j l : Fin c, r p j = r p l)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Squarefree q ∧ q.primeFactors ⊆ P)
    (J : ℕ) (u : ℕ →₀ ℂ) :
    ∃ a : (P → Fin c) → ℕ,
      (∀ f, a f < ∏ p ∈ P, p) ∧
      (∀ (f : P → Fin c) (p : P), (a f : ZMod (p : ℕ)) = r p (f p)) ∧
      (∀ q ∈ Q, ∀ f : P → Fin c, Nat.Coprime (a f) q) ∧
      ∀ f : ℕ → P → Fin c,
        (∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy u q (a (f q))‖) ≤
          ((c : ℝ) ^ P.card)⁻¹ *
            ∑ g : P → Fin c, ∑ q ∈ Q,
              (q.divisors.card : ℝ) ^ J *
                (c : ℝ) ^ (U.filter (fun p : P => (p : ℕ) ∈ q.primeFactors)).card *
                ‖fullDiscrepancy u q (a g)‖ := by
  classical
  obtain ⟨a, habound, hres, hcoprime, hlocal⟩ := coherent_prime_color_crt P hP c r hr
  refine ⟨a, habound, hres, ?_, ?_⟩
  · intro q hq f
    exact hcoprime q (hQ q hq).1 (hQ q hq).2 f
  · intro f
    let T : ℕ → Finset P := fun q => U.filter
      (fun p : P => (p : ℕ) ∈ q.primeFactors)
    have hlocalT (q : ℕ) (hq : q ∈ Q) (g g' : P → Fin c)
        (hgg' : ∀ p ∈ T q, g p = g' p) : a g % q = a g' % q := by
      apply hlocal q (hQ q hq).1 (hQ q hq).2 g g'
      intro p hp
      by_cases hpU : p ∈ U
      · exact congrArg (r p) (hgg' p (Finset.mem_filter.mpr ⟨hpU, hp⟩))
      · exact hfixed p hpU (g p) (g' p)
    have hbound := coherent_color_fullDiscrepancy_transfer c hc Q T J u a hlocalT f
    simpa only [T, Fintype.card_coe] using hbound

theorem selberg39_color_representation_loss (q : ℕ) (hq : Squarefree q) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 114) q) *
        38 ^ q.primeFactors.card ≤ q.divisors.card ^ 13 := by
  have hprime (k : ℕ) (p : ℕ) (hp : p.Prime) :
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ k) p) = k := by
    induction k with
    | zero => simp [hp.ne_one]
    | succ k ih =>
      rw [pow_succ, ArithmeticFunction.mul_zeta_apply, hp.divisors]
      have hone : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ k) 1) = 1 :=
        (ArithmeticFunction.isMultiplicative_zeta.pow).1
      simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({p} : Finset ℕ) by
          simpa only [Finset.mem_singleton] using hp.ne_one.symm),
        Finset.sum_singleton, hone, ih]
      omega
  have hpow : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 114) q) =
      114 ^ q.primeFactors.card := by
    rw [← (ArithmeticFunction.isMultiplicative_zeta.pow).prod_primeFactors hq,
      ← Finset.prod_const 114]
    exact Finset.prod_congr rfl fun p hp =>
      hprime 114 p (Nat.prime_of_mem_primeFactors hp)
  rw [hpow, squarefree_card_divisors q hq]
  calc
    114 ^ q.primeFactors.card * 38 ^ q.primeFactors.card =
        (114 * 38) ^ q.primeFactors.card := (mul_pow _ _ _).symm
    _ ≤ (2 ^ 13) ^ q.primeFactors.card :=
      Nat.pow_le_pow_left (by norm_num : 114 * 38 ≤ 2 ^ 13) q.primeFactors.card
    _ = (2 ^ q.primeFactors.card) ^ 13 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 13 q.primeFactors.card]

theorem coherent_actual_residue_fullDiscrepancy_transfer
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : ℕ) (hc : 0 < c)
    (r : (p : P) → Fin c → ZMod (p : ℕ))
    (hr : ∀ (p : P) (j : Fin c), r p j ≠ 0)
    (U : Finset P) (hfixed : ∀ p : P, p ∉ U → ∀ j l : Fin c, r p j = r p l)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Squarefree q ∧ q.primeFactors ⊆ P)
    (J : ℕ) (u : ℕ →₀ ℂ) (b : ℕ → ℕ)
    (hchoices : ∀ q ∈ Q, ∀ p : P, (p : ℕ) ∈ q.primeFactors →
      ∃ j : Fin c, (b q : ZMod (p : ℕ)) = r p j) :
    ∃ a : (P → Fin c) → ℕ,
      (∀ f, a f < ∏ p ∈ P, p) ∧
      (∀ (f : P → Fin c) (p : P), (a f : ZMod (p : ℕ)) = r p (f p)) ∧
      (∀ q ∈ Q, ∀ f : P → Fin c, Nat.Coprime (a f) q) ∧
      (∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy u q (b q)‖) ≤
        ((c : ℝ) ^ P.card)⁻¹ *
          ∑ g : P → Fin c, ∑ q ∈ Q,
            (q.divisors.card : ℝ) ^ J *
              (c : ℝ) ^ (U.filter (fun p : P => (p : ℕ) ∈ q.primeFactors)).card *
              ‖fullDiscrepancy u q (a g)‖ := by
  classical
  obtain ⟨a, habound, hres, hcoprime, htransfer⟩ :=
    coherent_prime_color_fullDiscrepancy_transfer P hP c hc r hr U hfixed Q hQ J u
  let f : ℕ → P → Fin c := fun q p =>
    if hq : q ∈ Q then
      if hp : (p : ℕ) ∈ q.primeFactors then Classical.choose (hchoices q hq p hp)
      else ⟨0, hc⟩
    else ⟨0, hc⟩
  have hf (q : ℕ) (hq : q ∈ Q) (p : P) (hp : (p : ℕ) ∈ q.primeFactors) :
      (b q : ZMod (p : ℕ)) = r p (f q p) := by
    dsimp only [f]
    rw [dite_eq_left hq, dite_eq_left hp]
    exact Classical.choose_spec (hchoices q hq p hp)
  have hmod (q : ℕ) (hq : q ∈ Q) : a (f q) % q = b q % q := by
    have hpair : q.primeFactors.toList.Pairwise Nat.Coprime := by
      apply q.primeFactors.nodup_toList.pairwise_of_forall_ne
      intro p hp t ht hpt
      exact (Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp))
        (Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp ht))).mpr hpt
    have hlist : Nat.ModEq (q.primeFactors.toList.map (fun p : ℕ => p)).prod
        (a (f q)) (b q) := by
      apply (Nat.modEq_list_map_prod_iff (s := fun p : ℕ => p) hpair).mpr
      intro p hp
      have hpq : p ∈ q.primeFactors := Finset.mem_toList.mp hp
      let pp : P := ⟨p, (hQ q hq).2 hpq⟩
      apply (ZMod.natCast_eq_natCast_iff (a (f q)) (b q) p).mp
      exact (hres (f q) pp).trans (hf q hq pp hpq).symm
    change Nat.ModEq q (a (f q)) (b q)
    simpa [Finset.prod_toList, Nat.prod_primeFactors_of_squarefree (hQ q hq).1] using hlist
  refine ⟨a, habound, hres, hcoprime, ?_⟩
  calc
    (∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy u q (b q)‖) =
        ∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy u q (a (f q))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [fullDiscrepancy,
        progressionMass, hmod q hq]
    _ ≤ ((c : ℝ) ^ P.card)⁻¹ *
          ∑ g : P → Fin c, ∑ q ∈ Q,
            (q.divisors.card : ℝ) ^ J *
              (c : ℝ) ^ (U.filter (fun p : P => (p : ℕ) ∈ q.primeFactors)).card *
              ‖fullDiscrepancy u q (a g)‖ := htransfer f

section
open scoped ContDiff

theorem selberg_auxiliary_unit_diagonal
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (B : ℝ) (hB : 0 < B) :
    let q : ℕ := ∏ p ∈ P, p
    let u : (Fin 1 → ℕ) →₀ ℝ :=
      ∑ s ∈ q.divisors, Finsupp.single (fun _ : Fin 1 => s) (1 / B)
    let Du := u.support.biUnion
      (fun r => Fintype.piFinset (fun j => (r j).divisors))
    let mass : ℝ := ∑ s ∈ q.divisors, (s.totient : ℝ)⁻¹
    let L : ℕ → ℝ := fun t =>
      ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
    (∀ r : Fin 1 → ℕ, u r = if r 0 ∈ q.divisors then 1 / B else 0) ∧
      u.support = Fintype.piFinset (fun _ : Fin 1 => q.divisors) ∧
      Du = Fintype.piFinset (fun _ : Fin 1 => q.divisors) ∧
      (∀ r : Fin 1 → ℕ, |u r| ≤ 1 / B) ∧
      mass = (q : ℝ) / (q.totient : ℝ) ∧ 0 < mass ∧
      (∑ r ∈ u.support, u r ^ 2 / (∏ j, ((r j).totient : ℝ))) = mass / B ^ 2 ∧
      ∀ t : ℕ, L t = (mass / B) * (if Nat.Coprime t q then 1 else 0) := by
  classical
  intro q u Du mass L
  have hq : Squarefree q := squarefree_prime_prod P hP
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hφpos : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  have hconst (r : Fin 1 → ℕ) : (fun _ : Fin 1 => r 0) = r := by
    funext j
    exact congrArg r (Subsingleton.elim 0 j)
  have hvalue (r : Fin 1 → ℕ) :
      u r = if r 0 ∈ q.divisors then 1 / B else 0 := by
    conv_lhs => rw [← hconst r]
    simp only [u, Finsupp.finsetSum_apply, Finsupp.single_apply]
    have hc (s : ℕ) : ((fun _ : Fin 1 => s) = fun _ : Fin 1 => r 0) ↔ s = r 0 :=
      Function.const_inj
    simp only [hc, Finset.sum_ite_eq']
  have hsupport : u.support = Fintype.piFinset (fun _ : Fin 1 => q.divisors) := by
    ext r
    rw [Finsupp.mem_support_iff, Fintype.mem_piFinset]
    simp only [Fin.forall_fin_one, hvalue]
    by_cases hr : r 0 ∈ q.divisors <;> simp [hr, hB.ne']
  have hDu : Du = Fintype.piFinset (fun _ : Fin 1 => q.divisors) := by
    ext e
    change e ∈ u.support.biUnion _ ↔ _
    rw [Finset.mem_biUnion, hsupport]
    constructor
    · rintro ⟨r, hr, he⟩
      apply Fintype.mem_piFinset.mpr
      intro j
      exact Nat.mem_divisors.mpr ⟨
        (Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp he j)).trans
          (Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hr j)), hq0⟩
    · intro he
      refine ⟨fun _ : Fin 1 => q, ?_, he⟩
      exact Fintype.mem_piFinset.mpr fun _ => Nat.mem_divisors_self q hq0
  have huBound (r : Fin 1 → ℕ) : |u r| ≤ 1 / B := by
    rw [hvalue]
    split_ifs
    · exact le_of_eq (abs_of_pos (one_div_pos.mpr hB))
    · simpa only [abs_zero] using (one_div_pos.mpr hB).le
  have hsum (f : (Fin 1 → ℕ) → ℝ) :
      (∑ r ∈ Fintype.piFinset (fun _ : Fin 1 => q.divisors), f r) =
        ∑ s ∈ q.divisors, f (fun _ : Fin 1 => s) := by
    apply Finset.sum_bij (fun r _ => r 0)
    · intro r hr
      exact Fintype.mem_piFinset.mp hr 0
    · intro r _ s _ hrs
      rw [← hconst r, ← hconst s, hrs]
    · intro s hs
      exact ⟨fun _ : Fin 1 => s, Fintype.mem_piFinset.mpr (fun _ => hs), rfl⟩
    · intro r _
      rw [hconst]
  have hmassProduct : mass = ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) :=
    reciprocal_totient_product P hP
  have hmassratio : mass = (q : ℝ) / (q.totient : ℝ) :=
    (squarefree_div_totient_eq_sum_divisors_inv_totient hq).symm
  have hmasspos : 0 < mass := by rw [hmassratio]; exact div_pos hqpos hφpos
  have huEnergy :
      (∑ r ∈ u.support, u r ^ 2 / (∏ j, ((r j).totient : ℝ))) = mass / B ^ 2 := by
    rw [hsupport, hsum]
    calc
      _ = ∑ s ∈ q.divisors, (s.totient : ℝ)⁻¹ / B ^ 2 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hvalue, ite_eq_left hs, Fin.prod_univ_one]
        simp only [div_eq_mul_inv]
        ring
      _ = mass / B ^ 2 := by rw [Finset.sum_div]
  refine ⟨hvalue, hsupport, hDu, huBound, hmassratio, hmasspos, huEnergy, ?_⟩
  intro t
  let ψ : ℕ → ℝ := fun p =>
    (1 - (p : ℝ) * (if p ∣ t then 1 else 0)) / ((p : ℝ) - 1)
  have huSq : ∀ r ∈ u.support, Squarefree (∏ j, r j) := by
    intro r hr
    have hs : r 0 ∈ q.divisors :=
      Fintype.mem_piFinset.mp (hsupport ▸ hr) 0
    simpa only [Fin.prod_univ_one] using hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hs)
  have hpoint : L t = ∑ r ∈ u.support,
      u r * ∏ p ∈ (r 0).primeFactors, ψ p := by
    simpa only [L, Du, Fin.forall_fin_one, Fin.prod_univ_one, ψ] using
      selberg_pointwise_expansion u (fun _ : Fin 1 => t) huSq
  have hEuler : (∑ s ∈ q.divisors, ∏ p ∈ s.primeFactors, ψ p) =
      ∏ p ∈ P, (1 + ψ p) := by
    have hm := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors ψ) hq
    calc
      _ = ∑ s ∈ q.divisors, ArithmeticFunction.prodPrimeFactors ψ s := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [ArithmeticFunction.prodPrimeFactors_apply (Nat.pos_of_mem_divisors hs).ne']
      _ = ∏ p ∈ P, (1 + ArithmeticFunction.prodPrimeFactors ψ p) := by
        simpa only [q, Nat.primeFactors_prod hP] using hm.symm
      _ = ∏ p ∈ P, (1 + ψ p) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [ArithmeticFunction.prodPrimeFactors_apply (hP p hp).ne_zero,
          (hP p hp).primeFactors, Finset.prod_singleton]
  have hpointProduct : L t = (1 / B) * ∏ p ∈ P, (1 + ψ p) := by
    rw [hpoint, hsupport, hsum]
    calc
      _ = (1 / B) * ∑ s ∈ q.divisors, ∏ p ∈ s.primeFactors, ψ p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [hvalue, ite_eq_left hs]
      _ = _ := by rw [hEuler]
  rw [hpointProduct]
  by_cases hcop : Nat.Coprime t q
  · rw [ite_eq_left hcop, mul_one]
    have hfactor : (∏ p ∈ P, (1 + ψ p)) = mass := by
      rw [hmassProduct]
      apply Finset.prod_congr rfl
      intro p hp
      have hpnot : ¬ p ∣ t :=
        (hP p hp).coprime_iff_not_dvd.mp
          (Nat.Coprime.of_dvd_right (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp) hcop).symm
      simp only [ψ, ite_eq_right hpnot, mul_zero, sub_zero]
    rw [hfactor]
    ring
  · rw [ite_eq_right hcop, mul_zero]
    obtain ⟨p, hp, hpt, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpP : p ∈ P := by
      rw [← Nat.primeFactors_prod hP]
      exact hp.mem_primeFactors hpq hq0
    have hp1 : (p : ℝ) - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
    have hzero : 1 + ψ p = 0 := by
      simp only [ψ, ite_eq_left hpt, mul_one]
      field_simp
      ring
    rw [Finset.prod_eq_zero hpP hzero, mul_zero]

open Classical in
theorem squarefree_coprime_progression_density
    (q m a h : ℕ) (hq : Squarefree q) (hm : m ∣ q)
    (ha : Nat.Coprime (a + h) m) :
    (1 / (q.totient : ℝ)) *
      (∑ n ∈ Finset.range q,
        if Nat.ModEq m n a ∧ Nat.Coprime (n + h) q then (1 : ℝ) else 0) =
      1 / (m.totient : ℝ) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hq0
  let : NeZero q := ⟨hq.ne_zero⟩
  have haM : (a + h) % m ∈ primitiveResidues m :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm0), (ZMod.coprime_mod_iff_coprime (a + h) m).mpr ha⟩
  have hbaseC :
      (∑ n ∈ Finset.range q,
        if Nat.ModEq m n (a + h) ∧ Nat.Coprime n q then (1 : ℂ) else 0) /
          (q.totient : ℂ) = 1 / (m.totient : ℂ) := by
    have hsum :
        (∑ n ∈ Finset.range q,
          if Nat.ModEq m n (a + h) ∧ Nat.Coprime n q then (1 : ℂ) else 0) =
          ∑ n ∈ primitiveResidues q,
            if n % m = (a + h) % m then (1 : ℂ) else 0 := by
      rw [primitiveResidues, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hc : Nat.Coprime n q <;> by_cases hr : n % m = (a + h) % m <;>
        simp [Nat.ModEq, hc, hr]
    rw [hsum]
    have havg := average_primitiveResidues_mod hq0 hm
      (fun b : ℕ => if b = (a + h) % m then (1 : ℂ) else 0)
    simpa [haM] using havg
  have hbaseR :
      (∑ n ∈ Finset.range q,
        if Nat.ModEq m n (a + h) ∧ Nat.Coprime n q then (1 : ℝ) else 0) /
          (q.totient : ℝ) = 1 / (m.totient : ℝ) := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using hbaseC
  have hsumrange (G : ℕ → ℝ) :
      (∑ n ∈ Finset.range q, G n) = ∑ z : ZMod q, G z.val := by
    cases q with
    | zero => omega
    | succ q => exact (Fin.sum_univ_eq_sum_range G (q + 1)).symm
  have hrotate (G : ℕ → ℝ) :
      (∑ n ∈ Finset.range q, G ((n + h) % q)) = ∑ n ∈ Finset.range q, G n := by
    rw [hsumrange, hsumrange]
    calc
      (∑ z : ZMod q, G ((z.val + h) % q)) =
          ∑ z : ZMod q, G (z + (h : ZMod q)).val := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [ZMod.val_add, ZMod.val_natCast, Nat.add_mod]
      _ = ∑ z : ZMod q, G z.val :=
        Equiv.sum_comp (Equiv.addRight (h : ZMod q)) (fun z : ZMod q => G z.val)
  have hmod (n : ℕ) :
      Nat.ModEq m ((n + h) % q) (a + h) ↔ Nat.ModEq m n a := by
    change ((n + h) % q) % m = (a + h) % m ↔ n % m = a % m
    rw [Nat.mod_mod_of_dvd (n + h) hm]
    exact Nat.ModEq.add_iff_right (Nat.ModEq.refl h)
  let G : ℕ → ℝ := fun n =>
    if Nat.ModEq m n (a + h) ∧ Nat.Coprime n q then 1 else 0
  have hshift :
      (∑ n ∈ Finset.range q,
        if Nat.ModEq m n a ∧ Nat.Coprime (n + h) q then (1 : ℝ) else 0) =
        ∑ n ∈ Finset.range q, G n := by
    calc
      _ = ∑ n ∈ Finset.range q, G ((n + h) % q) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [G, hmod n, ZMod.coprime_mod_iff_coprime]
      _ = ∑ n ∈ Finset.range q, G n := hrotate G
  rw [hshift]
  simpa only [G, one_div, div_eq_mul_inv, mul_comm, mul_one] using hbaseR

theorem selberg_retained_pair_modEq_iff {k : ℕ}
    (h : Fin k → ℕ) (d e : Fin k → ℕ)
    (hd : Squarefree (∏ j, d j)) (he : Squarefree (∏ j, e j))
    (hcross : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b))
    (c : ℕ) (hcd : ∀ j, d j ∣ c + h j) (hce : ∀ j, e j ∣ c + h j)
    (n : ℕ) :
    Nat.ModEq (∏ j, Nat.lcm (d j) (e j)) n c ↔
      (∀ j, d j ∣ n + h j) ∧ (∀ j, e j ∣ n + h j) := by
  classical
  let l := (Finset.univ : Finset (Fin k)).toList
  have hpairs := actual_modulus_pairwise_coprime_lcm d e hd he hcross
  have hpair : l.Pairwise
      (fun a b => Nat.Coprime (Nat.lcm (d a) (e a)) (Nat.lcm (d b) (e b))) := by
    apply (Finset.nodup_toList (Finset.univ : Finset (Fin k))).pairwise_of_forall_ne
    intro a ha b hb hab
    exact hpairs (Finset.mem_univ a) (Finset.mem_univ b) hab
  have hprod : (l.map (fun j => Nat.lcm (d j) (e j))).prod =
      ∏ j, Nat.lcm (d j) (e j) := by simp [l]
  have hcomponent (j : Fin k) :
      Nat.ModEq (Nat.lcm (d j) (e j)) n c ↔
        d j ∣ n + h j ∧ e j ∣ n + h j := by
    have hc0 : Nat.ModEq (Nat.lcm (d j) (e j)) (c + h j) 0 :=
      Nat.modEq_zero_iff_dvd.mpr (Nat.lcm_dvd (hcd j) (hce j))
    constructor
    · intro hn
      exact Nat.lcm_dvd_iff.mp
        (Nat.modEq_zero_iff_dvd.mp ((hn.add_right (h j)).trans hc0))
    · rintro ⟨hdn, hen⟩
      exact Nat.ModEq.add_right_cancel' (h j)
        ((Nat.modEq_zero_iff_dvd.mpr (Nat.lcm_dvd hdn hen)).trans hc0.symm)
  rw [← hprod, Nat.modEq_list_map_prod_iff hpair]
  simp only [l, Finset.mem_toList, Finset.mem_univ, forall_const, hcomponent, forall_and]

theorem selberg_prime_pair_density {k : ℕ}
    (h : Fin (k + 1) → ℕ) (hinj : Function.Injective h) (i : Fin (k + 1))
    (d e : Fin k → ℕ) (W v : ℕ) (hW : 0 < W)
    (hd : Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W)
    (he : Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W)
    (hcross : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b))
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (hv : Nat.Coprime (v + h i) W)
    (q : ℕ) (hq : Squarefree q) (hdq : (∏ j, d j) ∣ q) (heq : (∏ j, e j) ∣ q) :
    (1 / (q.totient : ℝ)) *
      (∑ n ∈ Finset.range q,
        if (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
          (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) ∧
          Nat.Coprime (n + h i) q then (1 : ℝ) else 0) =
      1 / (∏ j : Fin k, (Nat.totient (Nat.lcm (d j) (e j)) : ℝ)) := by
  classical
  have hdInsert : Squarefree (∏ j, i.insertNth (α := fun _ => ℕ) 1 d j) ∧
      Nat.Coprime (∏ j, i.insertNth (α := fun _ => ℕ) 1 d j) W := by
    simpa only [Fin.prod_insertNth, one_mul] using hd
  have hcrossInsert : ∀ a b : Fin k, a ≠ b →
      Nat.Coprime (i.insertNth (α := fun _ => ℕ) 1 d (i.succAbove a)) (e b) := by
    simpa only [Fin.insertNth_apply_succAbove] using hcross
  have hcrt := mixedPair_crt h hinj i
    (i.insertNth (α := fun _ => ℕ) 1 d) e W v hW
    hdInsert he hcrossInsert hcover hv
  simp only [Fin.insertNth_apply_succAbove] at hcrt
  obtain ⟨c, _, _, hcprimitive, hcclass⟩ := hcrt
  have hcdiv := (hcclass c).mp (Nat.ModEq.refl c)
  let m : ℕ := ∏ j : Fin k, Nat.lcm (d j) (e j)
  have hpure (n : ℕ) : Nat.ModEq m n c ↔
      (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
      (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) :=
    selberg_retained_pair_modEq_iff (fun j => h (i.succAbove j)) d e hd.1 he.1
      hcross c hcdiv.2.1 hcdiv.2.2 n
  have hdOne : Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) 1 := ⟨hd.1, by simp⟩
  have heOne : Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) 1 := ⟨he.1, by simp⟩
  have hmEq : m = Nat.lcm (∏ j, d j) (∏ j, e j) := by
    simpa only [Nat.lcm_one_left, one_mul] using
      (actual_modulus_eq_product 1 d e hdOne heOne hcross).symm
  have hmq : m ∣ q := by
    rw [hmEq]
    exact Nat.lcm_dvd hdq heq
  have hcm : Nat.Coprime (c + h i) m :=
    hcprimitive.of_dvd_right (dvd_mul_of_dvd_right (dvd_refl m) W)
  have hφ : m.totient = ∏ j : Fin k, Nat.totient (Nat.lcm (d j) (e j)) := by
    rw [hmEq]
    simpa only [Nat.lcm_one_left, Nat.totient_one, one_mul] using
      selberg_actual_modulus_totient_eq 1 (by decide) d e hdOne heOne hcross
  have hφR : (m.totient : ℝ) =
      ∏ j : Fin k, (Nat.totient (Nat.lcm (d j) (e j)) : ℝ) := by
    exact_mod_cast hφ
  calc
    (1 / (q.totient : ℝ)) *
        (∑ n ∈ Finset.range q,
          if (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
            (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) ∧
            Nat.Coprime (n + h i) q then (1 : ℝ) else 0) =
        (1 / (q.totient : ℝ)) *
          (∑ n ∈ Finset.range q,
            if Nat.ModEq m n c ∧ Nat.Coprime (n + h i) q then (1 : ℝ) else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      simp only [hpure n, and_assoc]
    _ = 1 / (m.totient : ℝ) :=
      squarefree_coprime_progression_density q m c (h i) hq hmq hcm
    _ = 1 / (∏ j : Fin k, (Nat.totient (Nat.lcm (d j) (e j)) : ℝ)) := by rw [hφR]

theorem selberg_prime_period_coefficient_identity
    {k : ℕ} (h : Fin (k + 1) → ℕ) (hinj : Function.Injective h)
    (i : Fin (k + 1)) (W v : ℕ) (hW : 0 < W)
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (hv : Nat.Coprime (v + h i) W)
    (q : ℕ) (hq : Squarefree q)
    (D E : Finset (Fin k → ℕ)) (lam mu : (Fin k → ℕ) → ℝ)
    (hD : ∀ d ∈ D,
      Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W ∧ (∏ j, d j) ∣ q)
    (hE : ∀ e ∈ E,
      Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W ∧ (∏ j, e j) ∣ q) :
    (1 / (q.totient : ℝ)) *
      (∑ n ∈ Finset.range q, if Nat.Coprime (n + h i) q then
        (∑ d ∈ D,
          if ∀ j : Fin k, d j ∣ n + h (i.succAbove j) then lam d else 0) *
        (∑ e ∈ E,
          if ∀ j : Fin k, e j ∣ n + h (i.succAbove j) then mu e else 0)
      else 0) =
      ∑ d ∈ D, ∑ e ∈ E,
        if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
          lam d * mu e / (∏ j : Fin k, (Nat.totient (Nat.lcm (d j) (e j)) : ℝ))
        else 0 := by
  classical
  have hexpand :
      (∑ n ∈ Finset.range q, if Nat.Coprime (n + h i) q then
        (∑ d ∈ D,
          if ∀ j : Fin k, d j ∣ n + h (i.succAbove j) then lam d else 0) *
        (∑ e ∈ E,
          if ∀ j : Fin k, e j ∣ n + h (i.succAbove j) then mu e else 0)
      else 0) =
        ∑ d ∈ D, ∑ e ∈ E, (lam d * mu e) *
          ∑ n ∈ Finset.range q,
            if (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
                (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) ∧
                Nat.Coprime (n + h i) q then (1 : ℝ) else 0 := by
    calc
      _ = ∑ n ∈ Finset.range q, ∑ d ∈ D, ∑ e ∈ E,
          (lam d * mu e) *
            (if (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
                (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) ∧
                Nat.Coprime (n + h i) q then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro n _hn
        by_cases hn : Nat.Coprime (n + h i) q
        · rw [ite_eq_left hn, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro d _hd
          apply Finset.sum_congr rfl
          intro e _he
          split_ifs <;> simp_all
        · simp [hn]
      _ = ∑ d ∈ D, ∑ e ∈ E, ∑ n ∈ Finset.range q,
          (lam d * mu e) *
            (if (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
                (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) ∧
                Nat.Coprime (n + h i) q then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _hd
        exact Finset.sum_comm
      _ = _ := by simp_rw [Finset.mul_sum]
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)
  · rw [ite_eq_left hc]
    have hpair := selberg_prime_pair_density h hinj i d e W v hW
      ⟨(hD d hd).1, (hD d hd).2.1⟩ ⟨(hE e he).1, (hE e he).2.1⟩
      hc hcover hv q hq (hD d hd).2.2 (hE e he).2.2
    calc
      _ = (lam d * mu e) * ((1 / (q.totient : ℝ)) *
          ∑ n ∈ Finset.range q,
            if (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
                (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) ∧
                Nat.Coprime (n + h i) q then (1 : ℝ) else 0) := by ring
      _ = (lam d * mu e) *
          (1 / (∏ j : Fin k, (Nat.totient (Nat.lcm (d j) (e j)) : ℝ))) := by
        rw [hpair]
      _ = _ := by ring
  · rw [ite_eq_right hc]
    have hzero : (∑ n ∈ Finset.range q,
        if (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
            (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) ∧
            Nat.Coprime (n + h i) q then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n _hn
      apply ite_eq_right
      intro hconditions
      have hdW : Nat.Coprime (∏ j, i.insertNth (α := fun _ => ℕ) 1 d j) W := by
        simpa only [Fin.prod_insertNth, one_mul] using (hD d hd).2.1
      have hnd : ∀ j : Fin k,
          i.insertNth (α := fun _ => ℕ) 1 d (i.succAbove j) ∣ n + h (i.succAbove j) := by
        simpa only [Fin.insertNth_apply_succAbove] using hconditions.1
      exact hc (by
        simpa only [Fin.insertNth_apply_succAbove] using
          mixedPair_compatible h hinj i
            (i.insertNth (α := fun _ => ℕ) 1 d) e W hdW hcover n
            hnd hconditions.2.1)
    rw [hzero, mul_zero, mul_zero]

end

section
open scoped ContDiff

theorem selberg38_prime_period_comparison
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ M : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      let ρ : ℝ := 2624989 / 10000000
      let h : Fin 39 → ℕ :=
        𝓗.orderEmbOfFin h𝓗_card
      let W := presievingModulus 𝓗 x
      let R := x ^ ρ
      let B := fragmentNormalization W R
      let P := fragmentPrimes W R κ
      let q : ℕ := ∏ p ∈ P, p
      0 < B ∧ ∀ z : (Fin 38 → ℕ) →₀ ℝ,
        (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
        (∀ r, |z r| ≤ M / B ^ 38) →
        let Dz := z.support.biUnion
          (fun r => Fintype.piFinset (fun j => (r j).divisors))
        let C : ℕ → ℝ := fun n =>
          ∑ d ∈ Dz, if ∀ j, d j ∣ n + h (i.succAbove j) then
            selbergCoefficient z d else 0
        |(1 / (q.totient : ℝ)) * (∑ n ∈ Finset.range q,
            if Nat.Coprime (n + h i) q then C n ^ 2 else 0) -
          z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))| ≤ ε / B ^ 38 := by
  classical
  intro ε hε
  let ρ : ℝ := 2624989 / 10000000
  have hρ : 0 < ρ := by norm_num [ρ]
  have hm := harmonic_fragment_normalizer_tendsto 𝓗 ρ κ hρ hκ
  have ht := presieved_prime_square_tail_tendsto 𝓗
  have he : Tendsto (fun x : ℝ => Real.exp (48672 *
      (∑' p : ℕ, if Nat.Prime p ∧ ¬ p ∣ presievingModulus 𝓗 x
        then 1 / (p : ℝ) ^ 2 else 0)) - 1) atTop (nhds 0) := by
    have h := (ht.const_mul (48672 : ℝ)).rexp.sub_const 1
    simpa only [mul_zero, Real.exp_zero, sub_self] using h
  have hsmall : Tendsto (fun x : ℝ =>
      M ^ 2 * (harmonicFragmentMass (presievingModulus 𝓗 x)
          (x ^ ρ) κ / fragmentNormalization (presievingModulus 𝓗 x)
          (x ^ ρ)) ^ 38 *
        (Real.exp (48672 * (∑' p : ℕ,
          if Nat.Prime p ∧ ¬ p ∣ presievingModulus 𝓗 x
          then 1 / (p : ℝ) ^ 2 else 0)) - 1)) atTop (nhds 0) := by
    have h := ((hm.pow 38).mul he).const_mul (M ^ 2)
    simpa only [mul_zero, mul_assoc] using h
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    selberg39_auxiliary_period_comparison
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ M 1 hκ hM zero_le_one 1 zero_lt_one,
    hsmall.eventually_le_const hε] with x hx hcomparison hsmall
  intro ρ' h W R B P q
  have hB : 0 < B := hcomparison.1
  refine ⟨hB, ?_⟩
  intro z hz hzBound Dz C
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  let mass : ℝ := harmonicFragmentMass W R κ
  let tail : ℝ := ∑' p : ℕ,
    if Nat.Prime p ∧ ¬ p ∣ W then 1 / (p : ℝ) ^ 2 else 0
  let u : (Fin 1 → ℕ) →₀ ℝ :=
    ∑ s ∈ q.divisors, Finsupp.single (fun _ : Fin 1 => s) (1 / B)
  let Du := u.support.biUnion
    (fun s => Fintype.piFinset (fun j => (s j).divisors))
  let L : ℕ → ℝ := fun t =>
    ∑ e ∈ Du, if e 0 ∣ t then selbergCoefficient u e else 0
  obtain ⟨_huValue, huSupport, _hDu, huBound, hmassRatio, hmassPos, huEnergy₀, hL⟩ :=
    selberg_auxiliary_unit_diagonal P hP B hB
  change mass = (q : ℝ) / (q.totient : ℝ) at hmassRatio
  change 0 < mass at hmassPos
  change ∀ t : ℕ, L t = (mass / B) * (if Nat.Coprime t q then 1 else 0) at hL
  change (∑ r ∈ u.support, u r ^ 2 / (∏ j, ((r j).totient : ℝ))) =
    mass / B ^ 2 at huEnergy₀
  have huEnergy : u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) = mass / B ^ 2 := by
    simpa only [Finsupp.sum, Fin.prod_univ_one] using huEnergy₀
  have hu : ∀ s ∈ u.support, s 0 ∈ q.divisors := by
    intro s hs
    rw [huSupport] at hs
    exact (Fintype.mem_piFinset.mp hs) 0
  have hraw := (hcomparison.2 u z hu hz huBound hzBound 0).1
  obtain ⟨hq, _hcop, _hroots, _hexpansion, _hK, _hD, _hLperiod, _hCperiod,
      _hbijection, haffine⟩ :=
    selberg39_auxiliary_exact_period_bridge (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ u z hu hz
  have hmean : (1 / (q : ℝ)) *
      (∑ n ∈ Finset.range q, (L (W * n + h i) * C (W * n)) ^ 2) =
      (1 / (q : ℝ)) *
        (∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2) := by
    simpa only [Nat.zero_add] using haffine 0
  let S : ℝ := ∑ n ∈ Finset.range q,
    if Nat.Coprime (n + h i) q then C n ^ 2 else 0
  let H : ℝ := z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))
  let prime : ℝ := (1 / (q.totient : ℝ)) * S
  have hsum : (∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2) =
      (mass / B) ^ 2 * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hL (n + h i)]
    by_cases hc : Nat.Coprime (n + h i) q <;> simp [hc, mul_pow]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hφR : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hshape :
      (1 / (q : ℝ)) * (∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2) -
        u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) * H =
      (mass / B ^ 2) * (prime - H) := by
    rw [hsum, huEnergy]
    change (1 / (q : ℝ)) * ((mass / B) ^ 2 * S) - (mass / B ^ 2) * H =
      (mass / B ^ 2) * ((1 / (q.totient : ℝ)) * S - H)
    rw [hmassRatio]
    field_simp [hqR, hφR, hB.ne']
  have hscale : 0 < mass / B ^ 2 := div_pos hmassPos (pow_pos hB 2)
  have hscaled : (mass / B ^ 2) * |prime - H| ≤
      M ^ 2 / B ^ 78 * mass ^ 39 * (Real.exp (48672 * tail) - 1) := by
    change |(1 / (q : ℝ)) *
      (∑ n ∈ Finset.range q, (L (0 + W * n + h i) * C (0 + W * n)) ^ 2) -
      u.sum (fun s us => us ^ 2 / ((s 0).totient : ℝ)) * H| ≤
      M ^ 2 * 1 ^ 2 / B ^ 78 * mass ^ 39 * (Real.exp (48672 * tail) - 1) at hraw
    simpa only [Nat.zero_add, hmean, hshape, abs_mul, abs_of_pos hscale,
      one_pow, mul_one] using hraw
  change |prime - H| ≤ ε / B ^ 38
  calc
    |prime - H| = ((mass / B ^ 2) * |prime - H|) / (mass / B ^ 2) :=
      (mul_div_cancel_left₀ _ hscale.ne').symm
    _ ≤ (M ^ 2 / B ^ 78 * mass ^ 39 * (Real.exp (48672 * tail) - 1)) /
        (mass / B ^ 2) := div_le_div_of_nonneg_right hscaled hscale.le
    _ = (M ^ 2 * (mass / B) ^ 38 * (Real.exp (48672 * tail) - 1)) / B ^ 38 := by
      field_simp [hmassPos.ne', hB.ne']
    _ ≤ ε / B ^ 38 := div_le_div_of_nonneg_right hsmall (pow_nonneg hB.le _)

open Classical in
theorem selberg38_prime_diagonal_comparison
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ M : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      let ρ : ℝ := 2624989 / 10000000
      let W := presievingModulus 𝓗 x
      let R := x ^ ρ
      let B := fragmentNormalization W R
      let q : ℕ := ∏ p ∈ fragmentPrimes W R κ, p
      0 < B ∧ ∀ z : (Fin 38 → ℕ) →₀ ℝ,
        (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
        (∀ r, |z r| ≤ M / B ^ 38) →
        let D := z.support.biUnion
          (fun r => Fintype.piFinset (fun j => (r j).divisors))
        |(∑ d ∈ D, ∑ e ∈ D,
            if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
              selbergCoefficient z d * selbergCoefficient z e /
                (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0) -
          z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))| ≤ ε / B ^ 38 := by
  intro ε hε
  filter_upwards [selberg38_prime_period_comparison
    (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ M hκ hM ε hε] with x hx
  intro ρ W R B q
  refine ⟨hx.1, ?_⟩
  intro z hz hzBound D
  let h : Fin 39 → ℕ := 𝓗.orderEmbOfFin h𝓗_card
  let P := fragmentPrimes W R κ
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hq : Squarefree q := squarefree_prime_prod P hP
  have hqW : q.Coprime W := by
    apply Nat.Coprime.prod_left
    intro p hp
    exact (hP p hp).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hp).2
  have hW : 0 < W := presieving_pos 𝓗 x
  have hclass (m a : ℕ) (hm : 0 < m) : ∃ v : ℕ, Nat.Coprime (v + a) m := by
    let : NeZero m := ⟨hm.ne'⟩
    let v := (1 - (a : ZMod m)).val
    refine ⟨v, (ZMod.isUnit_iff_coprime (v + a) m).mp ?_⟩
    have hvcast : ((v + a : ℕ) : ZMod m) = 1 := by
      simp only [Nat.cast_add, v, ZMod.natCast_zmod_val]
      ring
    rw [hvcast]
    exact isUnit_one
  obtain ⟨v, hv⟩ := hclass W (h i) hW
  have hinj : Function.Injective h :=
    (𝓗.orderEmbOfFin h𝓗_card).injective
  have hcover : ∀ a b : Fin 39, h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W := by
    intro a b hab p hp hpd
    exact difference_prime_dvd_presieving 𝓗 x
      (𝓗.orderEmbOfFin_mem h𝓗_card a)
      (𝓗.orderEmbOfFin_mem h𝓗_card b) hab hp hpd
  have hD (d : Fin 38 → ℕ) (hd : d ∈ D) :
      Squarefree (∏ j, d j) ∧ (∏ j, d j).Coprime W ∧ (∏ j, d j) ∣ q := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    have hdr' (j : Fin 38) : d j ∣ r j :=
      Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr j)
    have hdq (j : Fin 38) : d j ∣ q :=
      (hdr' j).trans (Nat.dvd_of_mem_divisors ((hz r hr).2 j))
    have hds : Squarefree (∏ j, d j) :=
      (hz r hr).1.squarefree_of_dvd
        (Finset.prod_dvd_prod_of_dvd d r (fun j _ => hdr' j))
    have hdpow : (∏ j : Fin 38, d j) ∣ q ^ 38 := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Finset.prod_dvd_prod_of_dvd (s := Finset.univ) d
          (fun _ : Fin 38 => q) (fun j _ => hdq j)
    have hdprod : (∏ j, d j) ∣ q :=
      hds.isRadical 38 q hdpow
    exact ⟨hds, hqW.of_dvd_left hdprod, hdprod⟩
  have hkernel := selberg_prime_period_coefficient_identity h hinj i W v hW
    hcover hv q hq D D (selbergCoefficient z) (selbergCoefficient z) hD hD
  have hperiod := hx.2 z hz hzBound
  have hrewrite :
      (1 / (q.totient : ℝ)) * (∑ n ∈ Finset.range q,
        if Nat.Coprime (n + h i) q then
          (∑ d ∈ D, if ∀ j, d j ∣ n + h (i.succAbove j) then
            selbergCoefficient z d else 0) ^ 2 else 0) =
      ∑ d ∈ D, ∑ e ∈ D,
        if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
          selbergCoefficient z d * selbergCoefficient z e /
            (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0 := by
    simpa only [pow_two] using hkernel
  change |(1 / (q.totient : ℝ)) * (∑ n ∈ Finset.range q,
      if Nat.Coprime (n + h i) q then
        (∑ d ∈ D, if ∀ j, d j ∣ n + h (i.succAbove j) then
          selbergCoefficient z d else 0) ^ 2 else 0) -
      z.sum (fun r zr => zr ^ 2 / (∏ j, ((r j).totient : ℝ)))| ≤
    ε / B ^ 38 at hperiod
  rw [hrewrite] at hperiod
  exact hperiod

theorem selberg38_prime_bilinear_comparison
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ M M' : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      let ρ : ℝ := 2624989 / 10000000
      let W := presievingModulus 𝓗 x
      let R := x ^ ρ
      let B := fragmentNormalization W R
      let q : ℕ := ∏ p ∈ fragmentPrimes W R κ, p
      0 < B ∧ ∀ z z' : (Fin 38 → ℕ) →₀ ℝ,
        (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
        (∀ r ∈ z'.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
        (∀ r, |z r| ≤ M / B ^ 38) → (∀ r, |z' r| ≤ M' / B ^ 38) →
        let D := z.support.biUnion
          (fun r => Fintype.piFinset (fun j => (r j).divisors))
        let E := z'.support.biUnion
          (fun r => Fintype.piFinset (fun j => (r j).divisors))
        |(∑ d ∈ D, ∑ e ∈ E,
            if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
              selbergCoefficient z d * selbergCoefficient z' e /
                (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0) -
          z.sum (fun r zr => zr * z' r / (∏ j, ((r j).totient : ℝ)))| ≤
            ε / B ^ 38 := by
  classical
  intro ε hε
  filter_upwards [selberg38_prime_period_comparison (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ (M + M') hκ
    (add_nonneg hM hM') (2 * ε) (mul_pos (by norm_num) hε)] with x hx
  intro ρ W R B q
  refine ⟨hx.1, ?_⟩
  intro z z' hz hz' hzBound hzBound' D E
  let h : Fin 39 → ℕ := 𝓗.orderEmbOfFin h𝓗_card
  let K := z.support ∪ z'.support
  let roots : ((Fin 38 → ℕ) →₀ ℝ) → Finset (Fin 38 → ℕ) := fun w =>
    w.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors))
  let C : ((Fin 38 → ℕ) →₀ ℝ) → ℕ → ℝ := fun w n =>
    ∑ d ∈ roots w, if ∀ j, d j ∣ n + h (i.succAbove j) then
      selbergCoefficient w d else 0
  let H : ((Fin 38 → ℕ) →₀ ℝ) → ℝ := fun w =>
    w.sum (fun r wr => wr ^ 2 / (∏ j, ((r j).totient : ℝ)))
  let Q : ((Fin 38 → ℕ) →₀ ℝ) → ℝ := fun w =>
    (1 / (q.totient : ℝ)) * (∑ n ∈ Finset.range q,
      if Nat.Coprime (n + h i) q then C w n ^ 2 else 0)
  let Hcross : ℝ := z.sum (fun r zr => zr * z' r / (∏ j, ((r j).totient : ℝ)))
  let Qcross : ℝ := (1 / (q.totient : ℝ)) * (∑ n ∈ Finset.range q,
    if Nat.Coprime (n + h i) q then C z n * C z' n else 0)
  have hsupport (w : (Fin 38 → ℕ) →₀ ℝ) (hw : w.support ⊆ K) :
      ∀ r ∈ w.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors := by
    intro r hr
    rcases Finset.mem_union.mp (hw hr) with hr | hr
    · exact hz r hr
    · exact hz' r hr
  have hplusBound (r : Fin 38 → ℕ) : |(z + z') r| ≤ (M + M') / B ^ 38 := by
    calc
      |(z + z') r| ≤ |z r| + |z' r| := abs_add_le _ _
      _ ≤ M / B ^ 38 + M' / B ^ 38 := add_le_add (hzBound r) (hzBound' r)
      _ = (M + M') / B ^ 38 := (add_div _ _ _).symm
  have hminusBound (r : Fin 38 → ℕ) : |(z - z') r| ≤ (M + M') / B ^ 38 := by
    calc
      |(z - z') r| ≤ |z r| + |z' r| := by
        simpa only [Real.norm_eq_abs, Finsupp.sub_apply] using norm_sub_le (z r) (z' r)
      _ ≤ M / B ^ 38 + M' / B ^ 38 := add_le_add (hzBound r) (hzBound' r)
      _ = (M + M') / B ^ 38 := (add_div _ _ _).symm
  have hplus : |Q (z + z') - H (z + z')| ≤ (2 * ε) / B ^ 38 :=
    hx.2 (z + z') (hsupport _ Finsupp.support_add) hplusBound
  have hminus : |Q (z - z') - H (z - z')| ≤ (2 * ε) / B ^ 38 :=
    hx.2 (z - z') (hsupport _ Finsupp.support_sub) hminusBound
  have hrootsEq (e : DecidableEq (Fin 38)) (w : (Fin 38 → ℕ) →₀ ℝ) :
      w.support.biUnion (fun r => @Fintype.piFinset (Fin 38) e inferInstance
        (fun _ => ℕ) (fun j => (r j).divisors)) = roots w := by
    ext d
    simp only [roots, Finset.mem_biUnion, Fintype.mem_piFinset]
  have hCplus (n : ℕ) : C (z + z') n = C z n + C z' n := by
    convert selberg_divisor_root_finset_combination (Finset.univ : Finset (Fin 2))
      (fun _ => (1 : ℝ)) ![z, z'] (fun j => n + h (i.succAbove j)) using 1 <;>
      simp only [Fin.sum_univ_two, C, hrootsEq, one_mul, one_smul, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> rfl
  have hCminus (n : ℕ) : C (z - z') n = C z n - C z' n := by
    convert selberg_divisor_root_finset_combination (Finset.univ : Finset (Fin 2))
      ![(1 : ℝ), -1] ![z, z'] (fun j => n + h (i.succAbove j)) using 1 <;>
      simp only [Fin.sum_univ_two, C, hrootsEq, sub_eq_add_neg, one_mul, one_smul,
        neg_one_smul, neg_mul, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> rfl
  have hH (w : (Fin 38 → ℕ) →₀ ℝ) (hw : w.support ⊆ K) :
      H w = ∑ r ∈ K, (w r) ^ 2 / (∏ j, ((r j).totient : ℝ)) := by
    exact w.sum_of_support_subset hw _ (by intro r hr; simp)
  have hHcross : Hcross =
      ∑ r ∈ K, z r * z' r / (∏ j, ((r j).totient : ℝ)) := by
    exact z.sum_of_support_subset Finset.subset_union_left _ (by intro r hr; simp)
  have hHpolar : H (z + z') - H (z - z') = 4 * Hcross := by
    rw [hH (z + z') Finsupp.support_add, hH (z - z') Finsupp.support_sub, hHcross,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    ring
  have hQpolar : Q (z + z') - Q (z - z') = 4 * Qcross := by
    calc
      _ = (1 / (q.totient : ℝ)) * (∑ n ∈ Finset.range q,
          ((if Nat.Coprime (n + h i) q then C (z + z') n ^ 2 else 0) -
          (if Nat.Coprime (n + h i) q then C (z - z') n ^ 2 else 0))) := by
        simp only [Q, Finset.sum_sub_distrib, mul_sub]
      _ = (1 / (q.totient : ℝ)) * (∑ n ∈ Finset.range q,
          4 * (if Nat.Coprime (n + h i) q then C z n * C z' n else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [hCplus, hCminus]
        split_ifs <;> ring
      _ = 4 * Qcross := by
        rw [← Finset.mul_sum]
        dsimp only [Qcross]
        ring
  have hpolar : 4 * (Qcross - Hcross) =
      (Q (z + z') - H (z + z')) - (Q (z - z') - H (z - z')) := by
    linarith [hQpolar, hHpolar]
  have herror : |4 * (Qcross - Hcross)| ≤ (2 * ε) / B ^ 38 + (2 * ε) / B ^ 38 := by
    rw [hpolar]
    calc
      _ ≤ |Q (z + z') - H (z + z')| + |Q (z - z') - H (z - z')| := by
        simpa only [Real.norm_eq_abs] using
          norm_sub_le (Q (z + z') - H (z + z')) (Q (z - z') - H (z - z'))
      _ ≤ _ := add_le_add hplus hminus
  have hscale : (2 * ε) / B ^ 38 + (2 * ε) / B ^ 38 = 4 * (ε / B ^ 38) := by ring
  rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num, hscale] at herror
  have hcross : |Qcross - Hcross| ≤ ε / B ^ 38 := by linarith
  let P := fragmentPrimes W R κ
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hq : Squarefree q := squarefree_prime_prod P hP
  have hqW : q.Coprime W := by
    apply Nat.Coprime.prod_left
    intro p hp
    exact (hP p hp).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hp).2
  have hW : 0 < W := presieving_pos 𝓗 x
  have hclass (m a : ℕ) (hm : 0 < m) : ∃ v : ℕ, Nat.Coprime (v + a) m := by
    let : NeZero m := ⟨hm.ne'⟩
    let v := (1 - (a : ZMod m)).val
    refine ⟨v, (ZMod.isUnit_iff_coprime (v + a) m).mp ?_⟩
    have hvcast : ((v + a : ℕ) : ZMod m) = 1 := by
      simp only [Nat.cast_add, v, ZMod.natCast_zmod_val]
      ring
    rw [hvcast]
    exact isUnit_one
  obtain ⟨v, hv⟩ := hclass W (h i) hW
  have hinj : Function.Injective h :=
    (𝓗.orderEmbOfFin h𝓗_card).injective
  have hcover : ∀ a b : Fin 39, h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W := by
    intro a b hab p hp hpd
    exact difference_prime_dvd_presieving 𝓗 x
      (𝓗.orderEmbOfFin_mem h𝓗_card a)
      (𝓗.orderEmbOfFin_mem h𝓗_card b) hab hp hpd
  have hroots (w : (Fin 38 → ℕ) →₀ ℝ)
      (hw : ∀ r ∈ w.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors)
      (d : Fin 38 → ℕ) (hd : d ∈ roots w) :
      Squarefree (∏ j, d j) ∧ (∏ j, d j).Coprime W ∧ (∏ j, d j) ∣ q := by
    obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
    have hdr' (j : Fin 38) : d j ∣ r j :=
      Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr j)
    have hdq (j : Fin 38) : d j ∣ q :=
      (hdr' j).trans (Nat.dvd_of_mem_divisors ((hw r hr).2 j))
    have hds : Squarefree (∏ j, d j) :=
      (hw r hr).1.squarefree_of_dvd
        (Finset.prod_dvd_prod_of_dvd d r (fun j _ => hdr' j))
    have hdpow : (∏ j : Fin 38, d j) ∣ q ^ 38 := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Finset.prod_dvd_prod_of_dvd (s := Finset.univ) d (fun _ : Fin 38 => q) (fun j _ => hdq j)
    have hdprod : (∏ j, d j) ∣ q :=
      hds.isRadical 38 q hdpow
    exact ⟨hds, hqW.of_dvd_left hdprod, hdprod⟩
  have hkernel := selberg_prime_period_coefficient_identity h hinj i W v hW
    hcover hv q hq D E (selbergCoefficient z) (selbergCoefficient z')
      (hroots z hz) (hroots z' hz')
  dsimp only [Qcross, C, roots] at hcross
  rw [hkernel] at hcross
  exact hcross

open Classical in
theorem canonical39_erased_prime_bilinear_tendsto
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    {m : ℕ} (i : Fin 39) (κ : ℝ) (hκ : 0 < κ)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = κ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hF : Measurable F) (hF' : Measurable F')
    (hbF : Bornology.IsBounded (Set.range F))
    (hbF' : Bornology.IsBounded (Set.range F')) :
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F X) →
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F' X) →
    let ρ : ℝ := 2624989 / 10000000
    let W : ℝ → ℕ := presievingModulus 𝓗
    let R : ℝ → ℝ := fun x => x ^ ρ
    let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) κ, p
    let T40 : ℝ → Finset (Fin 39 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
        (fun r => Squarefree (∏ j, r j))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    let y : ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T40 x, Finsupp.single r (F (fun j => X x (r j)) / B x ^ 39)
    let y' : ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T40 x, Finsupp.single r (F' (fun j => X x (r j)) / B x ^ 39)
    let z : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
      (y x).sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
        (yr / ((r i).totient : ℝ)))
    let z' : ℝ → ((Fin 38 → ℕ) →₀ ℝ) := fun x =>
      (y' x).sum (fun r yr => Finsupp.single (fun j => r (i.succAbove j))
        (yr / ((r i).totient : ℝ)))
    let D : ℝ → Finset (Fin 38 → ℕ) := fun x =>
      (z x).support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors))
    let E : ℝ → Finset (Fin 38 → ℕ) := fun x =>
      (z' x).support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors))
    Tendsto
      (fun x : ℝ => B x ^ 38 * (∑ d ∈ D x, ∑ e ∈ E x,
        if ∀ s t : Fin 38, s ≠ t → Nat.Coprime (d s) (e t) then
          selbergCoefficient (z x) d * selbergCoefficient (z' x) e /
            (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0))
      atTop (nhds (∫ Y : Fin 38 → Fin (m + 1) → ℝ,
        (∫ t : Fin (m + 1) → ℝ, F (i.insertNth t Y) ∂ν) *
          (∫ t : Fin (m + 1) → ℝ, F' (i.insertNth t Y) ∂ν)
        ∂Measure.pi (fun _ : Fin 38 => ν))) := by
  intro ν cF cF' ρ W R B q T40 X y y' z z' D E
  let H : ℝ → ℝ := fun x =>
    (z x).sum (fun r zr => zr * z' x r / (∏ j, ((r j).totient : ℝ)))
  let K : ℝ → ℝ := fun x => ∑ d ∈ D x, ∑ e ∈ E x,
    if ∀ s t : Fin 38, s ≠ t → Nat.Coprime (d s) (e t) then
      selbergCoefficient (z x) d * selbergCoefficient (z' x) e /
        (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0
  let L : ℝ := ∫ Y : Fin 38 → Fin (m + 1) → ℝ,
    (∫ t : Fin (m + 1) → ℝ, F (i.insertNth t Y) ∂ν) *
      (∫ t : Fin (m + 1) → ℝ, F' (i.insertNth t Y) ∂ν)
    ∂Measure.pi (fun _ : Fin 38 => ν)
  have hlim : Tendsto (fun x => B x ^ 38 * H x) atTop (nhds L) := by
    let G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ := fun _ => 0
    have hG : Measurable G := measurable_const
    have hbG : Bornology.IsBounded (Set.range G) :=
      Bornology.isBounded_singleton.subset Set.range_const_subset
    have cG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => ν), ContinuousAt G Y :=
      Filter.Eventually.of_forall (fun _ => continuousAt_const)
    have hraw := canonical_and_erased_polarized_harmonic_tendsto (𝓗 := 𝓗)
      i κ hκ a ha ha0 haLast G G F F' hG hG hF hF' hbG hbG hbF hbF'
        cG cG cF cF'
    simpa only [G, zero_div, Finsupp.single_zero, Finset.sum_const_zero, zero_add]
      using hraw
  obtain ⟨MF, hMF, hFb⟩ := hbF.exists_pos_norm_le
  obtain ⟨MF', hMF', hFb'⟩ := hbF'.exists_pos_norm_le
  simp only [Real.norm_eq_abs] at hFb hFb'
  let Cκ : ℝ := Real.exp Real.eulerMascheroniConstant * κ + 1
  have hCκ : 0 < Cκ := by dsimp only [Cκ]; positivity
  have herror : Tendsto (fun x => B x ^ 38 * (K x - H x)) atTop (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards
      [selberg39_canonical_erased_face (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ MF hκ hMF.le,
        selberg39_canonical_erased_face (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ MF' hκ hMF'.le,
        selberg38_prime_bilinear_comparison
          (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ (MF * Cκ) (MF' * Cκ) hκ
          (mul_nonneg hMF.le hCκ.le) (mul_nonneg hMF'.le hCκ.le)
          (ε / 2) (half_pos hε)] with x hx hx' hc
    obtain ⟨_, _, hface⟩ := hx
    obtain ⟨_, _, hface'⟩ := hx'
    obtain ⟨_, _, _, _, hzsupport, hzbound⟩ :=
      hface (fun Y => F (fun j => fragmentBandMasses a (Y j)))
        (fun Y => hFb _ ⟨fun j => fragmentBandMasses a (Y j), rfl⟩)
    obtain ⟨_, _, _, _, hzsupport', hzbound'⟩ :=
      hface' (fun Y => F' (fun j => fragmentBandMasses a (Y j)))
        (fun Y => hFb' _ ⟨fun j => fragmentBandMasses a (Y j), rfl⟩)
    have hzs : ∀ r ∈ (z x).support,
        Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ (q x).divisors := by
      intro r hr
      exact ⟨(hzsupport r hr).1, (hzsupport r hr).2.1⟩
    have hzs' : ∀ r ∈ (z' x).support,
        Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ (q x).divisors := by
      intro r hr
      exact ⟨(hzsupport' r hr).1, (hzsupport' r hr).2.1⟩
    have hzb : ∀ r, |z x r| ≤ (MF * Cκ) / B x ^ 38 := fun r => (hzbound r).2
    have hzb' : ∀ r, |z' x r| ≤ (MF' * Cκ) / B x ^ 38 :=
      fun r => (hzbound' r).2
    have hB : 0 < B x := hc.1
    have herr : |K x - H x| ≤ (ε / 2) / B x ^ 38 :=
      hc.2 (z x) (z' x) hzs hzs' hzb hzb'
    have hB39 : 0 < B x ^ 38 := pow_pos hB 38
    have hscaled := mul_le_mul_of_nonneg_left herr hB39.le
    rw [mul_div_cancel₀ _ hB39.ne'] at hscaled
    have hstrict := hscaled.trans_lt (half_lt_self hε)
    simpa only [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hB39] using hstrict
  have hsum := herror.add hlim
  simp only [zero_add] at hsum
  change Tendsto (fun x => B x ^ 38 * K x) atTop (nhds L)
  convert hsum using 1
  funext x
  ring

theorem fragment_band_law_integral_pullback
    {m : ℕ} (κ : ℝ) (a : Fin (m + 2) → ℝ) (d : ℕ)
    (F : (Fin d → Fin (m + 1) → ℝ) → ℝ) (hF : Measurable F) :
    let μ : Measure (FiniteMeasure ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        fragmentLaw κ
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∫ Y, F Y ∂Measure.pi (fun _ : Fin d => ν)) =
      ∫ X, F (fun j => fragmentBandMasses a (X j))
        ∂Measure.pi (fun _ : Fin d => μ) := by
  intro μ ν
  let b : FiniteMeasure ℝ → Fin (m + 1) → ℝ := fragmentBandMasses a
  have hb : Measurable b := measurable_fragmentBandMasses a
  let : IsProbabilityMeasure (fragmentLaw κ) :=
    fragmentLaw_isProbabilityMeasure κ
  let : IsFiniteMeasure μ := Measure.smul_finite
    (fragmentLaw κ) ENNReal.ofReal_ne_top
  have hmap : Measure.map b μ = ν := Measure.map_smul _ hb.aemeasurable
  have hpi : Measure.map (fun X : Fin d → FiniteMeasure ℝ => fun j => b (X j))
      (Measure.pi (fun _ : Fin d => μ)) = Measure.pi (fun _ : Fin d => ν) := by
    simpa only [hmap] using
      (Measure.pi_map_pi (μ := fun _ : Fin d => μ) (f := fun _ => b)
        (fun _ => hb.aemeasurable))
  rw [← hpi]
  exact integral_map_of_stronglyMeasurable
    (measurable_pi_lambda _ fun j => hb.comp (measurable_pi_apply j))
    hF.stronglyMeasurable

theorem fragment_band_law_fiber_function_integral_pullback
    {m : ℕ} (κ : ℝ) (a : Fin (m + 2) → ℝ) (d r : ℕ) (i : Fin (d + 1))
    (F : Fin r → (Fin (d + 1) → Fin (m + 1) → ℝ) → ℝ)
    (hF : ∀ j, Measurable (F j))
    (Ψ : (Fin d → Fin (m + 1) → ℝ) → (Fin r → ℝ) → ℝ)
    (hΨ : Measurable (Function.uncurry Ψ)) :
    let μ : Measure (FiniteMeasure ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        fragmentLaw κ
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∫ Y, Ψ Y (fun j =>
        ∫ t : Fin (m + 1) → ℝ, F j (i.insertNth t Y) ∂ν)
      ∂Measure.pi (fun _ : Fin d => ν)) =
      ∫ X, Ψ (fun k => fragmentBandMasses a (X k)) (fun j =>
        ∫ c : FiniteMeasure ℝ,
          F j (fun k => fragmentBandMasses a
            (i.insertNth (α := fun _ => FiniteMeasure ℝ) c X k)) ∂μ)
        ∂Measure.pi (fun _ : Fin d => μ) := by
  classical
  intro μ ν
  let b : FiniteMeasure ℝ → Fin (m + 1) → ℝ := fragmentBandMasses a
  have hb : Measurable b := measurable_fragmentBandMasses a
  let : IsProbabilityMeasure (fragmentLaw κ) :=
    fragmentLaw_isProbabilityMeasure κ
  let : IsFiniteMeasure μ := Measure.smul_finite
    (fragmentLaw κ) ENNReal.ofReal_ne_top
  have hmap : Measure.map b μ = ν := Measure.map_smul _ hb.aemeasurable
  let : IsFiniteMeasure ν := hmap ▸ Measure.isFiniteMeasure_map μ b
  let U : Fin r → (Fin d → Fin (m + 1) → ℝ) → ℝ := fun j Y =>
    ∫ t : Fin (m + 1) → ℝ, F j (i.insertNth t Y) ∂ν
  have hins : Measurable
      (fun p : (Fin d → Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
        i.insertNth (α := fun _ => Fin (m + 1) → ℝ) p.2 p.1) :=
    (continuous_snd.finInsertNth i continuous_fst).measurable
  have hU (j : Fin r) : Measurable (U j) :=
    ((hF j).comp hins).stronglyMeasurable.integral_prod_right'.measurable
  have houter : Measurable (fun Y => Ψ Y (fun j => U j Y)) :=
    hΨ.comp (measurable_id.prodMk (measurable_pi_lambda _ hU))
  have hfiber (j : Fin r) (X : Fin d → FiniteMeasure ℝ) :
      U j (fun k => b (X k)) =
        ∫ c : FiniteMeasure ℝ,
          F j (fun k => b (i.insertNth (α := fun _ => FiniteMeasure ℝ) c X k)) ∂μ := by
    have hslice : Measurable
        (fun t : Fin (m + 1) → ℝ => F j (i.insertNth t (fun k => b (X k)))) :=
      (hF j).comp (hins.comp (measurable_const.prodMk measurable_id))
    calc
      U j (fun k => b (X k)) =
          ∫ c : FiniteMeasure ℝ, F j (i.insertNth (b c) (fun k => b (X k))) ∂μ := by
        dsimp only [U]
        rw [← hmap]
        exact integral_map_of_stronglyMeasurable hb hslice.stronglyMeasurable
      _ = _ := by
        apply integral_congr_ae
        apply ae_of_all
        intro c
        apply congrArg (F j)
        funext k
        rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
        · simp only [Fin.insertNth_apply_same]
        · simp only [Fin.insertNth_apply_succAbove]
  calc
    _ = ∫ X, Ψ (fun k => b (X k)) (fun j => U j (fun k => b (X k)))
        ∂Measure.pi (fun _ : Fin d => μ) :=
      fragment_band_law_integral_pullback κ a d (fun Y => Ψ Y (fun j => U j Y)) houter
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro X
      apply congrArg (Ψ (fun k => b (X k)))
      funext j
      exact hfiber j X

end

open Classical in
theorem selberg38_coherent_pair_error_le
    (W : ℕ) (hW : 0 < W) (D E : Finset (Fin 38 → ℕ))
    (hD : ∀ d ∈ D, Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W)
    (hE : ∀ e ∈ E, Squarefree (∏ i, e i) ∧ Nat.Coprime (∏ i, e i) W)
    (gate : (Fin 38 → ℕ) → (Fin 38 → ℕ) → Prop) [DecidableRel gate]
    (hcross : ∀ d ∈ D, ∀ e ∈ E, gate d e →
      ∀ i j : Fin 38, i ≠ j → Nat.Coprime (d i) (e j))
    (lam mu : (Fin 38 → ℕ) → ℝ) (B₁ B₂ Err : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hlam : ∀ d ∈ D, |lam d| ≤ B₁) (hmu : ∀ e ∈ E, |mu e| ≤ B₂)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : (p : P) → Fin 38 → ZMod (p : ℕ))
    (hr : ∀ (p : P) (j : Fin 38), r p j ≠ 0)
    (U : Finset P) (hfixed : ∀ p : P, p ∉ U → ∀ j l : Fin 38, r p j = r p l)
    (Q : Finset ℕ) (hQ : Q ⊆ (∏ p ∈ P, p).divisors)
    (u : ℕ →₀ ℂ) (residue : (Fin 38 → ℕ) → (Fin 38 → ℕ) → ℕ)
    (hmoduli : ∀ d ∈ D, ∀ e ∈ E, gate d e →
      Nat.lcm W (Nat.lcm (∏ i, d i) (∏ i, e i)) ∈ Q)
    (hchoices : ∀ d ∈ D, ∀ e ∈ E, gate d e →
      ∀ p : P,
        (p : ℕ) ∈ (Nat.lcm W (Nat.lcm (∏ i, d i) (∏ i, e i))).primeFactors →
        ∃ j : Fin 38, (residue d e : ZMod (p : ℕ)) = r p j)
    (hSource : ∀ a : ℕ, Nat.Coprime a (∏ p ∈ P, p) →
      (∑ q ∈ Q, (q.divisors.card : ℝ) ^ 13 *
        ‖fullDiscrepancy u q a‖) ≤ Err) :
    (∑ p ∈ (D.product E).filter (fun p => gate p.1 p.2),
      |lam p.1| * |mu p.2| *
        ‖fullDiscrepancy u
          (Nat.lcm W (Nat.lcm (∏ i, p.1 i) (∏ i, p.2 i)))
          (residue p.1 p.2)‖) ≤ B₁ * B₂ * Err := by
  let Pair := (Fin 38 → ℕ) × (Fin 38 → ℕ)
  let S : Finset Pair := (D.product E).filter (fun p => gate p.1 p.2)
  let mod : Pair → ℕ := fun p =>
    Nat.lcm W (Nat.lcm (∏ i, p.1 i) (∏ i, p.2 i))
  let err : Pair → ℝ := fun p =>
    ‖fullDiscrepancy u (mod p) (residue p.1 p.2)‖
  let Qa : Finset ℕ := S.image mod
  have hQaQ : Qa ⊆ Q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hpDE, hgate⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpD, hpE⟩ := Finset.mem_product.mp hpDE
    exact hmoduli p.1 hpD p.2 hpE hgate
  have hPsq : Squarefree (∏ p ∈ P, p) := squarefree_prime_prod P hP
  have hQa (q : ℕ) (hq : q ∈ Qa) : Squarefree q ∧ q.primeFactors ⊆ P := by
    have hdiv : q ∣ ∏ p ∈ P, p := (Nat.mem_divisors.mp (hQ (hQaQ hq))).1
    refine ⟨hPsq.squarefree_of_dvd hdiv, ?_⟩
    simpa only [Nat.primeFactors_prod hP] using Nat.primeFactors_mono hdiv hPsq.ne_zero
  have hmax (q : Qa) :
      ∃ p ∈ S.filter (fun p => mod p = (q : ℕ)),
        ∀ p' ∈ S.filter (fun p => mod p = (q : ℕ)), err p' ≤ err p := by
    apply Finset.exists_max_image
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp q.property
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpq⟩⟩
  choose pick hpickMem hpickMax using hmax
  have hpickS (q : Qa) : pick q ∈ S := (Finset.mem_filter.mp (hpickMem q)).1
  have hpickMod (q : Qa) : mod (pick q) = (q : ℕ) :=
    (Finset.mem_filter.mp (hpickMem q)).2
  let b : ℕ → ℕ := fun q =>
    if hq : q ∈ Qa then residue (pick ⟨q, hq⟩).1 (pick ⟨q, hq⟩).2 else 0
  let Delta : ℕ → ℝ := fun q => ‖fullDiscrepancy u q (b q)‖
  have hb (q : Qa) : b q = residue (pick q).1 (pick q).2 := by
    simp only [b, dite_eq_left q.property]
  have hpairMax (p : Pair) (hp : p ∈ S) : err p ≤ Delta (mod p) := by
    let q : Qa := ⟨mod p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hh := hpickMax q p (Finset.mem_filter.mpr ⟨hp, rfl⟩)
    dsimp only [err] at hh
    rw [hpickMod q] at hh
    dsimp only [err, Delta]
    rw [hb q]
    exact hh
  have hbchoices (q : ℕ) (hq : q ∈ Qa) (p : P)
      (hp : (p : ℕ) ∈ q.primeFactors) :
      ∃ j : Fin 38, (b q : ZMod (p : ℕ)) = r p j := by
    let qq : Qa := ⟨q, hq⟩
    obtain ⟨hpDE, hgate⟩ := Finset.mem_filter.mp (hpickS qq)
    obtain ⟨hpD, hpE⟩ := Finset.mem_product.mp hpDE
    have hp' : (p : ℕ) ∈ (mod (pick qq)).primeFactors := by
      simpa only [hpickMod qq] using hp
    rw [hb qq]
    exact hchoices (pick qq).1 hpD (pick qq).2 hpE hgate p hp'
  let w : ℕ → ℝ := fun q =>
    ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 114) q : ℕ) : ℝ)
  have hw (q : ℕ) : 0 ≤ w q := Nat.cast_nonneg _
  have hrepresentation :
      (∑ p ∈ S, |lam p.1| * |mu p.2| * Delta (mod p)) ≤
        B₁ * B₂ * ∑ q ∈ Qa, w q * Delta q := by
    exact selberg_actual_modulus_weighted_error_le
      (k := 38) (by norm_num) W hW D E hD hE gate hcross lam mu B₁ B₂
      hB₁ hB₂ hlam hmu Qa Delta (fun _q _hq => norm_nonneg _) (by
        intro d hd e he hgate
        exact Finset.mem_image.mpr
          ⟨(d, e), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hd, he⟩, hgate⟩, rfl⟩)
  obtain ⟨a, _, hres, hcoprime, hlocal⟩ :=
    coherent_prime_color_crt P hP 38 r hr
  have hacoprime (g : P → Fin 38) : Nat.Coprime (a g) (∏ p ∈ P, p) :=
    hcoprime _ hPsq
      (by simpa only [Nat.primeFactors_prod hP] using (Finset.Subset.refl P)) g
  let f : ℕ → P → Fin 38 := fun q p =>
    if hq : q ∈ Qa then
      if hp : (p : ℕ) ∈ q.primeFactors then Classical.choose (hbchoices q hq p hp)
      else 0
    else 0
  have hf (q : ℕ) (hq : q ∈ Qa) (p : P) (hp : (p : ℕ) ∈ q.primeFactors) :
      (b q : ZMod (p : ℕ)) = r p (f q p) := by
    simpa only [f, dite_eq_left hq, dite_eq_left hp] using
      Classical.choose_spec (hbchoices q hq p hp)
  have hmod (q : ℕ) (hq : q ∈ Qa) : a (f q) % q = b q % q := by
    have hpair : q.primeFactors.toList.Pairwise Nat.Coprime := by
      apply q.primeFactors.nodup_toList.pairwise_of_forall_ne
      intro p hp t ht hpt
      exact (Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp))
        (Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp ht))).mpr hpt
    have hlist : Nat.ModEq (q.primeFactors.toList.map (fun p : ℕ => p)).prod
        (a (f q)) (b q) := by
      apply (Nat.modEq_list_map_prod_iff (s := fun p : ℕ => p) hpair).mpr
      intro p hp
      have hpq : p ∈ q.primeFactors := Finset.mem_toList.mp hp
      let pp : P := ⟨p, (hQa q hq).2 hpq⟩
      apply (ZMod.natCast_eq_natCast_iff (a (f q)) (b q) p).mp
      exact (hres (f q) pp).trans (hf q hq pp hpq).symm
    change Nat.ModEq q (a (f q)) (b q)
    simpa [Finset.prod_toList, Nat.prod_primeFactors_of_squarefree (hQa q hq).1] using hlist
  let T : ℕ → Finset P := fun q =>
    U.filter (fun p : P => (p : ℕ) ∈ q.primeFactors)
  let den : ℝ := (38 : ℝ) ^ P.card
  have hden : 0 < den := by positivity
  have hprojection (q : ℕ) (hq : q ∈ Qa) :
      Delta q ≤ (38 : ℝ) ^ (T q).card / den *
        ∑ g : P → Fin 38, ‖fullDiscrepancy u q (a g)‖ := by
    have hp := coherent_color_projection_average
      38 (by norm_num) (T q)
      (fun g : P → Fin 38 => ‖fullDiscrepancy u q (a g)‖)
      (fun _g => norm_nonneg _) (by
        intro g g' hgg'
        have hsame : a g % q = a g' % q := by
          apply hlocal q (hQa q hq).1 (hQa q hq).2 g g'
          intro p hp
          by_cases hpU : p ∈ U
          · exact congrArg (r p) (hgg' p (Finset.mem_filter.mpr ⟨hpU, hp⟩))
          · exact hfixed p hpU (g p) (g' p)
        simp only [fullDiscrepancy,
          progressionMass, hsame]) (f q)
    have heq : Delta q = ‖fullDiscrepancy u q (a (f q))‖ := by
      simp only [Delta, fullDiscrepancy,
        progressionMass, hmod q hq]
    simpa only [← heq, Fintype.card_coe, Nat.cast_ofNat, den] using hp
  have hweight (q : ℕ) (hq : q ∈ Qa) :
      w q * (38 : ℝ) ^ (T q).card ≤ (q.divisors.card : ℝ) ^ 13 := by
    have hTcard : (T q).card ≤ q.primeFactors.card :=
      Finset.card_le_card_of_injOn (fun p : P => (p : ℕ))
        (fun _p hp => (Finset.mem_filter.mp hp).2)
        (fun _p _hp _p' _hp' hpp' => Subtype.ext hpp')
    calc
      w q * (38 : ℝ) ^ (T q).card ≤ w q * (38 : ℝ) ^ q.primeFactors.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hTcard) (hw q)
      _ ≤ (q.divisors.card : ℝ) ^ 13 := by
        dsimp only [w]
        exact_mod_cast selberg39_color_representation_loss q (hQa q hq).1
  have hinner (g : P → Fin 38) :
      (∑ q ∈ Qa, w q * (38 : ℝ) ^ (T q).card *
        ‖fullDiscrepancy u q (a g)‖) ≤ Err := by
    calc
      _ ≤ ∑ q ∈ Qa, (q.divisors.card : ℝ) ^ 13 *
          ‖fullDiscrepancy u q (a g)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_right (hweight q hq) (norm_nonneg _)
      _ ≤ ∑ q ∈ Q, (q.divisors.card : ℝ) ^ 13 *
          ‖fullDiscrepancy u q (a g)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hQaQ
          (fun _q _hq _hqa => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (norm_nonneg _))
      _ ≤ Err := hSource (a g) (hacoprime g)
  have hcount : (Fintype.card (P → Fin 38) : ℝ) = den := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
      Nat.cast_pow, Nat.cast_ofNat, den]
  have hcoherent : (∑ q ∈ Qa, w q * Delta q) ≤ Err := by
    calc
      (∑ q ∈ Qa, w q * Delta q) ≤
          ∑ q ∈ Qa, w q * ((38 : ℝ) ^ (T q).card / den *
            ∑ g : P → Fin 38, ‖fullDiscrepancy u q (a g)‖) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (hprojection q hq) (hw q)
      _ = den⁻¹ * ∑ g : P → Fin 38, ∑ q ∈ Qa,
          w q * (38 : ℝ) ^ (T q).card *
            ‖fullDiscrepancy u q (a g)‖ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g _hg
        apply Finset.sum_congr rfl
        intro q _hq
        ring
      _ ≤ den⁻¹ * ∑ _g : P → Fin 38, Err :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _hg => hinner g)
          (inv_nonneg.mpr hden.le)
      _ = Err := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcount,
          ← mul_assoc, inv_mul_cancel₀ hden.ne', one_mul]
  change (∑ p ∈ S, |lam p.1| * |mu p.2| * err p) ≤ B₁ * B₂ * Err
  calc
    (∑ p ∈ S, |lam p.1| * |mu p.2| * err p) ≤
        ∑ p ∈ S, |lam p.1| * |mu p.2| * Delta (mod p) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hpairMax p hp) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ B₁ * B₂ * ∑ q ∈ Qa, w q * Delta q := hrepresentation
    _ ≤ B₁ * B₂ * Err := mul_le_mul_of_nonneg_left hcoherent (mul_nonneg hB₁ hB₂)

open Classical in
theorem selberg_retained_weighted_interval_crt
    {k : ℕ} (h : Fin (k + 1) → ℕ) (hinj : Function.Injective h)
    (i : Fin (k + 1)) (D E : Finset (Fin k → ℕ))
    (lam mu : (Fin k → ℕ) → ℝ) (W v : ℕ) (hW : 0 < W)
    (hD : ∀ d ∈ D, Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W)
    (hE : ∀ e ∈ E, Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W)
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (hv : Nat.Coprime (v + h i) W) (I : Finset ℕ) (f : ℕ → ℝ) :
    let q : (Fin k → ℕ) → (Fin k → ℕ) → ℕ := fun d e =>
      Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j))
    ∃ residue : (Fin k → ℕ) → (Fin k → ℕ) → ℕ,
      (∀ d ∈ D, ∀ e ∈ E,
        (∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)) →
        0 < q d e ∧ residue d e < q d e ∧
          Nat.Coprime (residue d e + h i) (q d e) ∧
          ∀ n : ℕ, Nat.ModEq (q d e) n (residue d e) ↔
            Nat.ModEq W n v ∧
              (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
              (∀ j : Fin k, e j ∣ n + h (i.succAbove j))) ∧
      (∑ n ∈ I, if Nat.ModEq W n v then
        f (n + h i) *
          (∑ d ∈ D, if ∀ j : Fin k, d j ∣ n + h (i.succAbove j) then lam d else 0) *
          (∑ e ∈ E, if ∀ j : Fin k, e j ∣ n + h (i.succAbove j) then mu e else 0)
        else 0) =
        ∑ d ∈ D, ∑ e ∈ E,
          if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
            lam d * mu e *
              ∑ n ∈ I, if Nat.ModEq (q d e) (n + h i) (residue d e + h i)
                then f (n + h i) else 0
          else 0 := by
  intro q
  have hpair (d : Fin k → ℕ) (hd : d ∈ D) (e : Fin k → ℕ) (he : e ∈ E)
      (hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)) :
      ∃ c : ℕ, 0 < q d e ∧ c < q d e ∧ Nat.Coprime (c + h i) (q d e) ∧
        ∀ n : ℕ, Nat.ModEq (q d e) n c ↔ Nat.ModEq W n v ∧
          (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
          (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) := by
    have hd' : Squarefree (∏ j, (i.insertNth (α := fun _ => ℕ) 1 d) j) ∧
        Nat.Coprime (∏ j, (i.insertNth (α := fun _ => ℕ) 1 d) j) W := by
      simpa only [Fin.prod_insertNth, one_mul] using hD d hd
    have hmod : q d e = W * ∏ j, Nat.lcm (d j) (e j) :=
      actual_modulus_eq_product W d e (hD d hd) (hE e he) hc
    simpa only [Fin.insertNth_apply_succAbove, ← hmod] using
      mixedPair_crt h hinj i
        (i.insertNth (α := fun _ => ℕ) 1 d) e W v hW hd' (hE e he)
        (by simpa only [Fin.insertNth_apply_succAbove] using hc) hcover hv
  let residue : (Fin k → ℕ) → (Fin k → ℕ) → ℕ := fun d e =>
    if hd : d ∈ D then
      if he : e ∈ E then
        if hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
          Classical.choose (hpair d hd e he hc)
        else 0
      else 0
    else 0
  have hresidue (d : Fin k → ℕ) (hd : d ∈ D) (e : Fin k → ℕ) (he : e ∈ E)
      (hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)) :
      0 < q d e ∧ residue d e < q d e ∧
        Nat.Coprime (residue d e + h i) (q d e) ∧
        ∀ n : ℕ, Nat.ModEq (q d e) n (residue d e) ↔ Nat.ModEq W n v ∧
          (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
          (∀ j : Fin k, e j ∣ n + h (i.succAbove j)) := by
    simpa only [residue, dite_eq_left hd, dite_eq_left he, dite_eq_left hc] using
      Classical.choose_spec (hpair d hd e he hc)
  refine ⟨residue, hresidue, ?_⟩
  have hexpand : (∑ n ∈ I, if Nat.ModEq W n v then
      f (n + h i) *
        (∑ d ∈ D, if ∀ j, d j ∣ n + h (i.succAbove j) then lam d else 0) *
        (∑ e ∈ E, if ∀ j, e j ∣ n + h (i.succAbove j) then mu e else 0)
      else 0) =
      ∑ d ∈ D, ∑ e ∈ E, lam d * mu e *
        ∑ n ∈ I, if Nat.ModEq W n v ∧
          (∀ j, d j ∣ n + h (i.succAbove j)) ∧
          (∀ j, e j ∣ n + h (i.succAbove j)) then f (n + h i) else 0 := by
    calc
      _ = ∑ n ∈ I, ∑ d ∈ D, ∑ e ∈ E,
          if Nat.ModEq W n v ∧
            (∀ j, d j ∣ n + h (i.succAbove j)) ∧
            (∀ j, e j ∣ n + h (i.succAbove j))
          then f (n + h i) * lam d * mu e else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases hnv : Nat.ModEq W n v
        · simp only [hnv, ite_true, true_and]
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          split_ifs <;> simp_all [mul_assoc]
        · simp only [hnv, ite_false, false_and, Finset.sum_const_zero]
      _ = ∑ d ∈ D, ∑ e ∈ E, ∑ n ∈ I,
          if Nat.ModEq W n v ∧
            (∀ j, d j ∣ n + h (i.succAbove j)) ∧
            (∀ j, e j ∣ n + h (i.succAbove j))
          then f (n + h i) * lam d * mu e else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs <;> ring
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)
  · rw [ite_eq_left hc]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have hshift : Nat.ModEq (q d e) (n + h i) (residue d e + h i) ↔
        Nat.ModEq (q d e) n (residue d e) :=
      Nat.ModEq.add_iff_right (Nat.ModEq.refl (h i))
    simp only [hshift, (hresidue d hd e he hc).2.2.2 n]
  · rw [ite_eq_right hc]
    have hzero : (∑ n ∈ I, if Nat.ModEq W n v ∧
        (∀ j, d j ∣ n + h (i.succAbove j)) ∧
        (∀ j, e j ∣ n + h (i.succAbove j)) then f (n + h i) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n _
      apply ite_eq_right
      intro hn
      apply hc
      simpa only [Fin.insertNth_apply_succAbove] using
        mixedPair_compatible h hinj i
          (i.insertNth (α := fun _ => ℕ) 1 d) e W
          (by simpa only [Fin.prod_insertNth, one_mul] using (hD d hd).2)
          hcover n (by simpa only [Fin.insertNth_apply_succAbove] using hn.2.1) hn.2.2
    rw [hzero, mul_zero]

open Classical in
theorem fullDiscrepancy_shifted_real_sample
    (I : Finset ℕ) (f : ℕ → ℝ) (h q a : ℕ) :
    fullDiscrepancy
      (∑ m ∈ I.image (fun n => n + h), Finsupp.single m ((f m : ℝ) : ℂ)) q a =
      (((∑ n ∈ I, if Nat.ModEq q (n + h) a then f (n + h) else 0) -
        (∑ n ∈ I, if Nat.Coprime (n + h) q then f (n + h) else 0) /
          (q.totient : ℝ) : ℝ) : ℂ) := by
  rw [fullDiscrepancy_sample,
    Finset.sum_image (fun n _ m _ hnm => Nat.add_right_cancel hnm),
    Finset.sum_sub_distrib, Finset.sum_div]
  simp only [Nat.ModEq]
  push_cast
  simp only [apply_ite, Complex.ofReal_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact (apply_ite Complex.ofReal ((n + h) % q = a % q) (f (n + h)) 0).symm

open Classical in
theorem selberg_retained_weighted_discrepancy_bound
    {k : ℕ} (h : Fin (k + 1) → ℕ) (hinj : Function.Injective h)
    (i : Fin (k + 1)) (D E : Finset (Fin k → ℕ))
    (lam mu : (Fin k → ℕ) → ℝ) (W v : ℕ) (hW : 0 < W)
    (hD : ∀ d ∈ D, Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W)
    (hE : ∀ e ∈ E, Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W)
    (hcover : ∀ a b : Fin (k + 1), h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (hv : Nat.Coprime (v + h i) W) (I : Finset ℕ) (f : ℕ → ℝ)
    (hweight : ∀ d ∈ D, ∀ e ∈ E,
      (∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)) →
      ∀ n ∈ I, f (n + h i) ≠ 0 →
        Nat.Coprime (n + h i) (Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j)))) :
    let q : (Fin k → ℕ) → (Fin k → ℕ) → ℕ := fun d e =>
      Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j))
    let u : ℕ →₀ ℂ :=
      ∑ m ∈ I.image (fun n => n + h i), Finsupp.single m ((f m : ℝ) : ℂ)
    let G : ℝ := ∑ d ∈ D, ∑ e ∈ E,
      if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
        lam d * mu e / (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0
    ∃ residue : (Fin k → ℕ) → (Fin k → ℕ) → ℕ,
      (∀ d ∈ D, ∀ e ∈ E,
        (∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)) →
        0 < q d e ∧ residue d e < q d e ∧
          Nat.Coprime (residue d e + h i) (q d e) ∧
          ∀ n : ℕ, Nat.ModEq (q d e) n (residue d e) ↔
            Nat.ModEq W n v ∧
              (∀ j : Fin k, d j ∣ n + h (i.succAbove j)) ∧
              (∀ j : Fin k, e j ∣ n + h (i.succAbove j))) ∧
      |(∑ n ∈ I, if Nat.ModEq W n v then
        f (n + h i) *
          (∑ d ∈ D, if ∀ j : Fin k, d j ∣ n + h (i.succAbove j) then lam d else 0) *
          (∑ e ∈ E, if ∀ j : Fin k, e j ∣ n + h (i.succAbove j) then mu e else 0)
        else 0) - ((∑ n ∈ I, f (n + h i)) / (W.totient : ℝ)) * G| ≤
        ∑ d ∈ D, ∑ e ∈ E,
          if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
            |lam d| * |mu e| *
              ‖fullDiscrepancy u (q d e) (residue d e + h i)‖
          else 0 := by
  intro q u G
  obtain ⟨residue, hresidue, hexpand⟩ :=
    selberg_retained_weighted_interval_crt h hinj i D E lam mu W v hW
      hD hE hcover hv I f
  refine ⟨residue, hresidue, ?_⟩
  let total : ℝ := ∑ n ∈ I, f (n + h i)
  let progression : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e =>
    ∑ n ∈ I, if Nat.ModEq (q d e) (n + h i) (residue d e + h i)
      then f (n + h i) else 0
  have hmean (d : Fin k → ℕ) (hd : d ∈ D) (e : Fin k → ℕ) (he : e ∈ E)
      (hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)) :
      (∑ n ∈ I, if Nat.Coprime (n + h i) (q d e) then f (n + h i) else 0) = total := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hf : f (n + h i) = 0
    · simp only [hf, ite_self]
    · exact ite_eq_left (hweight d hd e he hc n hn hf)
  have hdelta (d : Fin k → ℕ) (hd : d ∈ D) (e : Fin k → ℕ) (he : e ∈ E)
      (hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)) :
      ‖fullDiscrepancy u (q d e) (residue d e + h i)‖ =
        |progression d e - total / ((q d e).totient : ℝ)| := by
    rw [fullDiscrepancy_shifted_real_sample, hmean d hd e he hc,
      Complex.norm_real, Real.norm_eq_abs]
  have hmain : (total / (W.totient : ℝ)) * G =
      ∑ d ∈ D, ∑ e ∈ E,
        if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
          lam d * mu e * (total / ((q d e).totient : ℝ)) else 0 := by
    dsimp only [G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)
    · simp only [ite_eq_left hc]
      have hphi := selberg_actual_modulus_totient_eq W hW d e (hD d hd) (hE e he) hc
      change (q d e).totient = W.totient * ∏ j, (Nat.lcm (d j) (e j)).totient at hphi
      rw [hphi, Nat.cast_mul, Nat.cast_prod]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp only [ite_eq_right hc, mul_zero]
  have hdiff :
      (∑ n ∈ I, if Nat.ModEq W n v then
        f (n + h i) *
          (∑ d ∈ D, if ∀ j : Fin k, d j ∣ n + h (i.succAbove j) then lam d else 0) *
          (∑ e ∈ E, if ∀ j : Fin k, e j ∣ n + h (i.succAbove j) then mu e else 0)
        else 0) - (total / (W.totient : ℝ)) * G =
      ∑ d ∈ D, ∑ e ∈ E,
        if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
          lam d * mu e * (progression d e - total / ((q d e).totient : ℝ)) else 0 := by
    rw [hexpand, hmain, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)
    · simp only [ite_eq_left hc, progression]
      ring
    · simp only [ite_eq_right hc, sub_self]
  change |(_ : ℝ) - (total / (W.totient : ℝ)) * G| ≤ _
  rw [hdiff]
  calc
    _ ≤ ∑ d ∈ D, |∑ e ∈ E,
        if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
          lam d * mu e * (progression d e - total / ((q d e).totient : ℝ)) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ E,
        |if ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) then
          lam d * mu e * (progression d e - total / ((q d e).totient : ℝ)) else 0| :=
      Finset.sum_le_sum fun d _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      by_cases hc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b)
      · simp only [ite_eq_left hc, abs_mul, hdelta d hd e he hc]
      · simp only [ite_eq_right hc, abs_zero]

open Classical in
theorem selberg38_coherent_weighted_moment_bound
    (h : Fin 39 → ℕ) (hinj : Function.Injective h) (i : Fin 39)
    (D E : Finset (Fin 38 → ℕ)) (lam mu : (Fin 38 → ℕ) → ℝ)
    (W v : ℕ) (hW : 0 < W)
    (hD : ∀ d ∈ D, Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W)
    (hE : ∀ e ∈ E, Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W)
    (hcover : ∀ a b : Fin 39, h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W)
    (hv : Nat.Coprime (v + h i) W) (I : Finset ℕ) (f : ℕ → ℝ)
    (hweight : ∀ d ∈ D, ∀ e ∈ E,
      (∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b)) →
      ∀ n ∈ I, f (n + h i) ≠ 0 →
        Nat.Coprime (n + h i) (Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j))))
    (B₁ B₂ Err : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hlam : ∀ d ∈ D, |lam d| ≤ B₁) (hmu : ∀ e ∈ E, |mu e| ≤ B₂)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Finset ℕ) (hQ : Q ⊆ (∏ p ∈ P, p).divisors)
    (hmoduli : ∀ d ∈ D, ∀ e ∈ E,
      (∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b)) →
      lam d ≠ 0 → mu e ≠ 0 →
        Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j)) ∈ Q)
    (hSource : ∀ a : ℕ, Nat.Coprime a (∏ p ∈ P, p) →
      (∑ q ∈ Q, (q.divisors.card : ℝ) ^ 13 *
        ‖fullDiscrepancy
          (∑ m ∈ I.image (fun n => n + h i), Finsupp.single m ((f m : ℝ) : ℂ)) q a‖) ≤
        Err) :
    let G : ℝ := ∑ d ∈ D, ∑ e ∈ E,
      if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
        lam d * mu e / (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0
    |(∑ n ∈ I, if Nat.ModEq W n v then
        f (n + h i) *
          (∑ d ∈ D, if ∀ j : Fin 38, d j ∣ n + h (i.succAbove j) then lam d else 0) *
          (∑ e ∈ E, if ∀ j : Fin 38, e j ∣ n + h (i.succAbove j) then mu e else 0)
        else 0) - ((∑ n ∈ I, f (n + h i)) / (W.totient : ℝ)) * G| ≤
      B₁ * B₂ * Err := by
  intro G
  let q : (Fin 38 → ℕ) → (Fin 38 → ℕ) → ℕ := fun d e =>
    Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j))
  let u : ℕ →₀ ℂ :=
    ∑ m ∈ I.image (fun n => n + h i), Finsupp.single m ((f m : ℝ) : ℂ)
  obtain ⟨residue, hresidue, hmoment⟩ :=
    selberg_retained_weighted_discrepancy_bound h hinj i D E lam mu W v hW
      hD hE hcover hv I f hweight
  let gate : (Fin 38 → ℕ) → (Fin 38 → ℕ) → Prop := fun d e =>
    (∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b)) ∧ lam d ≠ 0 ∧ mu e ≠ 0
  let r : (p : P) → Fin 38 → ZMod (p : ℕ) := fun p j =>
    if (p : ℕ) ∣ W then ((v + h i : ℕ) : ZMod (p : ℕ))
    else (h i : ZMod (p : ℕ)) - (h (i.succAbove j) : ZMod (p : ℕ))
  have hr (p : P) (j : Fin 38) : r p j ≠ 0 := by
    by_cases hpW : (p : ℕ) ∣ W
    · let : Fact (Nat.Prime (p : ℕ)) := ⟨hP p p.property⟩
      have hu : IsUnit ((v + h i : ℕ) : ZMod (p : ℕ)) :=
        (ZMod.isUnit_iff_coprime _ _).mpr (hv.of_dvd_right hpW)
      simpa only [r, ite_eq_left hpW] using hu.ne_zero
    · simpa only [r, ite_eq_right hpW] using
        (selberg_prime_face_residue_alphabet h hinj i W hcover
          p (hP p p.property) hpW).1 j
  let U : Finset P := Finset.univ.filter (fun p : P => ¬ (p : ℕ) ∣ W)
  have hfixed (p : P) (hp : p ∉ U) (j l : Fin 38) : r p j = r p l := by
    have hpW : (p : ℕ) ∣ W := by
      by_contra hpW
      exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpW⟩)
    simp only [r, ite_eq_left hpW]
  have hchoices (d : Fin 38 → ℕ) (hd : d ∈ D) (e : Fin 38 → ℕ) (he : e ∈ E)
      (hg : gate d e) (p : P) (hpq : (p : ℕ) ∈ (q d e).primeFactors) :
      ∃ j : Fin 38, ((residue d e + h i : ℕ) : ZMod (p : ℕ)) = r p j := by
    have hcrt := hresidue d hd e he hg.1
    have hpoint := (hcrt.2.2.2 (residue d e)).mp (Nat.ModEq.refl _)
    by_cases hpW : (p : ℕ) ∣ W
    · refine ⟨0, ?_⟩
      simp only [r, ite_eq_left hpW]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
        (Nat.ModEq.add_right (h i) (Nat.ModEq.of_dvd hpW hpoint.1))
    · have hpdvd : (p : ℕ) ∣ W * ∏ j : Fin 38, Nat.lcm (d j) (e j) := by
        rw [← actual_modulus_eq_product W d e (hD d hd) (hE e he) hg.1]
        exact Nat.dvd_of_mem_primeFactors hpq
      have hplcm : (p : ℕ) ∣ ∏ j : Fin 38, Nat.lcm (d j) (e j) :=
        ((hP p p.property).dvd_mul.mp hpdvd).resolve_left hpW
      obtain ⟨j, hj⟩ := selberg_prime_face_residue_choice h i d e (residue d e)
        hpoint.2.1 hpoint.2.2 p (hP p p.property) hplcm
      exact ⟨j, by simpa only [r, ite_eq_right hpW] using hj⟩
  have hpair := selberg38_coherent_pair_error_le W hW D E hD hE gate
    (fun _ _ _ _ hg => hg.1) lam mu B₁ B₂ Err hB₁ hB₂ hlam hmu
    P hP r hr U hfixed Q hQ u (fun d e => residue d e + h i)
    (fun d hd e he hg => hmoduli d hd e he hg.1 hg.2.1 hg.2.2)
    hchoices hSource
  have hsum :
      (∑ d ∈ D, ∑ e ∈ E,
        if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
          |lam d| * |mu e| *
            ‖fullDiscrepancy u (q d e) (residue d e + h i)‖
        else 0) =
      ∑ p ∈ (D.product E).filter (fun p => gate p.1 p.2),
        |lam p.1| * |mu p.2| *
          ‖fullDiscrepancy u (q p.1 p.2)
            (residue p.1 p.2 + h i)‖ := by
    rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d _hd
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hl : lam d = 0 <;> by_cases hm : mu e = 0 <;>
      simp [gate, hl, hm]
  exact hmoment.trans (hsum.trans_le hpair)

section

open scoped ContDiff

open Classical in
theorem canonical39_presieving_fragment_carrier
    {𝓗 : Finset ℕ}
    (x R κ : ℝ) :
    let W := presievingModulus 𝓗 x
    let Pfrag := fragmentPrimes W R κ
    let P := W.primeFactors ∪ Pfrag
    (∀ p ∈ Pfrag, p.Prime) ∧ (∀ p ∈ P, p.Prime) ∧
      (∏ p ∈ P, p) = W * (∏ p ∈ Pfrag, p) ∧ 0 < ∏ p ∈ P, p := by
  intro W Pfrag P
  have hfrag (p : ℕ) (hp : p ∈ Pfrag) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact hfrag p hp
  have hW : Squarefree W := by
    dsimp only [W]
    delta presievingModulus
    exact squarefree_prime_prod _
      (fun p hp => presieve_factor_prime 𝓗 x hp)
  have hdisjoint : Disjoint W.primeFactors Pfrag := by
    apply Finset.disjoint_left.mpr
    intro p hp hfragp
    exact (Finset.mem_filter.mp hfragp).2 (Nat.dvd_of_mem_primeFactors hp)
  refine ⟨hfrag, hprime, ?_, Finset.prod_pos (fun p hp => (hprime p hp).pos)⟩
  dsimp only [P]
  rw [Finset.prod_union hdisjoint, Nat.prod_primeFactors_of_squarefree hW]
open Classical in
theorem canonical39_coherent_weighted_error_transfer
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (x : ℝ) (i : Fin 39) (D E : Finset (Fin 38 → ℕ))
    (F G : (Fin 38 → ℕ) → ℝ) (u : ℕ → ℝ)
    (C₁ C₂ K A : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hlog : 0 < Real.log x) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : Q ⊆ (∏ p ∈ P, p).divisors) :
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W := presievingModulus 𝓗 x
    let I := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
    let D' := D.filter (fun d => F d ≠ 0)
    let E' := E.filter (fun e => G e ≠ 0)
    (∀ d ∈ D', Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) W) →
    (∀ e ∈ E', Squarefree (∏ j, e j) ∧ Nat.Coprime (∏ j, e j) W) →
    (∀ d ∈ D, |F d| ≤ C₁ * Real.log x) →
    (∀ e ∈ E, |G e| ≤ C₂ * Real.log x) →
    (∀ d ∈ D', ∀ e ∈ E',
      (∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b)) →
      ∀ n ∈ I, u (n + h i) ≠ 0 →
        Nat.Coprime (n + h i) (Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j)))) →
    (∀ d ∈ D', ∀ e ∈ E',
      Nat.lcm W (Nat.lcm (∏ j, d j) (∏ j, e j)) ∈ Q) →
    (∀ a : ℕ, Nat.Coprime a (∏ p ∈ P, p) →
      (∑ q ∈ Q, (q.divisors.card : ℝ) ^ 13 *
        ‖fullDiscrepancy
          (∑ m ∈ I.image (fun n => n + h i), Finsupp.single m (u m : ℂ)) q a‖) ≤
        K * x / (Real.log x) ^ (A + 2)) →
    ∀ v : ℕ, Nat.Coprime (v + h i) W →
      |(∑ n ∈ I, if Nat.ModEq W n v then
          u (n + h i) *
            (∑ d ∈ D, if ∀ j, d j ∣ n + h (i.succAbove j) then F d else 0) *
            (∑ e ∈ E, if ∀ j, e j ∣ n + h (i.succAbove j) then G e else 0)
          else 0) -
        ((∑ n ∈ I, u (n + h i)) / (W.totient : ℝ)) *
          (∑ d ∈ D, ∑ e ∈ E,
            if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
              F d * G e / (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0)| ≤
        (C₁ * C₂ * K) * x / (Real.log x) ^ A := by
  intro h W I D' E' hD hE hF hG hweight hmoduli hSource v hv
  have hrootF (n : ℕ) :
      (∑ d ∈ D', if ∀ j, d j ∣ n + h (i.succAbove j) then F d else 0) =
        ∑ d ∈ D, if ∀ j, d j ∣ n + h (i.succAbove j) then F d else 0 :=
    Finset.sum_filter_of_ne fun d _ hd hzero => hd (by simp [hzero])
  have hrootG (n : ℕ) :
      (∑ e ∈ E', if ∀ j, e j ∣ n + h (i.succAbove j) then G e else 0) =
        ∑ e ∈ E, if ∀ j, e j ∣ n + h (i.succAbove j) then G e else 0 :=
    Finset.sum_filter_of_ne fun e _ he hzero => he (by simp [hzero])
  have hgram :
      (∑ d ∈ D', ∑ e ∈ E',
        if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
          F d * G e / (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0) =
      ∑ d ∈ D, ∑ e ∈ E,
        if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
          F d * G e / (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0 := by
    change (∑ d ∈ D.filter (fun d => F d ≠ 0), ∑ e ∈ E',
      if ∀ a b : Fin 38, a ≠ b → Nat.Coprime (d a) (e b) then
        F d * G e / (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0) = _
    rw [Finset.sum_filter_of_ne (s := D)]
    · exact Finset.sum_congr rfl fun d _ =>
        Finset.sum_filter_of_ne fun e _ he hzero => he (by simp [hzero])
    · exact fun d _ hd hzero => hd (by simp [hzero])
  have hcover : ∀ a b : Fin 39, h a ≠ h b → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h b) → p ∣ W := by
    intro a b hab p hp hpd
    exact difference_prime_dvd_presieving 𝓗 x
      (𝓗.orderEmbOfFin_mem h𝓗_card a)
      (𝓗.orderEmbOfFin_mem h𝓗_card b) hab hp hpd
  have hfinite := selberg38_coherent_weighted_moment_bound h
    (𝓗.orderEmbOfFin h𝓗_card).injective i
    D' E' F G W v (presieving_pos 𝓗 x)
    hD hE hcover hv I u hweight
    (C₁ * Real.log x) (C₂ * Real.log x) (K * x / (Real.log x) ^ (A + 2))
    (mul_nonneg hC₁.le hlog.le) (mul_nonneg hC₂.le hlog.le)
    (fun d hd => hF d (Finset.mem_filter.mp hd).1)
    (fun e he => hG e (Finset.mem_filter.mp he).1)
    P hP Q hQ (fun d hd e he _ _ _ => hmoduli d hd e he) hSource
  dsimp only at hfinite
  simp only [hrootF, hrootG, hgram] at hfinite
  apply hfinite.trans_eq
  clear * - C₁ C₂ K x A hlog
  rw [Real.rpow_add hlog, Real.rpow_two]
  field_simp

end

end PrimeGap182.Selberg

#print axioms PrimeGap182.Selberg.selberg39_auxiliary_local_gram
#print axioms PrimeGap182.Selberg.selberg_square_real_interval_crt
#print axioms PrimeGap182.Selberg.selberg38_coherent_weighted_moment_bound
#print axioms PrimeGap182.Selberg.canonical39_coherent_weighted_error_transfer
