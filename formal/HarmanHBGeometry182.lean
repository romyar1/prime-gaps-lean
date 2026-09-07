import HarmanTrichotomy182

/-! Actual localized Heath-Brown coefficient geometry at the new 182
cutoffs. Adapted from Apache-2.0 PrimeGaps186, with source hash and explicit
parameter changes checked by scripts/build_harman_hb_geometry.py.
The trichotomy is applied to the actual nonzero integer coefficient,
with its original logarithmic localization error proved. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem minorantHB_three_unmasked_term_geometry
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10) :
    let a : ℝ := 41361 / 100000
    let ζ : ℝ := 1 - 34941 / 100000 - a
    ∃ X : ℝ, 2 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ Θ : ℝ, 1 < Θ → Θ ≤ 2 →
      ∀ (r : Fin 3 → Fin 5) (t : Fin 3 → ℝ),
        (∀ c, 0 ≤ t c) → (∀ c, t c ≤ 10) →
      ∀ ν d : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ,
        ν ∈ Fintype.piFinset (fun c : Fin 3 =>
          minorantHBBoxes ((r c).val + 1) (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ) →
        (x ≤ ((∏ c, ∏ i, d c i : ℕ) : ℝ) ∧
          ((∏ c, ∏ i, d c i : ℕ) : ℝ) ≤ 3 * x) →
        (∏ c : Fin 3, ∏ i,
          (minorantHBLocalizedSlot ((r c).val + 1) (x ^ (9 / 100 : ℝ))
            Θ (t c) (ν c) i).coeff (d c i)) ≠ 0 →
        let α : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℝ :=
          fun c i => Real.logb x (Θ ^ ν c i)
        Fintype.card (Σ c : Fin 3, Fin (2 * ((r c).val + 1))) ≤ 30 ∧
          (∀ c i, 0 ≤ α c i) ∧
          (∀ c : Fin 3, ζ - τ / 5 ≤ ∑ i, α c i) ∧
          |(∑ c, ∑ i, α c i) - 1| ≤ τ / 1000 ∧
          ∀ (c : Fin 3) (i : Fin (2 * ((r c).val + 1))),
            i.val < (r c).val + 1 → α c i ≤ 1 / 10 := by
  intro a ζ
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  let X : ℝ := max 2 (Real.exp (100000 * (Real.log 2 + Real.log 3) / τ))
  refine ⟨X, le_max_left _ _, ?_⟩
  intro x hx Θ hΘ hΘtwo r t ht htten ν d hν htotal hterm α
  have hxTwo : 2 ≤ x := (le_max_left _ _).trans hx
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hxTwo
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hlogx : 0 < Real.log x := Real.log_pos hxOne
  have hΘpos : 0 < Θ := zero_lt_one.trans hΘ
  have hlarge : 100000 * (Real.log 2 + Real.log 3) / τ ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxPos).mpr ((le_max_right _ _).trans hx)
  have hsmall : (Real.log 2 + Real.log 3) / Real.log x ≤ τ / 100000 := by
    apply (div_le_iff₀ hlogx).mpr
    have hh := (div_le_iff₀ hτ).mp hlarge
    calc
      Real.log 2 + Real.log 3 ≤ (Real.log x * τ) / 100000 :=
        (le_div_iff₀ (by norm_num : (0 : ℝ) < 100000)).mpr
          (by simpa only [mul_comm] using hh)
      _ = τ / 100000 * Real.log x := by ring
  let e : ℝ := Real.logb x Θ
  have he : 0 ≤ e := Real.logb_nonneg hxOne hΘ.le
  have heSmall : e ≤ τ / 100000 :=
    (div_le_div_of_nonneg_right
      ((Real.log_le_log hΘpos hΘtwo).trans (le_add_of_nonneg_right hlog3)) hlogx.le).trans
      hsmall
  have hthreeSmall : Real.logb x 3 ≤ τ / 100000 :=
    (div_le_div_of_nonneg_right (le_add_of_nonneg_left hlog2) hlogx.le).trans hsmall
  have hA : 1 ≤ x ^ (ζ - τ / 10) :=
    Real.one_le_rpow hxOne.le (by dsimp [ζ, a]; linarith only [hτsmall])
  have hAB : x ^ (ζ - τ / 10) ≤ x ^ (a + τ / 10) :=
    Real.rpow_le_rpow_of_exponent_le hxOne.le (by dsimp [ζ, a]; linarith only [hτ])
  have hs (c : Fin 3) (i : Fin (2 * ((r c).val + 1))) :
      d c i ∈ (minorantHBLocalizedSlot ((r c).val + 1) (x ^ (9 / 100 : ℝ))
        Θ (t c) (ν c) i).coeff.support := by
    apply Finsupp.mem_support_iff.mpr
    exact (Finset.prod_ne_zero_iff.mp
      ((Finset.prod_ne_zero_iff.mp hterm) c (Finset.mem_univ c))) i (Finset.mem_univ i)
  have hslot (c : Fin 3) (i : Fin (2 * ((r c).val + 1))) :
      Θ ^ ν c i / Θ ≤ (d c i : ℝ) ∧ (d c i : ℝ) ≤ Θ * Θ ^ ν c i := by
    have hw := (minorantHB_box_localization ((r c).val + 1) (by omega)
      (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) (x ^ (9 / 100 : ℝ))
      Θ (t c) hA hAB hΘ hΘtwo (ht c) (htten c)).2.2
        (ν c) (Fintype.mem_piFinset.mp hν c) i (d c i) (hs c i)
    exact ⟨hw.1, hw.2.1⟩
  have hslots (c : Fin 3) : 2 * ((r c).val + 1) ≤ 10 := by
    have hr := (r c).isLt
    omega
  have hdPos (c : Fin 3) (i : Fin (2 * ((r c).val + 1))) : 0 < (d c i : ℝ) :=
    (div_pos (pow_pos hΘpos _) hΘpos).trans_le (hslot c i).1
  have hlogSlot (c : Fin 3) (i : Fin (2 * ((r c).val + 1))) :
      α c i - e ≤ Real.logb x (d c i : ℝ) ∧
        Real.logb x (d c i : ℝ) ≤ α c i + e := by
    have hlo := Real.logb_le_logb_of_le hxOne
      (div_pos (pow_pos hΘpos _) hΘpos) (hslot c i).1
    rw [Real.logb_div (pow_ne_zero _ hΘpos.ne') hΘpos.ne'] at hlo
    have hhi := Real.logb_le_logb_of_le hxOne (hdPos c i) (hslot c i).2
    rw [Real.logb_mul hΘpos.ne' (pow_ne_zero _ hΘpos.ne')] at hhi
    exact ⟨hlo, by simpa only [add_comm] using hhi⟩
  have hlogProd : Real.logb x ((∏ c, ∏ i, d c i : ℕ) : ℝ) =
      ∑ c, ∑ i, Real.logb x (d c i : ℝ) := by
    rw [Nat.cast_prod, Real.logb_prod Finset.univ _ (fun c _ => by
      rw [Nat.cast_prod]
      exact (Finset.prod_pos (fun i _ => hdPos c i)).ne')]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Nat.cast_prod]
    exact Real.logb_prod Finset.univ _ (fun i _ => (hdPos c i).ne')
  have htotalBounds :
      1 ≤ ∑ c, ∑ i, Real.logb x (d c i : ℝ) ∧
        (∑ c, ∑ i, Real.logb x (d c i : ℝ)) ≤ 1 + Real.logb x 3 := by
    have hlo := Real.logb_le_logb_of_le hxOne hxPos htotal.1
    have hhi := Real.logb_le_logb_of_le hxOne (hxPos.trans_le htotal.1) htotal.2
    rw [Real.logb_self_eq_one hxOne, hlogProd] at hlo
    rw [hlogProd, Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0) hxPos.ne',
      Real.logb_self_eq_one hxOne] at hhi
    exact ⟨hlo, by simpa only [add_comm] using hhi⟩
  have herror (c : Fin 3) :
      (∑ i, α c i) - 10 * e ≤ ∑ i, Real.logb x (d c i : ℝ) ∧
        (∑ i, Real.logb x (d c i : ℝ)) ≤ (∑ i, α c i) + 10 * e := by
    have hlo := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hlogSlot c i).1)
    have hhi := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hlogSlot c i).2)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hhi
    have hc : ((2 * ((r c).val + 1) : ℕ) : ℝ) ≤ 10 := by exact_mod_cast hslots c
    have herr := mul_le_mul_of_nonneg_right hc he
    constructor <;> linarith only [hlo, hhi, herr]
  have hall :
      (∑ c, ∑ i, α c i) - 30 * e ≤ ∑ c, ∑ i, Real.logb x (d c i : ℝ) ∧
        (∑ c, ∑ i, Real.logb x (d c i : ℝ)) ≤ (∑ c, ∑ i, α c i) + 30 * e := by
    have hlo := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => (herror c).1)
    have hhi := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => (herror c).2)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hlo hhi
    constructor <;> linarith only [hlo, hhi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sigma]
    calc
      (∑ c : Fin 3, Fintype.card (Fin (2 * ((r c).val + 1)))) ≤
          ∑ _c : Fin 3, (10 : ℕ) := by
        exact Finset.sum_le_sum (fun c _ => by
          simpa only [Fintype.card_fin] using hslots c)
      _ = 30 := by norm_num
  · exact fun c i => Real.logb_nonneg hxOne (one_le_pow₀ hΘ.le)
  · intro c
    have hνc := Fintype.mem_piFinset.mp hν c
    dsimp only [minorantHBBoxes] at hνc
    have hlo := (Finset.mem_filter.mp hνc).2.1
    have hl := Real.logb_le_logb_of_le hxOne
      (div_pos (Real.rpow_pos_of_pos hxPos _) (pow_pos hΘpos _)) hlo
    rw [Real.logb_div (Real.rpow_pos_of_pos hxPos _).ne' (pow_pos hΘpos _).ne',
      Real.logb_rpow hxPos hxOne.ne', Real.logb_pow,
      Real.logb_prod Finset.univ _ (fun i _ => pow_ne_zero _ hΘpos.ne')] at hl
    change ζ - τ / 10 - ((2 * ((r c).val + 1) : ℕ) : ℝ) * e ≤ ∑ i, α c i at hl
    have hc : ((2 * ((r c).val + 1) : ℕ) : ℝ) ≤ 10 := by exact_mod_cast hslots c
    have herr := mul_le_mul_of_nonneg_right hc he
    linarith only [hl, herr, heSmall, hτ]
  · apply abs_le.mpr
    constructor <;> linarith only [hall.1, hall.2, htotalBounds.1,
      htotalBounds.2, heSmall, hthreeSmall, hτ]
  · intro c i hi
    have hm := (minorantHBLocalizedSlot_moebius_support ((r c).val + 1)
      (x ^ (9 / 100 : ℝ)) Θ (t c) (ν c) i hi (d c i) (hs c i)).2
    have hdHi : Real.logb x (d c i : ℝ) ≤ 9 / 100 :=
      (Real.logb_le_iff_le_rpow hxOne (hdPos c i)).mpr hm
    have hsl := (hlogSlot c i).1
    linarith only [hdHi, hsl, heSmall, hτsmall]

open Classical in
theorem minorantHB_three_unmasked_term_cases
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10) :
    let a : ℝ := 41361 / 100000
    let ζ : ℝ := 1 - 34941 / 100000 - a
    ∃ X : ℝ, 2 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ Θ : ℝ, 1 < Θ → Θ ≤ 2 →
      ∀ (r : Fin 3 → Fin 5) (t : Fin 3 → ℝ),
        (∀ c, 0 ≤ t c) → (∀ c, t c ≤ 10) →
      ∀ ν d : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ,
        ν ∈ Fintype.piFinset (fun c : Fin 3 =>
          minorantHBBoxes ((r c).val + 1) (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ) →
        (x ≤ ((∏ c, ∏ i, d c i : ℕ) : ℝ) ∧ ((∏ c, ∏ i, d c i : ℕ) : ℝ) ≤ 3 * x) →
        (∏ c : Fin 3, ∏ i,
          (minorantHBLocalizedSlot ((r c).val + 1) (x ^ (9 / 100 : ℝ))
            Θ (t c) (ν c) i).coeff (d c i)) ≠ 0 →
        let α : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℝ :=
          fun c i => Real.logb x (Θ ^ ν c i)
        let I := Σ c : Fin 3, Fin (2 * ((r c).val + 1))
        Fintype.card I ≤ 30 ∧
          ((∃ s : I,
            (r s.1).val + 1 ≤ s.2.val ∧ 34941 / 100000 - τ ≤ α s.1 s.2) ∨
          (∃ S : Finset I,
            a - τ ≤ ∑ s ∈ S, α s.1 s.2 ∧
              (∑ s ∈ S, α s.1 s.2) ≤ 58639 / 100000 + τ) ∨
          (∃ s t u : I,
            s ≠ t ∧ s ≠ u ∧ t ≠ u ∧
            (r s.1).val + 1 ≤ s.2.val ∧ (r t.1).val + 1 ≤ t.2.val ∧
            (r u.1).val + 1 ≤ u.2.val ∧
            (4318 / 25000 - τ ≤ α s.1 s.2 ∧ α s.1 s.2 ≤ 10341 / 25000 + τ) ∧
            (4318 / 25000 - τ ≤ α t.1 t.2 ∧ α t.1 t.2 ≤ 10341 / 25000 + τ) ∧
            (4318 / 25000 - τ ≤ α u.1 u.2 ∧ α u.1 u.2 ≤ 10341 / 25000 + τ) ∧
            14659 / 25000 - τ ≤ α s.1 s.2 + α t.1 t.2 ∧
            14659 / 25000 - τ ≤ α s.1 s.2 + α u.1 u.2 ∧
            14659 / 25000 - τ ≤ α t.1 t.2 + α u.1 u.2)) := by
  intro a ζ
  obtain ⟨X, hX, hgeometry⟩ := minorantHB_three_unmasked_term_geometry τ hτ hτsmall
  refine ⟨X, hX, ?_⟩
  intro x hx Θ hΘ hΘtwo r t ht htten ν d hν htotal hterm α I
  have hg := hgeometry x hx Θ hΘ hΘtwo r t ht htten ν d hν htotal hterm
  refine ⟨hg.1, ?_⟩
  exact minorant_three_prime_colored_slot_trichotomy τ hτ hτsmall r α hg.2.1 hg.2.2.1
    hg.2.2.2.1 hg.2.2.2.2

open Classical in
theorem minorantHB_three_unmasked_coefficient_cases
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10) :
    let a : ℝ := 41361 / 100000
    let ζ : ℝ := 1 - 34941 / 100000 - a
    ∃ X : ℝ, 2 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ Θ : ℝ, 1 < Θ → Θ ≤ 2 →
      ∀ (r : Fin 3 → Fin 5) (t : Fin 3 → ℝ),
        (∀ c, 0 ≤ t c) → (∀ c, t c ≤ 10) →
      ∀ ν : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ,
        ν ∈ Fintype.piFinset (fun c : Fin 3 =>
          minorantHBBoxes ((r c).val + 1) (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ) →
      ∀ n : ℕ, x ≤ (n : ℝ) → (n : ℝ) ≤ 3 * x →
        (∏ s : Σ c : Fin 3, Fin (2 * ((r c).val + 1)),
          minorantHBLocalizedSlot ((r s.1).val + 1) (x ^ (9 / 100 : ℝ))
            Θ (t s.1) (ν s.1) s.2).coeff n ≠ 0 →
        let α : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℝ :=
          fun c i => Real.logb x (Θ ^ ν c i)
        let I := Σ c : Fin 3, Fin (2 * ((r c).val + 1))
        Fintype.card I ≤ 30 ∧
          ((∃ s : I,
            (r s.1).val + 1 ≤ s.2.val ∧ 34941 / 100000 - τ ≤ α s.1 s.2) ∨
          (∃ S : Finset I,
            a - τ ≤ ∑ s ∈ S, α s.1 s.2 ∧
              (∑ s ∈ S, α s.1 s.2) ≤ 58639 / 100000 + τ) ∨
          (∃ s t u : I,
            s ≠ t ∧ s ≠ u ∧ t ≠ u ∧
            (r s.1).val + 1 ≤ s.2.val ∧ (r t.1).val + 1 ≤ t.2.val ∧
            (r u.1).val + 1 ≤ u.2.val ∧
            (4318 / 25000 - τ ≤ α s.1 s.2 ∧ α s.1 s.2 ≤ 10341 / 25000 + τ) ∧
            (4318 / 25000 - τ ≤ α t.1 t.2 ∧ α t.1 t.2 ≤ 10341 / 25000 + τ) ∧
            (4318 / 25000 - τ ≤ α u.1 u.2 ∧ α u.1 u.2 ≤ 10341 / 25000 + τ) ∧
            14659 / 25000 - τ ≤ α s.1 s.2 + α t.1 t.2 ∧
            14659 / 25000 - τ ≤ α s.1 s.2 + α u.1 u.2 ∧
            14659 / 25000 - τ ≤ α t.1 t.2 + α u.1 u.2)) := by
  intro a ζ
  obtain ⟨X, hX, hcases⟩ := minorantHB_three_unmasked_term_cases τ hτ hτsmall
  refine ⟨X, hX, ?_⟩
  intro x hx Θ hΘ hΘtwo r t ht htten ν hν n hnlo hnhi hcoef α I
  let β : I → MonoidAlgebra ℂ ℕ := fun s =>
    minorantHBLocalizedSlot ((r s.1).val + 1) (x ^ (9 / 100 : ℝ))
      Θ (t s.1) (ν s.1) s.2
  change (∏ s : I, β s).coeff n ≠ 0 at hcoef
  rw [minorantHB_product_coefficient] at hcoef
  obtain ⟨d, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoef
  have hprod : (∏ s : I, d s) = n := by
    by_contra hbad
    exact hterm (ite_eq_right hbad)
  have hnonzero : (∏ s : I, (β s).coeff (d s)) ≠ 0 := by
    simpa only [ite_eq_left hprod] using hterm
  have hprod' : (∏ c : Fin 3, ∏ i, d ⟨c, i⟩) = n :=
    (Fintype.prod_sigma d).symm.trans hprod
  have hnonzero' : (∏ c : Fin 3, ∏ i,
      (minorantHBLocalizedSlot ((r c).val + 1) (x ^ (9 / 100 : ℝ))
        Θ (t c) (ν c) i).coeff (d ⟨c, i⟩)) ≠ 0 :=
    (congrArg (fun z : ℂ => z ≠ 0)
      (Fintype.prod_sigma (fun s : I => (β s).coeff (d s)))).mp hnonzero
  exact hcases x hx Θ hΘ hΘtwo r t ht htten ν (fun c i => d ⟨c, i⟩) hν
    (by simpa only [hprod'] using And.intro hnlo hnhi) hnonzero'

#print axioms minorantHB_three_unmasked_term_geometry
#print axioms minorantHB_three_unmasked_term_cases
#print axioms minorantHB_three_unmasked_coefficient_cases

end PrimeGap182Analytic.Harman
