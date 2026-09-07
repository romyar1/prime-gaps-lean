import HarmanSourceGeometry182

/-! Actual geometric bins, central factor selection, and positive monomial
boundary counts at lambda=.17278. These include the small-prime error term
at its new exponent. Adapted from Apache-2.0 PrimeGaps186 at the pinned hash. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

variable {arity : ℕ}

theorem small_prime_geometric_bin_eq_closed_interval
    (x h : ℝ) (hx : 0 < x) (hh : 0 < h) (k : ℕ) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
    let L : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ k)
    let U : ℝ := min (x ^ ((9 : ℝ) / 10))
      ((⌈(1 + h) ^ (k + 1)⌉₊ - 1 : ℕ) : ℝ)
    P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = k) =
      (Finset.Icc ⌈L⌉₊ ⌊U⌋₊).filter Nat.Prime := by
  classical
  intro P L U
  have hpow : 0 ≤ x ^ ((9 : ℝ) / 10) := (Real.rpow_pos_of_pos hx _).le
  have hU : 0 ≤ U := le_min hpow (Nat.cast_nonneg _)
  ext n
  by_cases hp : n.Prime
  · simp only [P, Finset.mem_filter, Finset.mem_Icc, hp, and_true,
      geometric_bin_integer_interval h hh n k hp.one_lt.le,
      Nat.ceil_le, Nat.le_floor_iff hpow, Nat.le_floor_iff hU]
    dsimp [L, U]
    rw [max_le_iff, le_min_iff, Nat.cast_le]
    tauto
  · simp [P, hp]

theorem small_prime_geometric_active_scales (hArity : arity ≤ 3)
    (x h : ℝ) (hx : 2 ≤ x) (hh : 0 < h) (hh1 : h ≤ 1)
    (b p : Fin (arity + 1) → ℕ) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
    let L (i : Fin (arity + 1)) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
    let U (i : Fin (arity + 1)) : ℝ := min (x ^ ((9 : ℝ) / 10))
      ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ)
    (∀ i, p i ∈ P) →
    (∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ = b i) →
    (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
    (∀ i, x ^ ((1 : ℝ) / 10) ≤ L i ∧ L i ≤ U i ∧ U i ≤ 2 * L i) ∧
      x / 32 ≤ ∏ i, L i ∧ (∏ i, L i) ≤ 2 * x := by
  classical
  intro P L U hp hlabel hprod
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hbase : 0 < 1 + h := by linarith
  have hL (i : Fin (arity + 1)) : 0 ≤ L i :=
    (Real.rpow_pos_of_pos hx0 _).le.trans (le_max_left _ _)
  have hpLU (i : Fin (arity + 1)) : L i ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ U i := by
    have hm : p i ∈ P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = b i) :=
      Finset.mem_filter.mpr ⟨hp i, hlabel i⟩
    rw [small_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)] at hm
    have hm' := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    exact ⟨Nat.le_of_ceil_le hm'.1,
      (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (by positivity))⟩
  have hU (i : Fin (arity + 1)) : U i ≤ 2 * L i := by
    have hceil : 0 < ⌈(1 + h) ^ (b i + 1)⌉₊ :=
      Nat.ceil_pos.mpr (pow_pos hbase _)
    have htop : ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ) <
        (1 + h) ^ (b i + 1) := Nat.lt_ceil.mp (by omega)
    calc
      U i ≤ ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ) := min_le_right _ _
      _ ≤ (1 + h) ^ (b i + 1) := htop.le
      _ = (1 + h) * (1 + h) ^ b i := by rw [pow_succ]; ring
      _ ≤ 2 * L i := mul_le_mul (by linarith) (le_max_right _ _)
        (pow_nonneg hbase.le _) (by norm_num)
  have hproduct : x ≤ ∏ i, (p i : ℝ) ∧ (∏ i, (p i : ℝ)) ≤ 2 * x := by
    have hmem := Finset.mem_Icc.mp hprod
    constructor
    · exact_mod_cast Nat.le_of_ceil_le hmem.1
    · exact_mod_cast (Nat.cast_le.mpr hmem.2).trans (Nat.floor_le (by positivity))
  have hupper : (∏ i, L i) ≤ 2 * x :=
    (Finset.prod_le_prod (fun i _ => hL i) (fun i _ => (hpLU i).1)).trans hproduct.2
  have hcompare : (∏ i, (p i : ℝ)) ≤ 32 * ∏ i, L i := by
    calc
      _ ≤ ∏ i, 2 * L i := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => (hpLU i).2.trans (hU i))
      _ = (2 : ℝ) ^ (arity + 1) * ∏ i, L i := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ 32 * ∏ i, L i := mul_le_mul_of_nonneg_right
        ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by omega : arity + 1 ≤ 5)).trans_eq (by norm_num))
        (Finset.prod_nonneg fun i _ => hL i)
  refine ⟨?_, ?_, hupper⟩
  · intro i
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num :
      (1 : ℝ) / 10 ≤ (8639 : ℝ) / 50000)).trans (le_max_left _ _),
      (hpLU i).1.trans (hpLU i).2, hU i⟩
  · linarith [hproduct.1, hcompare]

open Classical in
theorem small_prime_geometric_box_card_polylog (hArity : arity ≤ 3)
    (D x : ℝ) (hD : 0 ≤ D) (hx : Real.exp 1 ≤ x) :
    let h := (Real.log x) ^ (-D)
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
    let T := Fintype.piFinset (fun _ : Fin (arity + 1) => P)
    let label (p : Fin (arity + 1) → ℕ) : Fin (arity + 1) → ℕ :=
      fun i => ⌊Real.logb (1 + h) (p i : ℝ)⌋₊
    ((T.image label).card : ℝ) ≤
      (6 : ℝ) ^ 4 * (Real.log x) ^ (4 * (D + 1)) := by
  intro h P T label
  have hmesh := four_geometric_log_mesh_spec D x hD hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  let K : ℕ := ⌈Real.logb (1 + h) (2 * x)⌉₊ + 1
  have hK (n : ℕ) (hn : n ∈ P) : ⌊Real.logb (1 + h) (n : ℝ)⌋₊ < K := by
    obtain ⟨hnI, hnprime⟩ := Finset.mem_filter.mp hn
    have hupper : (n : ℝ) ≤ 2 * x := by
      calc
        _ ≤ x ^ ((9 : ℝ) / 10) :=
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hnI).2).trans
            (Nat.floor_le (Real.rpow_pos_of_pos hx0 _).le)
        _ ≤ x := Real.rpow_le_self_of_one_le hx1 (by norm_num)
        _ ≤ 2 * x := by linarith
    exact geometric_bin_label_bound h x hmesh.1 n hnprime.one_lt.le hupper
  have hcard : (T.image label).card ≤ K ^ (arity + 1) :=
    (finite_small_prime_box_cut_decomposition P
      (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊) (fun _ => True)).2.2.1 K hK
  have hKone : (1 : ℝ) ≤ K := by dsimp only [K]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact (show ((T.image label).card : ℝ) ≤ (K : ℝ) ^ (arity + 1)
    by exact_mod_cast hcard).trans
      ((pow_le_pow_right₀ hKone (by omega : arity + 1 ≤ 4)).trans hmesh.2.2)

open Classical in
theorem small_prime_geometric_central_scales (hArity : arity ≤ 3) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, 0 < h → h ≤ 1 / 4 → ∀ b p : Fin (arity + 1) → ℕ,
      let P : Finset ℕ :=
        (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
          ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
      let L (i : Fin (arity + 1)) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
      let U (i : Fin (arity + 1)) : ℝ := min (x ^ ((9 : ℝ) / 10))
        ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ)
      (∀ i, p i ∈ P) →
      (∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ = b i) →
      (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
      ∀ S : Finset (Fin (arity + 1)), S.Nonempty → S ≠ Finset.univ →
        x ^ ((41361 : ℝ) / 100000) ≤ ∏ i ∈ S, (p i : ℝ) →
        (∏ i ∈ S, (p i : ℝ)) ≤ x ^ ((58639 : ℝ) / 100000) →
        ∃ R : Finset (Fin (arity + 1)), ∃ Y : Fin (arity + 1) → ℝ,
          (R = S ∨ R = Sᶜ) ∧ R.Nonempty ∧ R ≠ Finset.univ ∧
          (∀ i, x ^ ((8639 : ℝ) / 100000) ≤ Y i ∧ Y i ≤ x ^ (2 : ℝ)) ∧
          (∀ i, Y i ≤ L i ∧ U i ≤ 2 * Y i) ∧
          x / 64 ≤ ∏ i, Y i ∧ (∏ i, Y i) ≤ 64 * x ∧
          x ^ ((41361 : ℝ) / 100000 - τ) ≤ ∏ i ∈ R, Y i ∧
          (∏ i ∈ R, Y i) ≤ x ^ (1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_ge_atTop (64 : ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8639 / 100000)).eventually
      (eventually_ge_atTop (2 : ℝ))] with x hx hxτ hxξ
  intro h hh hh4 b p P L U hp hlabel hprod S hSnon hSne hcentralLo hcentralHi
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hbase : 0 < 1 + h := by linarith
  have hscales := small_prime_geometric_active_scales hArity x h hx hh (by linarith)
    b p hp hlabel hprod
  have hLpos (i : Fin (arity + 1)) : 0 < L i :=
    (Real.rpow_pos_of_pos hx0 _).trans_le (le_max_left _ _)
  have hpLU (i : Fin (arity + 1)) : L i ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ U i := by
    have hm : p i ∈ P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = b i) :=
      Finset.mem_filter.mpr ⟨hp i, hlabel i⟩
    rw [small_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)] at hm
    have hm' := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    exact ⟨Nat.le_of_ceil_le hm'.1,
      (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (by positivity))⟩
  have hUnarrow (i : Fin (arity + 1)) : U i ≤ (4 / 3 : ℝ) * L i := by
    have hceil : 0 < ⌈(1 + h) ^ (b i + 1)⌉₊ :=
      Nat.ceil_pos.mpr (pow_pos hbase _)
    have htop : ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ) <
        (1 + h) ^ (b i + 1) := Nat.lt_ceil.mp (by omega)
    calc
      U i ≤ ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ) := min_le_right _ _
      _ ≤ (1 + h) ^ (b i + 1) := htop.le
      _ = (1 + h) * (1 + h) ^ b i := by rw [pow_succ]; ring
      _ ≤ (4 / 3 : ℝ) * L i := mul_le_mul (by linarith) (le_max_right _ _)
        (pow_nonneg hbase.le _) (by norm_num)
  have hsubcompare (T : Finset (Fin (arity + 1))) :
      (∏ i ∈ T, (p i : ℝ)) ≤ 32 * ∏ i ∈ T, L i := by
    have hT : T.card ≤ 5 := by
      have ht : T.card ≤ arity + 1 := by
        simpa using (Finset.card_le_card (Finset.subset_univ T))
      omega
    have hpow : (2 : ℝ) ^ T.card ≤ 32 := by
      calc
        _ ≤ (2 : ℝ) ^ 5 := pow_le_pow_right₀ (by norm_num) hT
        _ = 32 := by norm_num
    calc
      _ ≤ ∏ i ∈ T, 2 * L i := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => (hpLU i).2.trans (hscales.1 i).2.2)
      _ = (2 : ℝ) ^ T.card * ∏ i ∈ T, L i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 32 * ∏ i ∈ T, L i := mul_le_mul_of_nonneg_right hpow
        (Finset.prod_nonneg fun i _ => (hLpos i).le)
  have hpfull : x ≤ ∏ i, (p i : ℝ) := by
    exact_mod_cast Nat.le_of_ceil_le (Finset.mem_Icc.mp hprod).1
  have hpower : x ^ ((58639 : ℝ) / 100000) * x ^ ((41361 : ℝ) / 100000) = x := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hcomp : x ^ ((41361 : ℝ) / 100000) ≤ ∏ i ∈ Sᶜ, (p i : ℝ) := by
    apply le_of_mul_le_mul_left (a := x ^ ((58639 : ℝ) / 100000))
      ?_ (Real.rpow_pos_of_pos hx0 _)
    calc
      _ = x := hpower
      _ ≤ ∏ i, (p i : ℝ) := hpfull
      _ = (∏ i ∈ S, (p i : ℝ)) * ∏ i ∈ Sᶜ, (p i : ℝ) :=
        (Finset.prod_mul_prod_compl S (fun i => (p i : ℝ))).symm
      _ ≤ x ^ ((58639 : ℝ) / 100000) * ∏ i ∈ Sᶜ, (p i : ℝ) :=
        mul_le_mul_of_nonneg_right hcentralHi (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
  obtain ⟨R, Y, hR, hRn, hRne, hY, hprodLo, hprodHi, hblockLo, hblockHi⟩ :=
    small_central_box_one_coordinate_scales x hx0.le L U hLpos
      (fun i => ⟨(hpLU i).1.trans (hpLU i).2, hUnarrow i⟩)
      hscales.2.2 S hSnon hSne
  have hRlower : x ^ ((41361 : ℝ) / 100000) / 32 ≤ ∏ i ∈ R, L i := by
    rcases hR with hRS | hRS
    · rw [hRS]
      linarith [hsubcompare S]
    · rw [hRS]
      linarith [hsubcompare Sᶜ]
  refine ⟨R, Y, hR, hRn, hRne, ?_, (fun i => (hY i).2), ?_, ?_, ?_, hblockHi⟩
  · intro i
    constructor
    · have hξpos : 0 < x ^ ((8639 : ℝ) / 100000) := Real.rpow_pos_of_pos hx0 _
      have hξsq : x ^ ((8639 : ℝ) / 50000) =
          x ^ ((8639 : ℝ) / 100000) * x ^ ((8639 : ℝ) / 100000) := by
        rw [← Real.rpow_add hx0]
        congr 1
        norm_num
      have hξL : x ^ ((8639 : ℝ) / 50000) ≤ L i := le_max_left _ _
      have hξmul := mul_le_mul_of_nonneg_right hxξ hξpos.le
      nlinarith [(hY i).1]
    · exact (hY i).2.1.trans ((hscales.1 i).2.1.trans
        ((min_le_left _ _).trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))))
  · linarith [hscales.2.1]
  · linarith [hscales.2.2]
  · rw [Real.rpow_sub hx0]
    exact (div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hx0 _).le
      (by norm_num : (0 : ℝ) < 64) hxτ).trans (by linarith)

theorem geometric_small_box_product_bound (hArity : arity ≤ 3) (h x : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (p q : Fin (arity + 1) → ℕ) (hp : ∀ i, 1 ≤ p i) (hq : ∀ i, 1 ≤ q i)
    (hlabel : ∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ =
      ⌊Real.logb (1 + h) (q i : ℝ)⌋₊)
    (hprod : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x) :
    ((∏ i, q i : ℕ) : ℝ) ≤ 64 * x := by
  have hp0 : 0 ≤ ∏ i, (p i : ℝ) := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  have hprod' : (∏ i, (p i : ℝ)) ≤ 2 * x := by exact_mod_cast hprod
  have hratio : (∏ i, (q i : ℝ)) ≤ (1 + h) ^ (arity + 1) * ∏ i, (p i : ℝ) := by
    calc
      _ ≤ ∏ i, ((1 + h) * p i) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          (fun i _ => (geometric_bin_pair_ratios h hh (p i) (q i)
            (hp i) (hq i) (hlabel i)).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hpow : (1 + h) ^ (arity + 1) ≤ (32 : ℝ) := by
    calc
      (1 + h) ^ (arity + 1) ≤ (2 : ℝ) ^ (arity + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 32 := by norm_num
  have := hratio.trans (mul_le_mul_of_nonneg_right hpow hp0)
  exact_mod_cast this.trans (by nlinarith only [hprod'])

theorem finite_small_tuple_monomial_boundary_count (hArity : arity ≤ 3)
    (x η : ℝ) (hx : 2 ≤ x) (hη : 0 ≤ η) (i : Fin (arity + 1))
    (S : Finset (Fin (arity + 1) → ℕ)) (L U : (Fin arity → ℕ) → ℝ)
    (hS : ∀ t ∈ S,
      (∀ j, x ^ ((8639 : ℝ) / 50000) ≤ (t j : ℝ)) ∧
        ((∏ j, t j : ℕ) : ℝ) ≤ 64 * x ∧
        L (Fin.removeNth i t) ≤ (t i : ℝ) ∧
        (t i : ℝ) ≤ U (Fin.removeNth i t))
    (hwidth : ∀ r : Fin arity → ℕ, (∀ j, 0 < r j) →
      ((∏ j, r j : ℕ) : ℝ) ≤ 64 * x / x ^ ((8639 : ℝ) / 50000) →
        U r - L r ≤ η * (64 * x / ((∏ j, r j : ℕ) : ℝ))) :
    (S.card : ℝ) ≤
      64 * (η * x + x ^ (1 - (8639 : ℝ) / 50000)) *
        (1 + Real.log (64 * x)) ^ 16 := by
  classical
  let ξ : ℝ := 8639 / 50000
  let Z : ℝ := 64 * x
  let Y : ℝ := Z / x ^ ξ
  let N : ℕ := ⌊Y⌋₊
  let R : Finset (Fin arity → ℕ) := S.image (Fin.removeNth i)
  let H : ℝ := 1 + Real.log Z
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hξ0 : 0 ≤ ξ := by norm_num [ξ]
  have hξ1 : ξ ≤ 1 := by norm_num [ξ]
  have hxξ : 1 ≤ x ^ ξ := Real.one_le_rpow hx1 hξ0
  have hxξ0 : 0 < x ^ ξ := Real.rpow_pos_of_pos hx0 ξ
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hY1 : 1 ≤ Y := by
    apply (le_div_iff₀ hxξ0).mpr
    have hpow := Real.rpow_le_self_of_one_le hx1 hξ1
    dsimp [Z]
    linarith
  have hY0 : 0 ≤ Y := zero_le_one.trans hY1
  have hYZ : Y ≤ Z := div_le_self hZ.le hxξ
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa only [Nat.cast_one] using hY1)
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le hY0
  have hNZ : (N : ℝ) ≤ Z := hNY.trans hYZ
  have hH1 : 1 ≤ H := by
    have hZ1 : 1 ≤ Z := (by exact_mod_cast hN1 : (1 : ℝ) ≤ N).trans hNZ
    exact le_add_of_nonneg_right (Real.log_nonneg hZ1)
  have hlogN0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  have hlogNZ : 1 + Real.log (N : ℝ) ≤ H := by
    exact add_le_add (le_refl 1)
      (Real.log_le_log (by exact_mod_cast hN1 : (0 : ℝ) < N) hNZ)
  have hpositive (t : Fin (arity + 1) → ℕ) (ht : t ∈ S) (j : Fin (arity + 1)) : 0 < t j :=
    Nat.cast_pos.mp (hxξ0.trans_le ((hS t ht).1 j))
  have hR (r : Fin arity → ℕ) (hr : r ∈ R) :
      (∀ j, 0 < r j) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ Y := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨fun j => hpositive t ht (i.succAbove j), ?_⟩
    have hprod : (t i : ℝ) * ((∏ j, Fin.removeNth i t j : ℕ) : ℝ) =
        ((∏ j, t j : ℕ) : ℝ) := by
      exact_mod_cast Fin.mul_prod_removeNth i t
    apply (le_div_iff₀ hxξ0).mpr
    calc
      _ ≤ (t i : ℝ) * ((∏ j, Fin.removeNth i t j : ℕ) : ℝ) := by
        have hti : x ^ ξ ≤ (t i : ℝ) := (hS t ht).1 i
        exact (mul_le_mul_of_nonneg_left hti
          (Nat.cast_nonneg (∏ j, Fin.removeNth i t j))).trans_eq (mul_comm _ _)
      _ ≤ Z := hprod ▸ (hS t ht).2.1
  have hRnat : ∀ r ∈ R, (∀ j, 0 < r j) ∧ (∏ j, r j) ≤ N := by
    intro r hr
    exact ⟨(hR r hr).1, Nat.le_floor (hR r hr).2⟩
  obtain ⟨hRcard, hRrec⟩ := finite_positive_tuple_product_moments arity N R hRnat
  have hmoment : 2 ^ arity ≤ (8 : ℕ) :=
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hArity).trans_eq (by norm_num)
  have hRcard' : (R.card : ℝ) ≤ Y * H ^ 15 := by
    refine hRcard.trans ?_
    exact mul_le_mul hNY
      ((pow_le_pow_left₀ hlogN0 hlogNZ (2 ^ arity - 1)).trans
        (pow_le_pow_right₀ hH1 (by omega)))
      (pow_nonneg hlogN0 _) hY0
  have hRrec' : (∑ r ∈ R, 1 / ((∏ j, r j : ℕ) : ℝ)) ≤ H ^ 16 := by
    refine hRrec.trans ?_
    exact (pow_le_pow_left₀ hlogN0 hlogNZ (2 ^ arity)).trans
      (pow_le_pow_right₀ hH1 (by omega))
  have hfiber (r : Fin arity → ℕ) (hr : r ∈ R) :
      ((S.filter (fun t => Fin.removeNth i t = r)).card : ℝ) ≤
        η * (Z / ((∏ j, r j : ℕ) : ℝ)) + 1 := by
    let T := S.filter (fun t => Fin.removeNth i t = r)
    have hinj : Set.InjOn (fun t : Fin (arity + 1) → ℕ => t i) T := by
      intro t ht u hu htu
      change t i = u i at htu
      have htR := (Finset.mem_filter.mp ht).2
      have huR := (Finset.mem_filter.mp hu).2
      calc
        t = Fin.insertNth i (t i) (Fin.removeNth i t) :=
          (Fin.insertNth_self_removeNth i t).symm
        _ = Fin.insertNth i (u i) (Fin.removeNth i u) := by rw [htR, huR, htu]
        _ = u := Fin.insertNth_self_removeNth i u
    have hcard : (T.image (fun t => t i)).card = T.card :=
      Finset.card_image_of_injOn hinj
    rw [← hcard]
    apply finite_nat_closed_band_card_le _ (L r) (U r) _ (by positivity)
    · intro n hn
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨htS, htr⟩ := Finset.mem_filter.mp ht
      simpa only [htr] using (hS t htS).2.2
    · exact hwidth r (hR r hr).1 (hR r hr).2
  have hcount : (S.card : ℝ) ≤
      η * Z * (∑ r ∈ R, 1 / ((∏ j, r j : ℕ) : ℝ)) + (R.card : ℝ) := by
    calc
      _ = ∑ r ∈ R, ((S.filter (fun t => Fin.removeNth i t = r)).card : ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image (Fin.removeNth i) S
      _ ≤ ∑ r ∈ R, (η * (Z / ((∏ j, r j : ℕ) : ℝ)) + 1) :=
        Finset.sum_le_sum hfiber
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul, mul_one, div_eq_mul_inv, one_mul, mul_assoc]
  have hYeq : Y = 64 * x ^ (1 - ξ) := by
    dsimp [Y, Z]
    rw [Real.rpow_sub hx0, Real.rpow_one]
    ring
  have hHpow : H ^ 15 ≤ H ^ 16 := by
    exact pow_le_pow_right₀ hH1 (by norm_num)
  calc
    _ ≤ η * Z * H ^ 16 + Y * H ^ 15 :=
      hcount.trans (add_le_add
        (mul_le_mul_of_nonneg_left hRrec' (mul_nonneg hη hZ.le)) hRcard')
    _ ≤ η * Z * H ^ 16 + Y * H ^ 16 :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hHpow hY0)
    _ = _ := by rw [hYeq]; dsimp [Z, H, ξ]; ring

theorem geometric_small_monomial_comparison (h : ℝ) (hh : 0 < h)
    (p q : Fin (arity + 1) → ℕ) (hp : ∀ i, 1 ≤ p i) (hq : ∀ i, 1 ≤ q i)
    (hlabel : ∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ =
      ⌊Real.logb (1 + h) (q i : ℝ)⌋₊)
    (d : MinorantSmallMonomialCut (arity + 1)) :
    d.value p ≤ (1 + h) ^ (d.numerator.card + d.denominator.card) * d.value q ∧
    d.value q ≤ (1 + h) ^ (d.numerator.card + d.denominator.card) * d.value p := by
  have one_way (p q : Fin (arity + 1) → ℕ) (hp : ∀ i, 1 ≤ p i) (hq : ∀ i, 1 ≤ q i)
      (hlab : ∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ =
        ⌊Real.logb (1 + h) (q i : ℝ)⌋₊) :
      d.value p ≤ (1 + h) ^ (d.numerator.card + d.denominator.card) * d.value q := by
    have hp0 (i : Fin (arity + 1)) : 0 < (p i : ℝ) := by exact_mod_cast hp i
    have hq0 (i : Fin (arity + 1)) : 0 < (q i : ℝ) := by exact_mod_cast hq i
    have hnum : (∏ i ∈ d.numerator, (p i : ℝ)) ≤
        (1 + h) ^ d.numerator.card * ∏ i ∈ d.numerator, (q i : ℝ) := by
      calc
        _ ≤ ∏ i ∈ d.numerator, ((1 + h) * q i) :=
          Finset.prod_le_prod (fun i _ => (hp0 i).le)
            (fun i _ => (geometric_bin_pair_ratios h hh (p i) (q i)
              (hp i) (hq i) (hlab i)).1)
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hden : (∏ i ∈ d.denominator, (q i : ℝ)) ≤
        (1 + h) ^ d.denominator.card * ∏ i ∈ d.denominator, (p i : ℝ) := by
      calc
        _ ≤ ∏ i ∈ d.denominator, ((1 + h) * p i) :=
          Finset.prod_le_prod (fun i _ => (hq0 i).le)
            (fun i _ => (geometric_bin_pair_ratios h hh (p i) (q i)
              (hp i) (hq i) (hlab i)).2)
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hpd : 0 < ∏ i ∈ d.denominator, (p i : ℝ) :=
      Finset.prod_pos fun i _ => hp0 i
    have hqd : 0 < ∏ i ∈ d.denominator, (q i : ℝ) :=
      Finset.prod_pos fun i _ => hq0 i
    dsimp [MinorantSmallMonomialCut.value]
    rw [pow_add, ← mul_div_assoc, div_le_div_iff₀ hpd hqd]
    calc
      _ ≤ ((1 + h) ^ d.numerator.card * ∏ i ∈ d.numerator, (q i : ℝ)) *
          ((1 + h) ^ d.denominator.card * ∏ i ∈ d.denominator, (p i : ℝ)) :=
        mul_le_mul hnum hden hqd.le (by positivity)
      _ = _ := by ring
  exact ⟨one_way p q hp hq hlabel, one_way q p hq hp (fun i => (hlabel i).symm)⟩

theorem MinorantSmallMonomialCut.value_insertNth_factor (d : MinorantSmallMonomialCut (arity + 1))
    (i : Fin (arity + 1)) (hi : i ∈ d.numerator) (hid : i ∉ d.denominator)
    (p : Fin (arity + 1) → ℕ) :
    d.value p = (p i : ℝ) * d.value (i.insertNth 1 (i.removeNth p)) := by
  classical
  rw [Fin.insertNth_removeNth]
  simp only [MinorantSmallMonomialCut.value,
    Function.apply_update (fun (_ : Fin (arity + 1)) (n : ℕ) => (n : ℝ)), Nat.cast_one]
  rw [Finset.prod_update_of_mem hi, Finset.prod_update_of_notMem hid,
    one_mul, Finset.sdiff_singleton_eq_erase, ← Finset.mul_prod_erase _ _ hi]
  ring

theorem MinorantSmallMonomialCut.closed_coordinate_band (d : MinorantSmallMonomialCut (arity + 1))
    (i : Fin (arity + 1)) (hi : i ∈ d.numerator) (hid : i ∉ d.denominator)
    (p : Fin (arity + 1) → ℕ) (hp : ∀ k, 0 < p k) (R Z : ℝ) (hR : 0 < R)
    (hsupport : (p i : ℝ) ≤ Z)
    (hband : d.threshold / R ≤ d.value p ∧ d.value p ≤ d.threshold * R) :
    let t := d.threshold / d.value (i.insertNth 1 (i.removeNth p))
    t / R ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ min (t * R) Z := by
  intro t
  have hbase : ∀ k : Fin (arity + 1), 0 < (i.insertNth 1 (i.removeNth p) k : ℝ) := by
    rw [Fin.insertNth_removeNth,
      Function.forall_update_iff p (fun _ (n : ℕ) => 0 < (n : ℝ))]
    exact ⟨by norm_num, fun k _ => Nat.cast_pos.mpr (hp k)⟩
  have hv : 0 < d.value (i.insertNth 1 (i.removeNth p)) :=
    div_pos (Finset.prod_pos fun k _ => hbase k) (Finset.prod_pos fun k _ => hbase k)
  rw [d.value_insertNth_factor i hi hid p] at hband
  constructor
  · dsimp [t]
    rw [div_div, div_le_iff₀ (mul_pos hv hR)]
    have hh := (div_le_iff₀ hR).mp hband.1
    nlinarith only [hh]
  · apply le_min _ hsupport
    dsimp [t]
    rw [div_mul_eq_mul_div, le_div_iff₀ hv]
    exact hband.2

theorem geometric_small_monomial_test_crossing
    (h : ℝ) (hh : 0 < h) (d : MinorantSmallMonomialCut (arity + 1)) (hd : 0 ≤ d.threshold)
    (p q : Fin (arity + 1) → ℕ) (hp : ∀ i, 1 ≤ p i) (hq : ∀ i, 1 ≤ q i)
    (hlabel : ∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ =
      ⌊Real.logb (1 + h) (q i : ℝ)⌋₊)
    (hchange : ¬((if d.lower then
        if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
      else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
      (if d.lower then
        if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
      else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold))) :
    (d.threshold / (1 + h) ^ (d.numerator.card + d.denominator.card) ≤ d.value p ∧
      d.value p ≤ d.threshold * (1 + h) ^ (d.numerator.card + d.denominator.card)) ∧
    (d.threshold / (1 + h) ^ (d.numerator.card + d.denominator.card) ≤ d.value q ∧
      d.value q ≤ d.threshold * (1 + h) ^ (d.numerator.card + d.denominator.card)) := by
  have hcompare := geometric_small_monomial_comparison h hh p q hp hq hlabel d
  apply threshold_bands_of_crossing _ _ _ _ hd
    (one_le_pow₀ (by linarith)) hcompare.1 hcompare.2
  rw [not_iff, iff_iff_and_or_not_and_not] at hchange
  cases hl : d.lower <;> cases hs : d.strict <;>
    simp only [hl, hs, Bool.false_eq_true, ite_false, ite_true,
      not_le, not_lt] at hchange <;>
    rcases hchange with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
    first | exact Or.inl ⟨by linarith, by linarith⟩
          | exact Or.inr ⟨by linarith, by linarith⟩

open Classical in
theorem boolean_small_monomial_mixed_geometric_box_card (hArity : arity ≤ 3)
    (x h : ℝ) (hx : 2 ≤ x) (hh : 0 < h) (hh1 : h ≤ 1)
    (M : Finset (MinorantSmallMonomialCut (arity + 1))) (C : (Fin (arity + 1) → ℕ) → Prop)
    (hM : ∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
      d.numerator.card + d.denominator.card ≤ arity + 1 ∧ 0 < d.threshold) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
    let T := Fintype.piFinset (fun _ : Fin (arity + 1) => P)
    (∀ p ∈ T, ∀ q ∈ T,
      (∀ d ∈ M,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (C p ↔ C q)) →
    (∀ p ∈ T, C p → ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x) →
    let label (p : Fin (arity + 1) → ℕ) : Fin (arity + 1) → ℕ :=
      fun i => ⌊Real.logb (1 + h) (p i : ℝ)⌋₊
    let U (b : Fin (arity + 1) → ℕ) := T.filter (fun p => label p = b)
    let D := (T.image label).filter
      (fun b => (∃ p ∈ U b, C p) ∧ ¬∀ p ∈ U b, C p)
    (∑ b ∈ D, ((U b).card : ℝ)) ≤
      (M.card : ℝ) * 64 *
        (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
          (1 + Real.log (64 * x)) ^ 16 := by
  intro P T hboolean hsupport label U D
  let S := T.filter (fun q => label q ∈ D)
  let R (d : MinorantSmallMonomialCut (arity + 1)) : ℝ := (1 + h) ^
    (d.numerator.card + d.denominator.card)
  let E (d : MinorantSmallMonomialCut (arity + 1)) := S.filter
    (fun q => d.threshold / R d ≤ d.value q ∧ d.value q ≤ d.threshold * R d)
  let V : ℝ := 64 * (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
    (1 + Real.log (64 * x)) ^ 16
  have hpositive (p : Fin (arity + 1) → ℕ) (hp : p ∈ T) (i : Fin (arity + 1)) : 1 ≤ p i := by
    have hprime : (p i).Prime :=
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
    exact hprime.one_lt.le
  have hlower (p : Fin (arity + 1) → ℕ) (hp : p ∈ T) (i : Fin (arity + 1)) :
      x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) := by
    have hnat := (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).1).1
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hnat)
  have hchanged (p q : Fin (arity + 1) → ℕ) (hp : p ∈ T) (hq : q ∈ T)
      (hlab : ∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ =
        ⌊Real.logb (1 + h) (q i : ℝ)⌋₊) (hpass : C p) (hfail : ¬C q) :
      ∃ d ∈ M,
        (d.threshold / R d ≤ d.value p ∧ d.value p ≤ d.threshold * R d) ∧
        (d.threshold / R d ≤ d.value q ∧ d.value q ≤ d.threshold * R d) := by
    have hex : ∃ d ∈ M, ¬((if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) := by
      by_contra! hnone
      exact hfail ((hboolean p hp q hq hnone).mp hpass)
    obtain ⟨d, hd, hchange⟩ := hex
    exact ⟨d, hd, geometric_small_monomial_test_crossing h hh d (hM d hd).2.2.2.le
      p q (hpositive p hp) (hpositive q hq) hlab hchange⟩
  have hboundary (q : Fin (arity + 1) → ℕ) (hq : q ∈ S) :
      ((∏ i, q i : ℕ) : ℝ) ≤ 64 * x ∧
        ∃ d ∈ M, d.threshold / R d ≤ d.value q ∧ d.value q ≤ d.threshold * R d := by
    obtain ⟨hqT, hqD⟩ := Finset.mem_filter.mp hq
    have hmix := (Finset.mem_filter.mp hqD).2
    obtain ⟨p₀, hp₀, hpass⟩ := hmix.1
    have hex : ∃ p₁ ∈ U (label q), ¬C p₁ := by
      simpa only [not_forall, exists_prop] using hmix.2
    obtain ⟨p₁, hp₁, hfail⟩ := hex
    have hp₀T : p₀ ∈ T := (Finset.mem_filter.mp hp₀).1
    have hp₁T : p₁ ∈ T := (Finset.mem_filter.mp hp₁).1
    have hlab₀ (i : Fin (arity + 1)) :
        ⌊Real.logb (1 + h) (p₀ i : ℝ)⌋₊ =
          ⌊Real.logb (1 + h) (q i : ℝ)⌋₊ :=
      congrFun (Finset.mem_filter.mp hp₀).2 i
    have hlab₁ (i : Fin (arity + 1)) :
        ⌊Real.logb (1 + h) (p₁ i : ℝ)⌋₊ =
          ⌊Real.logb (1 + h) (q i : ℝ)⌋₊ :=
      congrFun (Finset.mem_filter.mp hp₁).2 i
    refine ⟨geometric_small_box_product_bound hArity h x hh hh1 p₀ q
      (hpositive p₀ hp₀T) (hpositive q hqT) hlab₀ (hsupport p₀ hp₀T hpass), ?_⟩
    by_cases hqpass : C q
    · obtain ⟨d, hd, hb, _⟩ := hchanged q p₁ hqT hp₁T
        (fun i => (hlab₁ i).symm) hqpass hfail
      exact ⟨d, hd, hb⟩
    · obtain ⟨d, hd, _, hb⟩ := hchanged p₀ q hp₀T hqT hlab₀ hpass hqpass
      exact ⟨d, hd, hb⟩
  have hE (d : MinorantSmallMonomialCut (arity + 1)) (hd : d ∈ M) : ((E d).card : ℝ) ≤ V := by
    have hdata := hM d hd
    obtain ⟨i, hi⟩ := hdata.1
    have hid : i ∉ d.denominator := fun hb => Finset.disjoint_left.mp hdata.2.1 hi hb
    have hR : 1 ≤ R d := one_le_pow₀ (by linarith)
    have hR0 : 0 < R d := zero_lt_one.trans_le hR
    let t (r : Fin arity → ℕ) := d.threshold / d.value (i.insertNth 1 r)
    let L (r : Fin arity → ℕ) := t r / R d
    let U₀ (r : Fin arity → ℕ) := min (t r * R d) (64 * x / ((∏ k, r k : ℕ) : ℝ))
    have hwidth (r : Fin arity → ℕ) (hr : ∀ k, 0 < r k) :
        U₀ r - L r ≤ (1023 * h) * (64 * x / ((∏ k, r k : ℕ) : ℝ)) := by
      have hbase : ∀ k : Fin (arity + 1),
          0 < ((Fin.insertNth (α := fun _ : Fin (arity + 1) => ℕ) i 1 r k : ℕ) : ℝ) := by
        rw [Fin.forall_iff_succAbove i]
        simpa using hr
      have ht : 0 ≤ t r :=
        div_nonneg hdata.2.2.2.le
          (div_nonneg (Finset.prod_nonneg fun k _ => (hbase k).le)
            (Finset.prod_nonneg fun k _ => (hbase k).le))
      have hZ : 0 ≤ 64 * x / ((∏ k, r k : ℕ) : ℝ) := by positivity
      exact (monomial_clipped_band_width (t r) (R d) _ ht hR hZ).trans
        (mul_le_mul_of_nonneg_right
          (geometric_degree_five_width h hh.le hh1 _
            (hdata.2.2.1.trans (by omega))) hZ)
    apply finite_small_tuple_monomial_boundary_count hArity x (1023 * h) hx (by positivity)
      i (E d) L U₀
    · intro q hq
      obtain ⟨hqS, hband⟩ := Finset.mem_filter.mp hq
      have hqT := (Finset.mem_filter.mp hqS).1
      have hco : 0 < ((∏ k, i.removeNth q k : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos fun k _ =>
          zero_lt_one.trans_le (hpositive q hqT (i.succAbove k))
      have hsupport : (q i : ℝ) ≤ 64 * x / ((∏ k, i.removeNth q k : ℕ) : ℝ) := by
        rw [le_div_iff₀ hco]
        have heq : (q i : ℝ) * ((∏ k, i.removeNth q k : ℕ) : ℝ) =
            ((∏ k, q k : ℕ) : ℝ) := by exact_mod_cast Fin.mul_prod_removeNth i q
        rw [heq]
        exact (hboundary q hqS).1
      exact ⟨hlower q hqT, (hboundary q hqS).1,
        d.closed_coordinate_band i hi hid q
          (fun k => zero_lt_one.trans_le (hpositive q hqT k))
          (R d) _ hR0 hsupport hband⟩
    · intro r hr _hprod
      exact hwidth r hr
  have hcover : S ⊆ M.biUnion E := by
    intro q hq
    obtain ⟨d, hd, hband⟩ := (hboundary q hq).2
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hq, hband⟩⟩
  have hcard : (S.card : ℝ) = ∑ b ∈ D, ((U b).card : ℝ) := by
    have hc : S.card = ∑ b ∈ D, (U b).card := by
      calc
        _ = ∑ b ∈ D, (S.filter (fun q => label q = b)).card :=
          Finset.card_eq_sum_card_fiberwise (fun q hq => (Finset.mem_filter.mp hq).2)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b hb
          congr 1
          ext q
          by_cases heq : label q = b <;> simp [S, U, heq, hb]
    exact_mod_cast hc
  rw [← hcard]
  calc
    _ ≤ ∑ d ∈ M, ((E d).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ M, V := Finset.sum_le_sum hE
    _ = (M.card : ℝ) * V := by simp
    _ = _ := by dsimp [V]; ring

#print axioms small_prime_geometric_bin_eq_closed_interval
#print axioms small_prime_geometric_active_scales
#print axioms small_prime_geometric_box_card_polylog
#print axioms small_prime_geometric_central_scales
#print axioms finite_small_tuple_monomial_boundary_count
#print axioms boolean_small_monomial_mixed_geometric_box_card

end PrimeGap182Analytic.Harman
