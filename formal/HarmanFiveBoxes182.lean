import HarmanPrimeBox182
import HarmanBoundaryArithmetic182

/-! Actual five-prime Boolean boxes for the new minorant. The allowed prime
band is [.17278,.31], and a selected pair or triple lies in [.41361,.58639].
Boundary cardinality, central factor selection, and subpower modulus retreat
are proved here. Distribution is explicitly derived from SourceBilinearEstimate.
Adapted from Apache-2.0 PrimeGaps186 at the generator's checked source hash. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem finite_five_tuple_monomial_boundary_count
    (x η : ℝ) (hx : 2 ≤ x) (hη : 0 ≤ η) (i : Fin 5)
    (S : Finset (Fin 5 → ℕ)) (L U : (Fin 4 → ℕ) → ℝ)
    (hS : ∀ t ∈ S,
      (∀ j, x ^ ((8639 : ℝ) / 50000) ≤ (t j : ℝ)) ∧
        ((∏ j, t j : ℕ) : ℝ) ≤ 64 * x ∧
        L (Fin.removeNth i t) ≤ (t i : ℝ) ∧
        (t i : ℝ) ≤ U (Fin.removeNth i t))
    (hwidth : ∀ r : Fin 4 → ℕ, (∀ j, 0 < r j) →
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
  let R : Finset (Fin 4 → ℕ) := S.image (Fin.removeNth i)
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
  have hpositive (t : Fin 5 → ℕ) (ht : t ∈ S) (j : Fin 5) : 0 < t j :=
    Nat.cast_pos.mp (hxξ0.trans_le ((hS t ht).1 j))
  have hR (r : Fin 4 → ℕ) (hr : r ∈ R) :
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
  obtain ⟨hRcard, hRrec⟩ := finite_positive_tuple_product_moments 4 N R hRnat
  have hRcard' : (R.card : ℝ) ≤ Y * H ^ 15 := by
    refine hRcard.trans ?_
    norm_num only [show 2 ^ (4 : ℕ) - 1 = 15 by norm_num]
    exact mul_le_mul hNY (pow_le_pow_left₀ hlogN0 hlogNZ 15)
      (pow_nonneg hlogN0 _) hY0
  have hRrec' : (∑ r ∈ R, 1 / ((∏ j, r j : ℕ) : ℝ)) ≤ H ^ 16 := by
    refine hRrec.trans ?_
    norm_num only [show 2 ^ (4 : ℕ) = 16 by norm_num]
    exact pow_le_pow_left₀ hlogN0 hlogNZ 16
  have hfiber (r : Fin 4 → ℕ) (hr : r ∈ R) :
      ((S.filter (fun t => Fin.removeNth i t = r)).card : ℝ) ≤
        η * (Z / ((∏ j, r j : ℕ) : ℝ)) + 1 := by
    let T := S.filter (fun t => Fin.removeNth i t = r)
    have hinj : Set.InjOn (fun t : Fin 5 → ℕ => t i) T := by
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

theorem compact_prime_geometric_bin_eq_closed_interval
    (x h : ℝ) (hx : 0 < x) (hh : 0 < h) (k : ℕ) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
    let L : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ k)
    let U : ℝ := min (x ^ ((31 : ℝ) / 100))
      ((⌈(1 + h) ^ (k + 1)⌉₊ - 1 : ℕ) : ℝ)
    P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = k) =
      (Finset.Icc ⌈L⌉₊ ⌊U⌋₊).filter Nat.Prime := by
  classical
  intro P L U
  have hpow : 0 ≤ x ^ ((31 : ℝ) / 100) := (Real.rpow_pos_of_pos hx _).le
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

theorem compact_prime_geometric_active_scales
    (x h : ℝ) (hx : 2 ≤ x) (hh : 0 < h) (hh1 : h ≤ 1)
    (b p : Fin 5 → ℕ) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
    let L (i : Fin 5) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
    let U (i : Fin 5) : ℝ := min (x ^ ((31 : ℝ) / 100))
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
  have hL (i : Fin 5) : 0 ≤ L i :=
    (Real.rpow_pos_of_pos hx0 _).le.trans (le_max_left _ _)
  have hpLU (i : Fin 5) : L i ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ U i := by
    have hm : p i ∈ P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = b i) :=
      Finset.mem_filter.mpr ⟨hp i, hlabel i⟩
    rw [compact_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)] at hm
    have hm' := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    exact ⟨Nat.le_of_ceil_le hm'.1,
      (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (by positivity))⟩
  have hU (i : Fin 5) : U i ≤ 2 * L i := by
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
      _ = _ := by rw [Finset.prod_mul_distrib]; norm_num
  refine ⟨?_, ?_, hupper⟩
  · intro i
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num :
      (1 : ℝ) / 10 ≤ (8639 : ℝ) / 50000)).trans (le_max_left _ _),
      (hpLU i).1.trans (hpLU i).2, hU i⟩
  · linarith [hproduct.1, hcompare]

theorem compact_prime_geometric_central_scales (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, 0 < h → h ≤ 1 / 4 → ∀ b p : Fin 5 → ℕ,
      let P : Finset ℕ :=
        (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
          ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
      let L (i : Fin 5) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
      let U (i : Fin 5) : ℝ := min (x ^ ((31 : ℝ) / 100))
        ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ)
      (∀ i, p i ∈ P) →
      (∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ = b i) →
      (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
      ∀ S : Finset (Fin 5), (S.card = 2 ∨ S.card = 3) →
        x ^ ((41361 : ℝ) / 100000) ≤ ∏ i ∈ S, (p i : ℝ) →
        (∏ i ∈ S, (p i : ℝ)) ≤ x ^ ((58639 : ℝ) / 100000) →
        ∃ R : Finset (Fin 5), ∃ Y : Fin 5 → ℝ,
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
  intro h hh hh4 b p P L U hp hlabel hprod S hcard hcentralLo hcentralHi
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hbase : 0 < 1 + h := by linarith
  have hscales := compact_prime_geometric_active_scales x h hx hh (by linarith)
    b p hp hlabel hprod
  have hLpos (i : Fin 5) : 0 < L i :=
    (Real.rpow_pos_of_pos hx0 _).trans_le (le_max_left _ _)
  have hpLU (i : Fin 5) : L i ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ U i := by
    have hm : p i ∈ P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = b i) :=
      Finset.mem_filter.mpr ⟨hp i, hlabel i⟩
    rw [compact_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)] at hm
    have hm' := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    exact ⟨Nat.le_of_ceil_le hm'.1,
      (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (by positivity))⟩
  have hUnarrow (i : Fin 5) : U i ≤ (4 / 3 : ℝ) * L i := by
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
  have hSnon : S.Nonempty := Finset.card_pos.mp (by rcases hcard with h | h <;> omega)
  have hSne : S ≠ Finset.univ := by
    intro heq
    have hc : S.card = 5 := by simp [heq]
    rcases hcard with h | h <;> omega
  have hsubcompare (T : Finset (Fin 5)) :
      (∏ i ∈ T, (p i : ℝ)) ≤ 32 * ∏ i ∈ T, L i := by
    have hT : T.card ≤ 5 := by
      simpa using (Finset.card_le_card (Finset.subset_univ T))
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
    central_box_one_coordinate_scales x hx0.le L U hLpos
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

open Classical in
theorem compact_prime_geometric_box_card_polylog
    (D x : ℝ) (hD : 0 ≤ D) (hx : Real.exp 1 ≤ x) :
    let h := (Real.log x) ^ (-D)
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
    let T := Fintype.piFinset (fun _ : Fin 5 => P)
    let label (p : Fin 5 → ℕ) : Fin 5 → ℕ :=
      fun i => ⌊Real.logb (1 + h) (p i : ℝ)⌋₊
    ((T.image label).card : ℝ) ≤
      (6 : ℝ) ^ 5 * (Real.log x) ^ (5 * (D + 1)) := by
  intro h P T label
  have hmesh := geometric_log_mesh_spec D x hD hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  let K : ℕ := ⌈Real.logb (1 + h) (2 * x)⌉₊ + 1
  have hK (n : ℕ) (hn : n ∈ P) : ⌊Real.logb (1 + h) (n : ℝ)⌋₊ < K := by
    obtain ⟨hnI, hnprime⟩ := Finset.mem_filter.mp hn
    have hupper : (n : ℝ) ≤ 2 * x := by
      calc
        _ ≤ x ^ ((31 : ℝ) / 100) :=
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hnI).2).trans
            (Nat.floor_le (Real.rpow_pos_of_pos hx0 _).le)
        _ ≤ x := Real.rpow_le_self_of_one_le hx1 (by norm_num)
        _ ≤ 2 * x := by linarith
    exact geometric_bin_label_bound h x hmesh.1 n hnprime.one_lt.le hupper
  have hcard : (T.image label).card ≤ K ^ 5 :=
    (finite_five_prime_box_cut_decomposition P
      (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊) (fun _ => True)).2.2.1 K hK
  exact (show ((T.image label).card : ℝ) ≤ (K : ℝ) ^ 5 by exact_mod_cast hcard).trans
    hmesh.2.2

open Classical in
theorem boolean_monomial_mixed_geometric_box_card
    (x h : ℝ) (hx : 2 ≤ x) (hh : 0 < h) (hh1 : h ≤ 1)
    (M : Finset MinorantMonomialCut) (C : (Fin 5 → ℕ) → Prop)
    (hM : ∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
      d.numerator.card + d.denominator.card ≤ 5 ∧ 0 < d.threshold) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
    let T := Fintype.piFinset (fun _ : Fin 5 => P)
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
    let label (p : Fin 5 → ℕ) : Fin 5 → ℕ :=
      fun i => ⌊Real.logb (1 + h) (p i : ℝ)⌋₊
    let U (b : Fin 5 → ℕ) := T.filter (fun p => label p = b)
    let D := (T.image label).filter
      (fun b => (∃ p ∈ U b, C p) ∧ ¬∀ p ∈ U b, C p)
    (∑ b ∈ D, ((U b).card : ℝ)) ≤
      (M.card : ℝ) * 64 *
        (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
          (1 + Real.log (64 * x)) ^ 16 := by
  intro P T hboolean hsupport label U D
  let S := T.filter (fun q => label q ∈ D)
  let R (d : MinorantMonomialCut) : ℝ := (1 + h) ^
    (d.numerator.card + d.denominator.card)
  let E (d : MinorantMonomialCut) := S.filter
    (fun q => d.threshold / R d ≤ d.value q ∧ d.value q ≤ d.threshold * R d)
  let V : ℝ := 64 * (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
    (1 + Real.log (64 * x)) ^ 16
  have hpositive (p : Fin 5 → ℕ) (hp : p ∈ T) (i : Fin 5) : 1 ≤ p i := by
    have hprime : (p i).Prime :=
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
    exact hprime.one_lt.le
  have hlower (p : Fin 5 → ℕ) (hp : p ∈ T) (i : Fin 5) :
      x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) := by
    have hnat := (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).1).1
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hnat)
  have hchanged (p q : Fin 5 → ℕ) (hp : p ∈ T) (hq : q ∈ T)
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
    exact ⟨d, hd, geometric_monomial_test_crossing h hh d (hM d hd).2.2.2.le
      p q (hpositive p hp) (hpositive q hq) hlab hchange⟩
  have hboundary (q : Fin 5 → ℕ) (hq : q ∈ S) :
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
    have hlab₀ (i : Fin 5) :
        ⌊Real.logb (1 + h) (p₀ i : ℝ)⌋₊ =
          ⌊Real.logb (1 + h) (q i : ℝ)⌋₊ :=
      congrFun (Finset.mem_filter.mp hp₀).2 i
    have hlab₁ (i : Fin 5) :
        ⌊Real.logb (1 + h) (p₁ i : ℝ)⌋₊ =
          ⌊Real.logb (1 + h) (q i : ℝ)⌋₊ :=
      congrFun (Finset.mem_filter.mp hp₁).2 i
    refine ⟨geometric_five_box_product_bound h x hh hh1 p₀ q
      (hpositive p₀ hp₀T) (hpositive q hqT) hlab₀ (hsupport p₀ hp₀T hpass), ?_⟩
    by_cases hqpass : C q
    · obtain ⟨d, hd, hb, _⟩ := hchanged q p₁ hqT hp₁T
        (fun i => (hlab₁ i).symm) hqpass hfail
      exact ⟨d, hd, hb⟩
    · obtain ⟨d, hd, _, hb⟩ := hchanged p₀ q hp₀T hqT hlab₀ hpass hqpass
      exact ⟨d, hd, hb⟩
  have hE (d : MinorantMonomialCut) (hd : d ∈ M) : ((E d).card : ℝ) ≤ V := by
    have hdata := hM d hd
    obtain ⟨i, hi⟩ := hdata.1
    have hid : i ∉ d.denominator := fun hb => Finset.disjoint_left.mp hdata.2.1 hi hb
    have hR : 1 ≤ R d := one_le_pow₀ (by linarith)
    have hR0 : 0 < R d := zero_lt_one.trans_le hR
    let t (r : Fin 4 → ℕ) := d.threshold / d.value (i.insertNth 1 r)
    let L (r : Fin 4 → ℕ) := t r / R d
    let U₀ (r : Fin 4 → ℕ) := min (t r * R d) (64 * x / ((∏ k, r k : ℕ) : ℝ))
    have hwidth (r : Fin 4 → ℕ) (hr : ∀ k, 0 < r k) :
        U₀ r - L r ≤ (1023 * h) * (64 * x / ((∏ k, r k : ℕ) : ℝ)) := by
      have hbase : ∀ k : Fin 5,
          0 < ((Fin.insertNth (α := fun _ : Fin 5 => ℕ) i 1 r k : ℕ) : ℝ) := by
        rw [Fin.forall_iff_succAbove i]
        simpa using hr
      have ht : 0 ≤ t r :=
        div_nonneg hdata.2.2.2.le
          (div_nonneg (Finset.prod_nonneg fun k _ => (hbase k).le)
            (Finset.prod_nonneg fun k _ => (hbase k).le))
      have hZ : 0 ≤ 64 * x / ((∏ k, r k : ℕ) : ℝ) := by positivity
      exact (monomial_clipped_band_width (t r) (R d) _ ht hR hZ).trans
        (mul_le_mul_of_nonneg_right
          (geometric_degree_five_width h hh.le hh1 _ hdata.2.2.1) hZ)
    apply finite_five_tuple_monomial_boundary_count x (1023 * h) hx (by positivity)
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

open Classical in
theorem central_five_prime_boolean_cut_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hωupper : «ω» < 1 / 4)
    (hsource : SourceBilinearEstimate j «ω» δ σ) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ M : Finset MinorantMonomialCut, ∀ C : (Fin 5 → ℕ) → Prop,
      M.card ≤ 32 →
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 5 ∧ 0 < d.threshold) →
      let P : Finset ℕ :=
        (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
          ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 5 => P)
      (∀ p ∈ T, ∀ q ∈ T,
        (∀ d ∈ M,
          (if d.lower then
            if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
          else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
          (if d.lower then
            if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
          else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
        (C p ↔ C q)) →
      (∀ p ∈ T, C p →
        (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        ∃ S : Finset (Fin 5), (S.card = 2 ∨ S.card = 3) ∧
          x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
          ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000)) →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ :=
          ∑ p ∈ T, Finsupp.single (∏ i, p i) (if C p then 1 else 0)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧
            Nonempty (DenseDivisibilityWitness
              ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  intro A hA
  let τ : ℝ := σ - (1 / 2 - 41361 / 100000)
  have hτ : 0 < τ := sub_pos.mpr hσgap
  have hσ : 0 < σ := by linarith
  let θ : ℝ := 1 / 2 + 2 * «ω»
  have hθ0 : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  let D : ℝ := A + 20
  let E : ℝ := 5 * (D + 1)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨Kb, Xb, hKb, hXb, hbox⟩ :=
    central_prime_box_typeII_coherent_log_saving_of_bilinear j 5 «ω» δ σ
      (8639 / 100000) 64 hω hδ hσ (by norm_num) (by norm_num) hsource
      (A + E) (by linarith)
  obtain ⟨Xc, hXc⟩ := Filter.eventually_atTop.mp
    (compact_prime_geometric_central_scales τ hτ)
  obtain ⟨Xs, hXs⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (A + 18)
      (by norm_num : (0 : ℝ) < 8639 / 50000)).eventuallyLE)
  let C0 : ℝ := 2 + Real.log 64
  let Cb : ℝ := 8 * (17 * 64) * (1023 + 1) * C0 ^ 16
  let K : ℝ := (6 : ℝ) ^ 5 * Kb + 32 * Cb
  have hC0 : 0 < C0 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 64)
    dsimp only [C0]
    linarith
  have hK : 0 < K := by dsimp only [K, Cb]; positivity
  refine ⟨K, max Xb (max Xc Xs), hK, hXb.trans (le_max_left _ _), ?_⟩
  intro x hx M C hMcard hM P T hboolean hsupport I hI a ha F Q
  have hxb : Xb ≤ x := (le_max_left _ _).trans hx
  have hxc : Xc ≤ x := (le_max_left Xc Xs).trans ((le_max_right _ _).trans hx)
  have hxs : Xs ≤ x := (le_max_right Xc Xs).trans ((le_max_right _ _).trans hx)
  have hx100 : Real.exp 100 ≤ x := hXb.trans hxb
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx100
  have hx2 : 2 ≤ x := by
    have := Real.add_one_le_exp (100 : ℝ)
    linarith
  have hx1 : 1 ≤ x := by linarith
  have hxexp : Real.exp 1 ≤ x :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 100)).trans hx100
  have hlog100 : 100 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx100
  have hlog1 : 1 ≤ Real.log x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  let l : ℝ := Real.log x
  let h : ℝ := l ^ (-D)
  let bin (p : ℕ) := ⌊Real.logb (1 + h) (p : ℝ)⌋₊
  let label (p : Fin 5 → ℕ) : Fin 5 → ℕ := fun i => bin (p i)
  let B := T.image label
  let U (b : Fin 5 → ℕ) := T.filter (fun p => label p = b)
  let V := B.filter (fun b => ∃ p ∈ U b, C p)
  let W := V.filter (fun b => ¬∀ p ∈ U b, C p)
  let Fbox (b : Fin 5 → ℕ) : ℕ →₀ ℂ :=
    ∑ p ∈ U b, Finsupp.single (∏ i, p i) 1
  have hmesh := geometric_log_mesh_spec D x hD hxexp
  have hh : 0 < h := hmesh.1
  have hh1 : h ≤ 1 := hmesh.2.1
  have hhquarter : h ≤ 1 / 4 := by
    calc
      h ≤ l ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by dsimp only [D]; linarith)
      _ = 1 / l := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by dsimp only [l]; linarith)
  have hcardB : (B.card : ℝ) ≤ (6 : ℝ) ^ 5 * l ^ E :=
    compact_prime_geometric_box_card_polylog D x hD hxexp
  have hcardV : (V.card : ℝ) ≤ (6 : ℝ) ^ 5 * l ^ E :=
    (Nat.cast_le.mpr (Finset.card_filter_le B _)).trans hcardB
  have hBbound (b : Fin 5 → ℕ) (hb : b ∈ V) :
      (∑ q ∈ Q, ‖fullDiscrepancy (Fbox b) q a‖) ≤ Kb * x / l ^ (A + E) := by
    obtain ⟨p, hp, hCp⟩ := (Finset.mem_filter.mp hb).2
    have hpT := (Finset.mem_filter.mp hp).1
    have hlabel := (Finset.mem_filter.mp hp).2
    obtain ⟨hprod, S, hS, hSlo, hShi⟩ := hsupport p hpT hCp
    let Lb (i : Fin 5) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
    let Rb (i : Fin 5) : ℝ := min (x ^ ((31 : ℝ) / 100))
      ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ)
    obtain ⟨R, Y, _hRS, hRne, hRproper, hY, hcuts, hYlo, hYhi, hNlo, hNhi⟩ :=
      hXc x hxc h hh hhquarter b p (Fintype.mem_piFinset.mp hpT)
        (fun i => congrFun hlabel i) hprod S hS
        (by simpa only [Nat.cast_prod] using hSlo)
        (by simpa only [Nat.cast_prod] using hShi)
    have hexponent : (41361 : ℝ) / 100000 - τ = 1 / 2 - σ := by
      dsimp only [τ]
      ring
    rw [hexponent] at hNlo
    have hU : U b = Fintype.piFinset (fun i : Fin 5 =>
        (Finset.Icc ⌈Lb i⌉₊ ⌊Rb i⌋₊).filter Nat.Prime) := by
      have hboxes := (finite_five_prime_box_cut_decomposition P bin C).1 b
      change U b = Fintype.piFinset (fun i : Fin 5 => P.filter (fun p => bin p = b i)) at hboxes
      rw [hboxes]
      congr 1
      funext i
      exact compact_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)
    have hcoeff : (primeIntervalBoxAlgebra Lb Rb Finset.univ).coeff = Fbox b := by
      simpa only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Fbox, hU] using
        congrArg (fun f : MonoidAlgebra ℂ ℕ => f.coeff)
          (primeIntervalBoxAlgebra_univ_eq_tuple_sum Lb Rb)
    have hb' := hbox x hxb Y Lb Rb R hRne hRproper hY hcuts hYlo hYhi
      hNlo hNhi I hI a ha
    rw [hcoeff] at hb'
    exact hb'
  have hinterior :
      (∑ b ∈ V, ∑ q ∈ Q, ‖fullDiscrepancy (Fbox b) q a‖) ≤
        (6 : ℝ) ^ 5 * Kb * x / l ^ A := by
    calc
      _ ≤ ∑ b ∈ V, Kb * x / l ^ (A + E) := Finset.sum_le_sum hBbound
      _ = (V.card : ℝ) * (Kb * x / l ^ (A + E)) := by simp
      _ ≤ ((6 : ℝ) ^ 5 * l ^ E) * (Kb * x / l ^ (A + E)) :=
        mul_le_mul_of_nonneg_right hcardV (by positivity)
      _ = _ := by
        dsimp only [l]
        rw [Real.rpow_add hlog0]
        field_simp [(Real.rpow_pos_of_pos hlog0 A).ne',
          (Real.rpow_pos_of_pos hlog0 E).ne']
  have hW : W = B.filter
      (fun b => (∃ p ∈ U b, C p) ∧ ¬∀ p ∈ U b, C p) := by
    ext b
    simp only [W, V, Finset.mem_filter, and_assoc]
  have hmass : (∑ b ∈ W, ((U b).card : ℝ)) ≤
      (M.card : ℝ) * 64 * (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
        (1 + Real.log (64 * x)) ^ 16 := by
    rw [hW]
    apply boolean_monomial_mixed_geometric_box_card x h hx2 hh hh1 M C hM hboolean
    intro p hp hCp
    exact (Nat.cast_le.mpr (Finset.mem_Icc.mp (hsupport p hp hCp).1).2).trans
      (Nat.floor_le (by positivity))
  have hQsub : Q ⊆ Finset.Icc 1 ⌊x ^ θ⌋₊ := Finset.filter_subset _ _
  clear_value P bin Q
  have hφsum : (∑ q ∈ Q, 1 / (q.totient : ℝ)) ≤ 4 * l ^ 2 := by
    let Q₀ := Finset.Icc 1 ⌊x ^ θ⌋₊
    have hq1 : 1 ≤ ⌊x ^ θ⌋₊ :=
      Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_rpow hx1 hθ0.le)
    have hqx : (⌊x ^ θ⌋₊ : ℝ) ≤ x :=
      (Nat.floor_le (Real.rpow_nonneg hx0.le θ)).trans
        (Real.rpow_le_self_of_one_le hx1 hθ1.le)
    have hlogQ : Real.log (⌊x ^ θ⌋₊ : ℝ) ≤ l :=
      Real.log_le_log (by exact_mod_cast zero_lt_one.trans_le hq1) hqx
    have hmoment : (∑ q ∈ Q₀, 1 / (q.totient : ℝ)) ≤
        (harmonic ⌊x ^ θ⌋₊ : ℝ) ^ 2 := by
      calc
        _ ≤ ∑ q ∈ Q₀, (q.divisors.card : ℝ) / (q : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
          have ht := div_totient_le_card_divisors q
          calc
            1 / (q.totient : ℝ) = ((q : ℝ) / (q.totient : ℝ)) / q := by
              field_simp [hq0.ne']
            _ ≤ _ := div_le_div_of_nonneg_right ht hq0.le
        _ ≤ ∑ q ∈ Q₀,
            (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 2) q : ℝ) / (q : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
          have ht := card_divisors_pow_le_zeta_pow 1 q
            (Finset.mem_Icc.mp hq).1
          norm_num only [pow_one, pow_one] at ht
          exact_mod_cast ht
        _ ≤ _ := sum_zeta_pow_div_le_harmonic_pow 2 _
    have hH : (harmonic ⌊x ^ θ⌋₊ : ℝ) ≤ 2 * l := by
      have ht := (harmonic_le_one_add_log ⌊x ^ θ⌋₊).trans (add_le_add (le_refl 1) hlogQ)
      dsimp only [l] at *
      linarith
    have hsub : Q ⊆ Q₀ := hQsub
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => by positivity)).trans
      (hmoment.trans ((pow_le_pow_left₀ (by unfold harmonic; positivity) hH 2).trans_eq
        (by ring)))
  have hsmallx : l ^ (A + 18) ≤ x ^ ((8639 : ℝ) / 50000) := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlog0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), l] using hXs x hxs
  have hmassScaled : (∑ b ∈ W, ((U b).card : ℝ)) / 32 ≤
      17 * 64 * (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
        (1 + Real.log (64 * x)) ^ 16 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    have hcount : (M.card : ℝ) ≤ 32 := by exact_mod_cast hMcard
    have hz : 0 ≤ 64 * (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
        (1 + Real.log (64 * x)) ^ 16 := by positivity
    nlinarith only [hmass, mul_le_mul_of_nonneg_right hcount hz, hz]
  have hboundary :
      2 * (∑ b ∈ W, ((U b).card : ℝ)) * (∑ q ∈ Q, 1 / (q.totient : ℝ)) ≤
        (32 * Cb) * x / l ^ A := by
    have hmassNonneg : 0 ≤ ∑ b ∈ W, ((U b).card : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hφNonneg : 0 ≤ ∑ q ∈ Q, 1 / (q.totient : ℝ) :=
      Finset.sum_nonneg fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
    have hb := minorant_boundary_log_arithmetic A x
      ((∑ b ∈ W, ((U b).card : ℝ)) / 32) (∑ q ∈ Q, 1 / (q.totient : ℝ))
      hA hxexp (div_nonneg hmassNonneg (by norm_num)) hφNonneg hmassScaled hφsum hsmallx
    calc
      _ = 32 * (2 * ((∑ b ∈ W, ((U b).card : ℝ)) / 32) *
          (∑ q ∈ Q, 1 / (q.totient : ℝ))) := by ring
      _ ≤ 32 * (Cb * x / l ^ A) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  have harith : (6 : ℝ) ^ 5 * Kb * x / l ^ A +
      (32 * Cb) * x / l ^ A = K * x / l ^ A := by
    dsimp only [K]
    ring
  have hcover := finite_five_prime_box_discrepancy_cover P bin C Q (fun _ => a)
  exact hcover.trans ((add_le_add hinterior hboundary).trans_eq harith)

open Classical in
theorem central_five_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ M : Finset MinorantMonomialCut, ∀ C : (Fin 5 → ℕ) → Prop,
      M.card ≤ 32 →
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 5 ∧ 0 < d.threshold) →
      let P : Finset ℕ :=
        (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
          ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 5 => P)
      (∀ p ∈ T, ∀ q ∈ T,
        (∀ d ∈ M,
          (if d.lower then
            if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
          else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
          (if d.lower then
            if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
          else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
        (C p ↔ C q)) →
      (∀ p ∈ T, C p →
        (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        ∃ S : Finset (Fin 5), (S.card = 2 ∨ S.card = 3) ∧
          x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
          ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000)) →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ :=
          ∑ p ∈ T, Finsupp.single (∏ i, p i) (if C p then 1 else 0)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧
            Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  obtain ⟨r, hr, hωupper, hsource⟩ := hretreat
  obtain ⟨Xr, hXr⟩ := eventually_atTop.mp
    (central_subpower_modulus_family_subset j «ω» δ r hr L0 hL0 hL0sub)
  intro A hA
  obtain ⟨K, Xp, hK, hXp, hp⟩ :=
    central_five_prime_boolean_cut_coherent_log_saving_of_bilinear j («ω» + r) (δ + r) σ
      (by linarith) (by linarith) hσgap hωupper hsource A hA
  refine ⟨K, max Xp Xr, hK, hXp.trans (le_max_left _ _), ?_⟩
  intro x hx Y hY M C hMcard hM P T hboolean hsupport I hI a ha F Q
  have hxp : Xp ≤ x := (le_max_left _ _).trans hx
  have hxr : Xr ≤ x := (le_max_right _ _).trans hx
  have hsubset := hXr x hxr Y hY I
  have hbound := hp x hxp M C hMcard hM hboolean hsupport I hI a ha
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun q _ _ => norm_nonneg (fullDiscrepancy F q a))).trans hbound

#print axioms finite_five_tuple_monomial_boundary_count
#print axioms compact_prime_geometric_active_scales
#print axioms compact_prime_geometric_central_scales
#print axioms boolean_monomial_mixed_geometric_box_card
#print axioms central_five_prime_boolean_cut_coherent_log_saving_of_bilinear
#print axioms central_five_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear

end PrimeGap182Analytic.Harman
