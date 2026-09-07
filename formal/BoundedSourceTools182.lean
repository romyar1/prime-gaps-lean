import BandDiscrepancy182

/-! Divisor-weight and finite-shift transfers for the literal three sieve
weights. These lemmas use only boundedness of the arithmetic function and
the stated unweighted estimate; they introduce no analytic axiom. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic

open Classical in
def selbergClosedSequence182 (w : Fin 3) (x : ℝ) : ℕ →₀ ℂ :=
  ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    Finsupp.single n (selbergWeight182 w x n : ℂ)

theorem selbergWeight182_norm_le (w : Fin 3) (x : ℝ) (n : ℕ) :
    ‖(selbergWeight182 w x n : ℂ)‖ ≤ 25 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using selbergWeight182_abs_le w x n

theorem selbergClosedSequence182_support_and_envelope (w : Fin 3) (x : ℝ) (hx : 1 < x) :
    (∀ n ∈ (selbergClosedSequence182 w x).support, 0 < n ∧ (n : ℝ) ≤ 2 * x) ∧
    (∀ n ∈ (selbergClosedSequence182 w x).support,
      ‖selbergClosedSequence182 w x n‖ ≤ 25) := by
  classical
  let T := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  have hvalue (n : ℕ) : selbergClosedSequence182 w x n =
      if n ∈ T then (selbergWeight182 w x n : ℂ) else 0 := by
    simp only [selbergClosedSequence182, T, Finsupp.finsetSum_apply,
      Finsupp.single_apply, Finset.sum_ite_eq']
  have hmem (n : ℕ) (hn : n ∈ (selbergClosedSequence182 w x).support) : n ∈ T := by
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hn) (by rw [hvalue, ite_eq_right hnot])
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (hmem n hn)
    have hx0 : 0 < x := zero_lt_one.trans hx
    exact ⟨Nat.cast_pos.mp (hx0.trans_le ((Nat.le_ceil x).trans (Nat.cast_le.mpr hlo))),
      (Nat.cast_le.mpr hhi).trans (Nat.floor_le (by positivity))⟩
  · intro n hn
    rw [hvalue, ite_eq_left (hmem n hn)]
    exact selbergWeight182_norm_le w x n

theorem selbergWeight_divisor_weight_log_growth
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (J : ℕ) :
    ∃ P : ℕ, ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ w : Fin 3,
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 ⌊x ^ θ⌋₊ →
      ∀ a : ℕ → ℕ, (∀ q ∈ S, Nat.Coprime (a q) q) →
        (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖) ≤
            K * x * (Real.log x) ^ P := by
  obtain ⟨P, Kg, hKg, hgrowth⟩ :=
    weighted_fullDiscrepancy_positiveSupport_log_growth
      θ hθ0 hθ1 0 J 0 2 (by norm_num)
  refine ⟨P, Kg * 25, Real.exp 1, by positivity,
    Real.one_lt_exp_iff.mpr zero_lt_one, ?_⟩
  intro x hx w S hS a ha
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx
  have henv := selbergClosedSequence182_support_and_envelope w x hx1
  have hg := hgrowth x hx 25 (by norm_num) S hS a ha (selbergClosedSequence182 w x) henv.1
    (fun n hn => by simpa only [pow_zero, Real.rpow_zero, mul_one] using henv.2 n hn)
  simpa only [mul_assoc] using hg

theorem selbergWeight_divisor_weight_log_saving_of_unweighted
    {ι : Type*} (w : ι → Fin 3) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (Q : ℝ → ι → Finset ℕ) (a : ℝ → ι → ℕ → ℕ)
    (hQ : ∀ᶠ x : ℝ in atTop, ∀ i : ι, Q x i ⊆ Finset.Icc 1 ⌊x ^ θ⌋₊)
    (ha : ∀ᶠ x : ℝ in atTop, ∀ i : ι, ∀ q ∈ Q x i, Nat.Coprime (a x i q) q)
    (J : ℕ)
    (hunweighted : ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ i : ι,
        (∑ q ∈ Q x i, ‖fullDiscrepancy (selbergClosedSequence182 (w i) x) q (a x i q)‖) ≤
          K * x / (Real.log x) ^ A) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ i : ι,
        (∑ q ∈ Q x i, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (selbergClosedSequence182 (w i) x) q (a x i q)‖) ≤
            K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨P, Kc, Xc, hKc, _hXc, hcrude⟩ :=
    selbergWeight_divisor_weight_log_growth θ hθ0 hθ1 (2 * J)
  have hrequested : 0 < 2 * A + (P : ℝ) := by positivity
  obtain ⟨Ks, Xs, hKs, hXs, hsmall⟩ := hunweighted (2 * A + (P : ℝ)) hrequested
  obtain ⟨Xf, hXf⟩ := eventually_atTop.mp (hQ.and ha)
  let X : ℝ := max Xs (max Xc Xf)
  refine ⟨Ks + Kc, X, add_pos hKs hKc, hXs.trans_le (le_max_left _ _), ?_⟩
  intro x hx i
  have hxxs : Xs ≤ x := (le_max_left _ _).trans hx
  have hxxc : Xc ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxxf : Xf ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : 1 < x := hXs.trans_le hxxs
  have hraw := hsmall x hxxs i
  have hlarge := hcrude x hxxc (w i) (Q x i) ((hXf x hxxf).1 i)
    (a x i) ((hXf x hxxf).2 i)
  exact sum_divisor_weighted_log_saving_of_two_bounds
    (Q x i) J (fun q => ‖fullDiscrepancy (selbergClosedSequence182 (w i) x) q (a x i q)‖)
    (fun q _hq => norm_nonneg _) x (Real.log x) A Ks Kc P
    (zero_lt_one.trans hx1).le (Real.log_pos hx1) hKs hKc hraw hlarge

open Classical in
theorem bounded_shifted_discrepancy_sub_le
    (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (L R h q a : ℕ) (hq : 0 < q) :
    ‖fullDiscrepancy (∑ n ∈ Finset.Icc (L + h) (R + h), Finsupp.single n (f n)) q a -
      fullDiscrepancy (∑ n ∈ Finset.Icc L R, Finsupp.single n (f n)) q a‖ ≤
        4 * (h : ℝ) * C := by
  let w (n : ℕ) := (if n % q = a % q then f n else 0) -
    (if Nat.Coprime n q then f n else 0) / (q.totient : ℂ)
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hmask (n : ℕ) (P : Prop) [Decidable P] : ‖if P then f n else 0‖ ≤ C := by
    split_ifs
    · exact hf n
    · simpa only [norm_zero] using hC
  have hw (n : ℕ) : ‖w n‖ ≤ 2 * C := by
    dsimp only [w]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, Complex.norm_natCast]
    have hr := (div_le_div_of_nonneg_right (hmask n (Nat.Coprime n q))
      (Nat.cast_nonneg _)).trans (div_le_self hC hφ)
    linarith only [hmask n (n % q = a % q), hr]
  have hleft : (Finset.Icc L R \ Finset.Icc (L + h) (R + h)).card ≤ h := by
    calc
      _ ≤ (Finset.Ico L (L + h)).card := Finset.card_le_card (by
        intro n hn
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ico] at hn ⊢
        omega)
      _ = h := by simp
  have hright : (Finset.Icc (L + h) (R + h) \ Finset.Icc L R).card ≤ h := by
    calc
      _ ≤ (Finset.Ioc R (R + h)).card := Finset.card_le_card (by
        intro n hn
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
        omega)
      _ = h := by simp
  have hsum (S : Finset ℕ) (hS : S.card ≤ h) : ‖∑ n ∈ S, w n‖ ≤ 2 * (h : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ S, 2 * C := norm_sum_le_of_le _ (fun n _ => hw n)
      _ = (S.card : ℝ) * (2 * C) := by simp
      _ ≤ (h : ℝ) * (2 * C) := mul_le_mul_of_nonneg_right (Nat.mono_cast hS) (by positivity)
      _ = _ := by ring
  rw [fullDiscrepancy_sample, fullDiscrepancy_sample]
  change ‖∑ n ∈ Finset.Icc (L + h) (R + h), w n - ∑ n ∈ Finset.Icc L R, w n‖ ≤ _
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  exact (norm_sub_le _ _).trans ((add_le_add (hsum _ hright) (hsum _ hleft)).trans_eq (by ring))

open Classical in
theorem bounded_shifted_discrepancy_divisor_weight_le
    (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (J Q L R h : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) (a : ℕ → ℕ) :
    (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
      ‖fullDiscrepancy (∑ n ∈ Finset.Icc (L + h) (R + h), Finsupp.single n (f n)) q (a q) -
        fullDiscrepancy (∑ n ∈ Finset.Icc L R, Finsupp.single n (f n)) q (a q)‖) ≤
      4 * (h : ℝ) * C * Q * (1 + Real.log (Q : ℝ)) ^ (2 ^ J - 1) := by
  have hweights : (∑ q ∈ S, (q.divisors.card : ℝ) ^ J) ≤
      (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ J - 1) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun q _ _ => by positivity)).trans
      (sum_card_divisors_pow_le_mul_log_pow J Q)
  calc
    _ ≤ ∑ q ∈ S, (q.divisors.card : ℝ) ^ J * (4 * (h : ℝ) * C) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (bounded_shifted_discrepancy_sub_le f C hC hf L R h q (a q)
          (Finset.mem_Icc.mp (hS hq)).1) (by positivity)
    _ = (4 * (h : ℝ) * C) * ∑ q ∈ S, (q.divisors.card : ℝ) ^ J := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ (4 * (h : ℝ) * C) * ((Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ J - 1)) :=
      mul_le_mul_of_nonneg_left hweights (by positivity)
    _ = _ := by ring

open Classical in
theorem selbergWeight_shifted_discrepancy_divisor_weight_eventually
    (h : ℕ) (θ : ℝ) (hθ : θ < 1) (J : ℕ) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ w : Fin 3,
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 ⌊x ^ θ⌋₊ → ∀ a : ℕ → ℕ,
        (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q (a q) -
            fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖) ≤
          x / (Real.log x) ^ A := by
  filter_upwards [fixed_shift_divisor_moment_eventually θ hθ J (h * 25) A] with x hx
  intro w S hS a
  have himage : (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).image (fun n => n + h) =
      Finset.Icc (⌈x⌉₊ + h) (⌊2 * x⌋₊ + h) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨m, ⟨hmlo, hmhi⟩, rfl⟩
      omega
    · intro hn
      refine ⟨n - h, ?_, ?_⟩ <;> omega
  have hb := bounded_shifted_discrepancy_divisor_weight_le
    (fun n => (selbergWeight182 w x n : ℂ)) 25 (by norm_num)
    (selbergWeight182_norm_le w x) J ⌊x ^ θ⌋₊ ⌈x⌉₊ ⌊2 * x⌋₊ h S hS a
  simp only [selbergShiftedSequence182, selbergClosedSequence182, himage]
  refine hb.trans ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hx

#print axioms selbergWeight_divisor_weight_log_saving_of_unweighted
#print axioms bounded_shifted_discrepancy_sub_le
#print axioms selbergWeight_shifted_discrepancy_divisor_weight_eventually

end PrimeGap182Analytic
