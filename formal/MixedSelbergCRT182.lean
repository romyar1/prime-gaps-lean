import Selberg39

/-!
Mixed marked Selberg sums. The CRT estimate acts on the complete divisor
coefficient, so a profile radius stays paired with its own auxiliary radius.
No maximum of unrelated radii is taken. All mixed terms remain in the mean.
-/

noncomputable section
open scoped BigOperators
open PrimeGap182.Selberg

namespace PrimeGap182Analytic

def divisorRootOn {ι : Type*} [Fintype ι]
    (D : Finset (ι → ℕ)) (lam : (ι → ℕ) → ℝ) (h : ι → ℕ) (n : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ D, if ∀ j, d j ∣ n + h j then lam d else 0

theorem divisorRootOn_add {ι : Type*} [Fintype ι]
    (D : Finset (ι → ℕ)) (lam mu : (ι → ℕ) → ℝ) (h : ι → ℕ) (n : ℕ) :
    divisorRootOn D (lam + mu) h n =
      divisorRootOn D lam h n + divisorRootOn D mu h n := by
  classical
  unfold divisorRootOn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : ∀ j, d j ∣ n + h j <;> simp [hd]

theorem divisorRootOn_sub {ι : Type*} [Fintype ι]
    (D : Finset (ι → ℕ)) (lam mu : (ι → ℕ) → ℝ) (h : ι → ℕ) (n : ℕ) :
    divisorRootOn D (lam - mu) h n =
      divisorRootOn D lam h n - divisorRootOn D mu h n := by
  classical
  unfold divisorRootOn
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : ∀ j, d j ∣ n + h j <;> simp [hd]

theorem divisorRootOn_extend {ι : Type*} [Fintype ι]
    (D E : Finset (ι → ℕ)) (hDE : D ⊆ E)
    (lam : (ι → ℕ) → ℝ) (h : ι → ℕ) (n : ℕ) :
    divisorRootOn E (fun d => if d ∈ D then lam d else 0) h n =
      divisorRootOn D lam h n := by
  classical
  unfold divisorRootOn
  symm
  calc
    _ = ∑ d ∈ D, if ∀ j, d j ∣ n + h j then
        (if d ∈ D then lam d else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [ite_eq_left hd]
    _ = _ := Finset.sum_subset hDE (by
      intro d _ hd
      simp only [ite_eq_right hd, ite_self])

theorem coefficientL1_extend {α : Type*} [DecidableEq α]
    (D E : Finset α) (hDE : D ⊆ E) (lam : α → ℝ) :
    (∑ d ∈ E, |if d ∈ D then lam d else 0|) = ∑ d ∈ D, |lam d| := by
  classical
  symm
  calc
    _ = ∑ d ∈ D, |if d ∈ D then lam d else 0| := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [ite_eq_left hd]
    _ = _ := Finset.sum_subset hDE (by
      intro d _ hd
      simp only [ite_eq_right hd, abs_zero])

theorem finite_marked_polarization {α : Type*} (S : Finset α)
    (w f g : α → ℝ) :
    4 * (∑ n ∈ S, w n * f n * g n) =
      (∑ n ∈ S, w n * (f n + g n) ^ 2) -
        ∑ n ∈ S, w n * (f n - g n) ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The marked count is compared with the actual full-period square. -/
theorem selberg_square_interval_period_crt_marked
    {ι : Type*} [Fintype ι] (h : ι → ℕ) (hinj : Function.Injective h) (i : ι)
    (D : Finset (ι → ℕ)) (lam : (ι → ℕ) → ℝ)
    (W b M q : ℕ) (hW : 0 < W) (hM : 0 < M) (hq : 0 < q)
    (hWM : Nat.Coprime W M)
    (hD : ∀ d ∈ D, Squarefree (∏ j, d j) ∧
      Nat.Coprime (∏ j, d j) W ∧ Nat.Coprime (∏ j, d j) M ∧ ∀ j, d j ∣ q)
    (hcover : ∀ a c : ι, h a ≠ h c → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h c) → p ∣ W)
    (x : ℝ) (hx : 0 ≤ x) :
    |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq W n b ∧ M ∣ n + h i then
          divisorRootOn D lam h n ^ 2 else 0) -
      x / ((W : ℝ) * (M : ℝ)) * ((1 / (q : ℝ)) *
        ∑ n ∈ Finset.range q, divisorRootOn D lam h n ^ 2)| ≤
      2 * (∑ d ∈ D, |lam d|) ^ 2 := by
  classical
  have hp := selberg_square_period_mean h hinj D lam W q hq
    (fun d hd => ⟨(hD d hd).1, (hD d hd).2.1, (hD d hd).2.2.2⟩) hcover
  have hc := selberg_square_real_interval_crt_marked h hinj i D lam W b M
    hW hM hWM (fun d hd => ⟨(hD d hd).1, (hD d hd).2.1, (hD d hd).2.2.1⟩)
    hcover x hx
  simpa only [divisorRootOn, hp] using hc

/-- A bilinear bound on complete divisor coefficients. In the application each
coefficient is the product of a radial block and its own auxiliary sieve. -/
theorem selberg_mixed_interval_period_crt_marked
    {ι : Type*} [Fintype ι] (h : ι → ℕ) (hinj : Function.Injective h) (i : ι)
    (D : Finset (ι → ℕ)) (lam mu : (ι → ℕ) → ℝ)
    (W b M q : ℕ) (hW : 0 < W) (hM : 0 < M) (hq : 0 < q)
    (hWM : Nat.Coprime W M)
    (hD : ∀ d ∈ D, Squarefree (∏ j, d j) ∧
      Nat.Coprime (∏ j, d j) W ∧ Nat.Coprime (∏ j, d j) M ∧ ∀ j, d j ∣ q)
    (hcover : ∀ a c : ι, h a ≠ h c → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h c) → p ∣ W)
    (x : ℝ) (hx : 0 ≤ x) :
    |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq W n b ∧ M ∣ n + h i then
          divisorRootOn D lam h n * divisorRootOn D mu h n else 0) -
      x / ((W : ℝ) * (M : ℝ)) * ((1 / (q : ℝ)) *
        ∑ n ∈ Finset.range q, divisorRootOn D lam h n * divisorRootOn D mu h n)| ≤
      ((∑ d ∈ D, |lam d|) + ∑ d ∈ D, |mu d|) ^ 2 := by
  classical
  let S := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let f := divisorRootOn D lam h
  let g := divisorRootOn D mu h
  let w : ℕ → ℝ := fun n => if Nat.ModEq W n b ∧ M ∣ n + h i then 1 else 0
  let K := (∑ d ∈ D, |lam d|) + ∑ d ∈ D, |mu d|
  have hK : 0 ≤ K := add_nonneg
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hpL : (∑ d ∈ D, |(lam + mu) d|) ≤ K := by
    dsimp only [K]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun d _ => abs_add_le (lam d) (mu d)
  have hmL : (∑ d ∈ D, |(lam - mu) d|) ≤ K := by
    dsimp only [K]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun d _ => abs_sub (lam d) (mu d)
  have hp := selberg_square_interval_period_crt_marked h hinj i D (lam + mu)
    W b M q hW hM hq hWM hD hcover x hx
  have hm := selberg_square_interval_period_crt_marked h hinj i D (lam - mu)
    W b M q hW hM hq hWM hD hcover x hx
  have hp' := hp.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hpL 2) zero_le_two)
  have hm' := hm.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hmL 2) zero_le_two)
  simp only [divisorRootOn_add, divisorRootOn_sub] at hp' hm'
  have hite (n : ℕ) (v : ℝ) :
      (if Nat.ModEq W n b ∧ M ∣ n + h i then v else 0) = w n * v := by
    dsimp only [w]
    split_ifs <;> simp
  simp_rw [hite] at hp' hm' ⊢
  have hS := finite_marked_polarization S w f g
  have hT := finite_marked_polarization (Finset.range q) (fun _ => 1) f g
  simp only [one_mul] at hT
  have heq :
      4 * ((∑ n ∈ S, w n * f n * g n) -
          x / ((W : ℝ) * (M : ℝ)) * ((1 / (q : ℝ)) *
            ∑ n ∈ Finset.range q, f n * g n)) =
        ((∑ n ∈ S, w n * (f n + g n) ^ 2) -
          x / ((W : ℝ) * (M : ℝ)) * ((1 / (q : ℝ)) *
            ∑ n ∈ Finset.range q, (f n + g n) ^ 2)) -
        ((∑ n ∈ S, w n * (f n - g n) ^ 2) -
          x / ((W : ℝ) * (M : ℝ)) * ((1 / (q : ℝ)) *
            ∑ n ∈ Finset.range q, (f n - g n) ^ 2)) := by
    linear_combination hS - (x / ((W : ℝ) * (M : ℝ)) * (1 / (q : ℝ))) * hT
  have hpabs := abs_le.mp hp'
  have hmabs := abs_le.mp hm'
  simp only [← mul_assoc]
  apply abs_le.mpr
  constructor <;> nlinarith only [heq, hpabs.1, hpabs.2, hmabs.1, hmabs.2]

open Classical in
theorem selberg_mixed_two_supports_interval_period_crt_marked
    {ι : Type*} [Fintype ι] (h : ι → ℕ) (hinj : Function.Injective h) (i : ι)
    (D E : Finset (ι → ℕ)) (lam mu : (ι → ℕ) → ℝ)
    (W b M q : ℕ) (hW : 0 < W) (hM : 0 < M) (hq : 0 < q)
    (hWM : Nat.Coprime W M)
    (hD : ∀ d ∈ D, Squarefree (∏ j, d j) ∧
      Nat.Coprime (∏ j, d j) W ∧ Nat.Coprime (∏ j, d j) M ∧ ∀ j, d j ∣ q)
    (hE : ∀ d ∈ E, Squarefree (∏ j, d j) ∧
      Nat.Coprime (∏ j, d j) W ∧ Nat.Coprime (∏ j, d j) M ∧ ∀ j, d j ∣ q)
    (hcover : ∀ a c : ι, h a ≠ h c → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h c) → p ∣ W)
    (x : ℝ) (hx : 0 ≤ x) :
    |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq W n b ∧ M ∣ n + h i then
          divisorRootOn D lam h n * divisorRootOn E mu h n else 0) -
      x / ((W : ℝ) * (M : ℝ)) * ((1 / (q : ℝ)) *
        ∑ n ∈ Finset.range q, divisorRootOn D lam h n * divisorRootOn E mu h n)| ≤
      ((∑ d ∈ D, |lam d|) + ∑ d ∈ E, |mu d|) ^ 2 := by
  let U := D ∪ E
  have hDU : D ⊆ U := Finset.subset_union_left
  have hEU : E ⊆ U := Finset.subset_union_right
  have hU : ∀ d ∈ U, Squarefree (∏ j, d j) ∧
      Nat.Coprime (∏ j, d j) W ∧ Nat.Coprime (∏ j, d j) M ∧ ∀ j, d j ∣ q := by
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact hD d hd
    · exact hE d hd
  have hc := selberg_mixed_interval_period_crt_marked h hinj i U
    (fun d => if d ∈ D then lam d else 0) (fun d => if d ∈ E then mu d else 0)
    W b M q hW hM hq hWM hU hcover x hx
  simpa only [divisorRootOn_extend D U hDU, divisorRootOn_extend E U hEU,
    coefficientL1_extend D U hDU, coefficientL1_extend E U hEU] using hc

#print axioms selberg_square_interval_period_crt_marked
#print axioms selberg_mixed_interval_period_crt_marked
#print axioms selberg_mixed_two_supports_interval_period_crt_marked

end PrimeGap182Analytic
