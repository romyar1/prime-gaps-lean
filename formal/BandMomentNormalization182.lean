import WeightMeans182

/-! The normalization lemmas are adapted, with the full proofs, from
PrimeGaps186.lean lines 201588--201719. The powers here are 39 for the
root and 38 for the prime face. All logarithmic error estimates remain
explicit hypotheses in these generic normalization lemmas. -/

noncomputable section
open MeasureTheory Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182Analytic

theorem selberg39_log_saving_error_small
    {𝓗 : Finset ℕ}
    (S : ℝ → ℕ → ℝ) (Admissible : ℝ → ℕ → Prop)
    (hS : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧
      ∀ᶠ x : ℝ in Filter.atTop, ∀ v : ℕ, Admissible x v →
        |S x v| ≤ K * x / (Real.log x) ^ A) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      let ρ : ℝ := 2624989 / 10000000
      let W := presievingModulus 𝓗 x
      let B := fragmentNormalization W (x ^ ρ)
      let Z : ℝ := x / (W : ℝ) / B ^ 39
      1 < x ∧ 0 < B ∧ 0 < Z ∧ ∀ v : ℕ, Admissible x v → |S x v| ≤ ε * Z := by
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := hS 41 (by norm_num)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    presieving_le_mul_log_eventually 𝓗 1 zero_lt_one,
    Real.tendsto_log_atTop.eventually_ge_atTop (K / ε), hbound]
      with x hx hWlog hloglarge hbound
  intro ρ W B Z
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hρ : 0 < ρ := by norm_num [ρ]
  have hρ1 : ρ ≤ 1 := by norm_num [ρ]
  have hW : 0 < W := presieving_pos 𝓗 x
  have hWR : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hφ : (0 : ℝ) < W.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)
  have hratio : (W.totient : ℝ) / (W : ℝ) ≤ 1 :=
    (div_le_one hWR).mpr (Nat.cast_le.mpr (Nat.totient_le W))
  have hBformula : B = ((W.totient : ℝ) / (W : ℝ)) * (ρ * Real.log x) := by
    dsimp only [B, fragmentNormalization]
    rw [Real.log_rpow hx0]
  have hB : 0 < B := by
    rw [hBformula]
    exact mul_pos (div_pos hφ hWR) (mul_pos hρ hlog)
  have hBle : B ≤ Real.log x := by
    rw [hBformula]
    exact (mul_le_of_le_one_left (mul_nonneg hρ.le hlog.le) hratio).trans
      (mul_le_of_le_one_left hlog.le hρ1)
  have hWlog' : (W : ℝ) ≤ Real.log x := by simpa only [one_mul] using hWlog
  have hden : (W : ℝ) * B ^ 39 ≤ (Real.log x) ^ 40 := by
    calc
      (W : ℝ) * B ^ 39 ≤ Real.log x * (Real.log x) ^ 39 :=
        mul_le_mul hWlog' (pow_le_pow_left₀ hB.le hBle 39)
          (pow_nonneg hB.le 39) hlog.le
      _ = (Real.log x) ^ 40 := by ring
  have hZ : 0 < Z := div_pos (div_pos hx0 hWR) (pow_pos hB 39)
  have hZlower : x / (Real.log x) ^ 40 ≤ Z := by
    change x / (Real.log x) ^ 40 ≤ x / (W : ℝ) / B ^ 39
    rw [div_div]
    exact div_le_div_of_nonneg_left hx0.le (mul_pos hWR (pow_pos hB 39)) hden
  have hKsmall : K / Real.log x ≤ ε :=
    (div_le_comm₀ hlog hε).2 hloglarge
  refine ⟨hx, hB, hZ, ?_⟩
  intro v hv
  calc
    |S x v| ≤ K * x / (Real.log x) ^ 41 := by
      simpa only [Real.rpow_ofNat] using hbound v hv
    _ = (K / Real.log x) * (x / (Real.log x) ^ 40) := by
      rw [show (Real.log x) ^ 41 = (Real.log x) ^ 40 * Real.log x by ring]
      ring
    _ ≤ ε * (x / (Real.log x) ^ 40) :=
      mul_le_mul_of_nonneg_right hKsmall (div_nonneg hx0.le (pow_nonneg hlog.le 40))
    _ ≤ ε * Z := mul_le_mul_of_nonneg_left hZlower hε.le

theorem selberg39_moment_from_diagonal_error
    {𝓗 : Finset ℕ}
    (S : ℝ → ℕ → ℝ) (Admissible : ℝ → ℕ → Prop)
    (total gram : ℝ → ℝ) (m J : ℝ)
    (hmass : Filter.Tendsto (fun x => (Real.log x / x) * total x)
      Filter.atTop (nhds m))
    (hgram : Filter.Tendsto (fun x =>
      (fragmentNormalization
        (presievingModulus 𝓗 x)
        (x ^ (2624989 / 10000000 : ℝ))) ^ 38 * gram x)
      Filter.atTop (nhds J))
    (herror : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧
      ∀ᶠ x : ℝ in Filter.atTop, ∀ v : ℕ, Admissible x v →
        |S x v - total x /
          ((presievingModulus 𝓗 x).totient : ℝ) *
          gram x| ≤ K * x / (Real.log x) ^ A) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      let ρ : ℝ := 2624989 / 10000000
      let W := presievingModulus 𝓗 x
      let B := fragmentNormalization W (x ^ ρ)
      let Z : ℝ := x / (W : ℝ) / B ^ 39
      ∀ v : ℕ, Admissible x v → |S x v - (ρ * m * J) * Z| ≤ ε * Z := by
  let ρ : ℝ := 2624989 / 10000000
  let W : ℝ → ℕ := presievingModulus 𝓗
  let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (x ^ ρ)
  let Z : ℝ → ℝ := fun x => x / (W x : ℝ) / B x ^ 39
  let T : ℝ → ℝ := fun x => ρ * ((Real.log x / x) * total x) * (B x ^ 38 * gram x)
  have hlim : Filter.Tendsto T Filter.atTop (nhds (ρ * m * J)) :=
    (hmass.const_mul ρ).mul hgram
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop, |T x - ρ * m * J| < ε / 2 := by
    simpa only [Real.norm_eq_abs] using
      hlim.eventually (eventually_norm_sub_lt (ρ * m * J) hhalf)
  filter_upwards [selberg39_log_saving_error_small (𝓗 := 𝓗)
    (fun x v => S x v - total x / ((W x).totient : ℝ) * gram x)
      Admissible herror (ε / 2) hhalf, hsmall] with x hx hsmall
  intro ρ' W' B' Z' v hv
  have hx0 : 0 < x := zero_lt_one.trans hx.1
  have hlog : 0 < Real.log x := Real.log_pos hx.1
  have hρ : 0 < ρ := by norm_num [ρ]
  have hW : (0 : ℝ) < W x :=
    Nat.cast_pos.mpr (presieving_pos 𝓗 x)
  have hφ : (0 : ℝ) < (W x).totient := Nat.cast_pos.mpr
    (Nat.totient_pos.mpr (presieving_pos 𝓗 x))
  have hZ : 0 < Z x := hx.2.2.1
  have hBformula : B x = (((W x).totient : ℝ) / (W x : ℝ)) * (ρ * Real.log x) := by
    dsimp only [B, fragmentNormalization]
    rw [Real.log_rpow hx0]
  have hmain : total x / ((W x).totient : ℝ) * gram x = Z x * T x := by
    dsimp only [Z, T]
    rw [hBformula]
    field_simp [hW.ne', hφ.ne', hρ.ne', hlog.ne', hx0.ne']
  change |S x v - (ρ * m * J) * Z x| ≤ ε * Z x
  calc
    |S x v - (ρ * m * J) * Z x| =
        |(S x v - total x / ((W x).totient : ℝ) * gram x) +
          Z x * (T x - ρ * m * J)| := by rw [hmain]; ring_nf
    _ ≤ |S x v - total x / ((W x).totient : ℝ) * gram x| +
        |Z x * (T x - ρ * m * J)| := abs_add_le _ _
    _ = |S x v - total x / ((W x).totient : ℝ) * gram x| +
        Z x * |T x - ρ * m * J| := by rw [abs_mul, abs_of_pos hZ]
    _ ≤ (ε / 2) * Z x + Z x * (ε / 2) :=
      add_le_add (hx.2.2.2 v hv) (mul_le_mul_of_nonneg_left hsmall.le hZ.le)
    _ = ε * Z x := by ring


#print axioms selberg39_log_saving_error_small
#print axioms selberg39_moment_from_diagonal_error

end PrimeGap182Analytic
