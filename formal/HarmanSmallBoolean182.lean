import HarmanPrimeBox182
import HarmanSmallBoxes182
import HarmanBoundaryArithmetic182

/-! Actual Boolean-cut prime sequences of two, three, or four factors at
the new central/roughness thresholds, with all monomial boundary errors.
The only analytic premise is the explicit uniform bilinear estimate.
Adapted from Apache-2.0 PrimeGaps186 at the checked source hash. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

variable {arity : ℕ}

open Classical in
theorem central_small_prime_boolean_cut_coherent_log_saving_of_bilinear (hArity : arity ≤ 3)
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hωupper : «ω» < 1 / 4)
    (hsource : SourceBilinearEstimate j «ω» δ σ) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ M : Finset (MinorantSmallMonomialCut (arity + 1)), ∀ C : (Fin (arity + 1) → ℕ) → Prop,
      M.card ≤ 32 →
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ arity + 1 ∧ 0 < d.threshold) →
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
      (∀ p ∈ T, C p →
        (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        ∃ S : Finset (Fin (arity + 1)), S.Nonempty ∧ S ≠ Finset.univ ∧
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
  let E : ℝ := 4 * (D + 1)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨Kb, Xb, hKb, hXb, hbox⟩ :=
    central_prime_box_typeII_coherent_log_saving_of_bilinear j (arity + 1) «ω» δ σ
      (8639 / 100000) 64 hω hδ hσ (by norm_num) (by norm_num) hsource
      (A + E) (by linarith)
  obtain ⟨Xc, hXc⟩ := Filter.eventually_atTop.mp
    (small_prime_geometric_central_scales hArity τ hτ)
  obtain ⟨Xs, hXs⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (A + 18)
      (by norm_num : (0 : ℝ) < 8639 / 50000)).eventuallyLE)
  let C0 : ℝ := 2 + Real.log 64
  let Cb : ℝ := 8 * (17 * 64) * (1023 + 1) * C0 ^ 16
  let K : ℝ := (6 : ℝ) ^ 4 * Kb + 32 * Cb
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
  let label (p : Fin (arity + 1) → ℕ) : Fin (arity + 1) → ℕ := fun i => bin (p i)
  let B := T.image label
  let U (b : Fin (arity + 1) → ℕ) := T.filter (fun p => label p = b)
  let V := B.filter (fun b => ∃ p ∈ U b, C p)
  let W := V.filter (fun b => ¬∀ p ∈ U b, C p)
  let Fbox (b : Fin (arity + 1) → ℕ) : ℕ →₀ ℂ :=
    ∑ p ∈ U b, Finsupp.single (∏ i, p i) 1
  have hmesh := four_geometric_log_mesh_spec D x hD hxexp
  have hh : 0 < h := hmesh.1
  have hh1 : h ≤ 1 := hmesh.2.1
  have hhquarter : h ≤ 1 / 4 := by
    calc
      h ≤ l ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by dsimp only [D]; linarith)
      _ = 1 / l := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by dsimp only [l]; linarith)
  have hcardB : (B.card : ℝ) ≤ (6 : ℝ) ^ 4 * l ^ E :=
    small_prime_geometric_box_card_polylog hArity D x hD hxexp
  have hcardV : (V.card : ℝ) ≤ (6 : ℝ) ^ 4 * l ^ E :=
    (Nat.cast_le.mpr (Finset.card_filter_le B _)).trans hcardB
  have hBbound (b : Fin (arity + 1) → ℕ) (hb : b ∈ V) :
      (∑ q ∈ Q, ‖fullDiscrepancy (Fbox b) q a‖) ≤ Kb * x / l ^ (A + E) := by
    obtain ⟨p, hp, hCp⟩ := (Finset.mem_filter.mp hb).2
    have hpT := (Finset.mem_filter.mp hp).1
    have hlabel := (Finset.mem_filter.mp hp).2
    obtain ⟨hprod, S, hS, hSproper, hSlo, hShi⟩ := hsupport p hpT hCp
    let Lb (i : Fin (arity + 1)) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
    let Rb (i : Fin (arity + 1)) : ℝ := min (x ^ ((9 : ℝ) / 10))
      ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ)
    obtain ⟨R, Y, _hRS, hRne, hRproper, hY, hcuts, hYlo, hYhi, hNlo, hNhi⟩ :=
      hXc x hxc h hh hhquarter b p (Fintype.mem_piFinset.mp hpT)
        (fun i => congrFun hlabel i) hprod S hS hSproper
        (by simpa only [Nat.cast_prod] using hSlo)
        (by simpa only [Nat.cast_prod] using hShi)
    have hexponent : (41361 : ℝ) / 100000 - τ = 1 / 2 - σ := by
      dsimp only [τ]
      ring
    rw [hexponent] at hNlo
    have hU : U b = Fintype.piFinset (fun i : Fin (arity + 1) =>
        (Finset.Icc ⌈Lb i⌉₊ ⌊Rb i⌋₊).filter Nat.Prime) := by
      have hboxes := (finite_small_prime_box_cut_decomposition P bin C).1 b
      change U b = Fintype.piFinset
        (fun i : Fin (arity + 1) => P.filter (fun p => bin p = b i)) at hboxes
      rw [hboxes]
      congr 1
      funext i
      exact small_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)
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
        (6 : ℝ) ^ 4 * Kb * x / l ^ A := by
    calc
      _ ≤ ∑ b ∈ V, Kb * x / l ^ (A + E) := Finset.sum_le_sum hBbound
      _ = (V.card : ℝ) * (Kb * x / l ^ (A + E)) := by simp
      _ ≤ ((6 : ℝ) ^ 4 * l ^ E) * (Kb * x / l ^ (A + E)) :=
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
    apply boolean_small_monomial_mixed_geometric_box_card hArity x h hx2 hh hh1 M C hM hboolean
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
  have harith : (6 : ℝ) ^ 4 * Kb * x / l ^ A +
      (32 * Cb) * x / l ^ A = K * x / l ^ A := by
    dsimp only [K]
    ring
  have hcover := finite_small_prime_box_discrepancy_cover P bin C Q (fun _ => a)
  exact hcover.trans ((add_le_add hinterior hboundary).trans_eq harith)

open Classical in
theorem central_small_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear (hArity : arity ≤ 3)
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ M : Finset (MinorantSmallMonomialCut (arity + 1)), ∀ C : (Fin (arity + 1) → ℕ) → Prop,
      M.card ≤ 32 →
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ arity + 1 ∧ 0 < d.threshold) →
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
      (∀ p ∈ T, C p →
        (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        ∃ S : Finset (Fin (arity + 1)), S.Nonempty ∧ S ≠ Finset.univ ∧
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
    central_small_prime_boolean_cut_coherent_log_saving_of_bilinear hArity j («ω» + r) (δ + r) σ
      (by linarith) (by linarith) hσgap hωupper hsource A hA
  refine ⟨K, max Xp Xr, hK, hXp.trans (le_max_left _ _), ?_⟩
  intro x hx Y hY M C hMcard hM P T hboolean hsupport I hI a ha F Q
  have hxp : Xp ≤ x := (le_max_left _ _).trans hx
  have hxr : Xr ≤ x := (le_max_right _ _).trans hx
  have hsubset := hXr x hxr Y hY I
  have hbound := hp x hxp M C hMcard hM hboolean hsupport I hI a ha
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun q _ _ => norm_nonneg (fullDiscrepancy F q a))).trans hbound

#print axioms central_small_prime_boolean_cut_coherent_log_saving_of_bilinear
#print axioms central_small_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear

end PrimeGap182Analytic.Harman
