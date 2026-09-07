import HarmanHBSelected182
import HarmanSmallBoxes182
import HarmanBoundary182
import HarmanBoundaryArithmetic182

/-! Distribution of the actual new T3 source from the explicit bilinear
and Type III interfaces. This proves all prime-box, Mellin, HB, original
boundary, radial boundary, and monomial-cut transfers at the new cutoffs.
The source itself is the literal arithmetic function from HarmanBuchstab182.
Adapted from Apache-2.0 PrimeGaps186 at the source hash in the generator. -/

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sourceT3_closed_prime_boxes_log_saving_of_analytic_inputs
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ (1 / 10 ^ 10 : ℝ))
    (density : ℕ) (hdensity : 1 ≤ density) («ω» δ : ℝ)
    (hω : 0 < «ω») (hωupper : «ω» < 1 / 12) (hδ : 0 < δ) :
    let a : ℝ := 41361 / 100000
    let ζ : ℝ := 1 - 34941 / 100000 - a
    let σclass : ℝ := 1 / 2 - a + τ
    let γ₀ : ℝ := 34941 / 100000 - τ
    ∀ σdist σIII : ℝ, σclass < σdist → σdist < 1 / 2 →
      PrimeGap182.TypeIII.PositiveSmoothTypeIIIGlobalEstimate «ω» δ σIII →
      σIII < 2159 / 25000 - τ →
      1 / 4 + 7 * «ω» + 2 * δ < γ₀ →
      SourceBilinearEstimate density «ω» δ σdist →
      ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
        ∀ x : ℝ, X ≤ x → ∀ L U : Fin 3 → ℝ,
          (∀ c, x ^ (ζ - τ / 10) ≤ L c) →
          (∀ c, L c ≤ U c ∧ U c ≤ 2 * L c) →
          (∀ c, U c ≤ x ^ (a + τ / 10)) →
        ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
        ∀ a₀ : ℕ, Nat.Coprime a₀ (∏ p ∈ I, p) →
          let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
            q ∣ (∏ p ∈ I, p) ∧
              Nonempty (DenseDivisibilityWitness
                ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q))
          (∑ q ∈ Q, ‖PrimeGap186.fullDiscrepancy
            ((primeIntervalBoxAlgebra L U Finset.univ).coeff.filter
              (fun n : ℕ => n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)) q a₀‖) ≤
            K * x / (Real.log x) ^ A := by
  intro a ζ σclass γ₀ σdist σIII hσσ hσhalf hIIIlo hIIIhi hgap hdist A hA
  obtain ⟨Dr, hDr, Kr, Xr, hKr, hXr, hradial⟩ :=
    minorantHB_three_radial_error_moduli_log_saving A hA 0
  obtain ⟨Do, hDo, Ko, Xo, hKo, hXo, horiginal⟩ :=
    minorantHB_three_original_boundary_moduli_log_saving 0 A hA
  let D : ℕ := max Dr Do
  have hD : 1 ≤ D := hDr.trans (le_max_left _ _)
  obtain ⟨Ks, Xs, hKs, hXs, hselected⟩ :=
    sourceT3_selected_boxes_log_saving_of_analytic_inputs τ hτ hτsmall
      density hdensity D hD «ω» δ hω hωupper hδ
      σdist σIII hσσ hσhalf hIIIlo hIIIhi hgap hdist A hA
  obtain ⟨Km, Xm, hKm, hXm, hmellin⟩ :=
    three_closed_prime_box_mellin_transfer (23 / 100) (42 / 100) (53 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 A hA
  let Kraw : ℝ := Ks + Kr + Ko
  let X : ℝ := max (max Xr Xo) (max Xs Xm)
  refine ⟨1000 * Kraw + Km, X, ?_, ?_, ?_⟩
  · dsimp only [Kraw]
    positivity
  · exact hXr.trans ((le_max_left Xr Xo).trans (le_max_left _ _))
  intro x hx L U hLwide hLU hUwide I hI a₀ ha₀ Q
  have hxr : Xr ≤ x := ((le_max_left Xr Xo).trans (le_max_left _ _)).trans hx
  have hxo : Xo ≤ x := ((le_max_right Xr Xo).trans (le_max_left _ _)).trans hx
  have hxs : Xs ≤ x := ((le_max_left Xs Xm).trans (le_max_right _ _)).trans hx
  have hxm : Xm ≤ x := ((le_max_right Xs Xm).trans (le_max_right _ _)).trans hx
  have hxexp : Real.exp 1 ≤ x := hXr.trans hxr
  have hxone : 1 < x := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hxexp
  have hxpos : 0 < x := zero_lt_one.trans hxone
  have hlogpos : 0 < Real.log x := Real.log_pos hxone
  have hscale (c : Fin 3) :
      x ^ ((23 : ℝ) / 100) ≤ L c ∧ L c ≤ x ^ ((42 : ℝ) / 100) := by
    refine ⟨?_, (hLU c).1.trans ((hUwide c).trans ?_)⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hxone.le
        (by dsimp only [ζ, a]; linarith only [hτ, hτsmall])).trans (hLwide c)
    · exact Real.rpow_le_rpow_of_exponent_le hxone.le (by
        dsimp only [a]
        linarith only [hτ, hτsmall])
  have hLone (c : Fin 3) : 1 ≤ L c :=
    (Real.one_le_rpow hxone.le (by norm_num : (0 : ℝ) ≤ 23 / 100)).trans (hscale c).1
  have hθ : (1 / 2 : ℝ) + 2 * «ω» ≤ 53 / 100 := by
    have hγ : γ₀ < (350 : ℝ) / 1000 := by dsimp only [γ₀]; linarith only [hτ, hτsmall]
    linarith only [hgap, hδ, hγ]
  have hQ : Q ⊆ Finset.Icc 1 ⌊x ^ ((53 : ℝ) / 100)⌋₊ := by
    intro q hq
    obtain ⟨hrange, _hdvd, _hdd⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqone, hqhi⟩ := Finset.mem_Icc.mp hrange
    exact Finset.mem_Icc.mpr ⟨hqone, hqhi.trans
      (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hxone.le hθ))⟩
  have hcop (q : ℕ) (hq : q ∈ Q) : Nat.Coprime a₀ q :=
    Nat.Coprime.of_dvd_right (Finset.mem_filter.mp hq).2.1 ha₀
  have hmask (n : ℕ) :
      (x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x) ↔ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := by
    rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 2 * x)]
  have hfilter (f : ℕ →₀ ℂ) :
      f.filter (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x) =
        f.filter (fun n : ℕ => n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) := by
    ext n
    simp only [Finsupp.filter_apply, hmask]
  have hraw (t : Fin 3 → ℝ) (ht : ∀ c, 0 ≤ t c) (htten : ∀ c, t c ≤ 10) :
      (∑ q ∈ Q, (q.divisors.card : ℝ) ^ 0 * ‖fullDiscrepancy
        (((∏ c : Fin 3, (MonoidAlgebra.ofCoeff
          (minorantHBClosedMangoldt (L c) (U c) (t c)) : MonoidAlgebra ℂ ℕ)).coeff).filter
            (fun n : ℕ => n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)) q a₀‖) ≤
          Kraw * x / (Real.log x) ^ A := by
    let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
    let Uhb : ℝ := x ^ ((9 : ℝ) / 100)
    let boxes (r : Fin 3 → Fin 5) :=
      Fintype.piFinset (fun c : Fin 3 => minorantHBBoxes ((r c).val + 1) (L c) (U c) Θ)
    let β (r : Fin 3 → Fin 5)
        (ν : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ) : ℕ →₀ ℂ :=
      (∏ s : Σ c : Fin 3, Fin (2 * ((r c).val + 1)),
        minorantHBLocalizedSlot ((r s.1).val + 1) Uhb Θ (t s.1) (ν s.1) s.2).coeff
    let P (r : Fin 3 → Fin 5)
        (ν : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ) : ℝ :=
      ∏ s : Σ c : Fin 3, Fin (2 * ((r c).val + 1)), Θ ^ ν s.1 s.2
    let selected : ℕ →₀ ℂ :=
      ∑ r : Fin 3 → Fin 5,
        (∏ c : Fin 3,
          (((-1 : ℝ) ^ (r c).val * ((5 : ℕ).choose ((r c).val + 1) : ℝ) : ℝ) : ℂ)) •
            ∑ ν ∈ (boxes r).filter
              (fun ν => x * Θ ^ 30 ≤ P r ν ∧ P r ν * Θ ^ 30 ≤ 2 * x), β r ν
    let G : ℕ →₀ ℂ :=
      (∏ c : Fin 3, (MonoidAlgebra.ofCoeff
        (minorantHBUnmaskedFive (L c) (U c) Uhb Θ (t c)) : MonoidAlgebra ℂ ℕ)).coeff
    let F : ℕ →₀ ℂ :=
      (∏ c : Fin 3, (MonoidAlgebra.ofCoeff
        (minorantHBClosedMangoldt (L c) (U c) (t c)) : MonoidAlgebra ℂ ℕ)).coeff
    let R : ℕ →₀ ℂ :=
      G.filter (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x) - selected
    let E : ℕ →₀ ℂ :=
      (G - F).filter (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)
    have hs : (∑ q ∈ Q, ‖fullDiscrepancy selected q a₀‖) ≤
        Ks * x / (Real.log x) ^ A :=
      hselected x hxs t ht htten L U hLwide (fun c => (hLU c).1) hUwide I hI a₀ ha₀
    have hr : (∑ q ∈ Q, ‖fullDiscrepancy R q a₀‖) ≤
        Kr * x / (Real.log x) ^ A := by
      simpa only [pow_zero, one_mul] using
        hradial x hxr D (le_max_left Dr Do) L U t Uhb hLone
          (fun c => (hLU c).1) ht htten Q hQ (fun _ => a₀) hcop
    have he : (∑ q ∈ Q, ‖fullDiscrepancy E q a₀‖) ≤
        Ko * x / (Real.log x) ^ A := by
      simpa only [pow_zero, one_mul] using
        horiginal x hxo D (le_max_right Dr Do) L L U t hscale
          (fun c => ⟨le_rfl, (hLU c).1, (hLU c).2⟩)
          (fun c => ⟨ht c, htten c⟩) Q hQ (fun _ => a₀) hcop
    have hF : F.filter (fun n : ℕ => n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) =
        selected + R - E := by
      rw [← hfilter F]
      dsimp only [R, E]
      rw [Finsupp.filter_sub]
      abel
    let kernel : ℕ → ℕ → ℂ := fun q n =>
      (if n % q = a₀ % q then 1 else 0) -
        (if Nat.Coprime n q then 1 else 0) / (q.totient : ℂ)
    have hfull (f : ℕ →₀ ℂ) (q : ℕ) :
        fullDiscrepancy f q a₀ = f.sum (fun n z => z * kernel q n) := by
      change fullDiscrepancy f q a₀ = ∑ n ∈ f.support, f n * kernel q n
      simp only [fullDiscrepancy, progressionMass, reducedMass, kernel,
        div_eq_mul_inv, mul_sub, mul_ite, ite_mul, one_mul, mul_one,
        zero_mul, mul_zero, Finset.sum_sub_distrib, Finset.sum_mul]
    have hlinear (q : ℕ) :
        fullDiscrepancy (F.filter (fun n : ℕ => n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)) q a₀ =
          fullDiscrepancy selected q a₀ + fullDiscrepancy R q a₀ -
            fullDiscrepancy E q a₀ := by
      rw [hF]
      simp only [hfull]
      rw [Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _),
        Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [pow_zero, one_mul]
    change (∑ q ∈ Q, ‖fullDiscrepancy
      (F.filter (fun n : ℕ => n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)) q a₀‖) ≤ _
    calc
      _ ≤ ∑ q ∈ Q, (‖fullDiscrepancy selected q a₀‖ +
          ‖fullDiscrepancy R q a₀‖ + ‖fullDiscrepancy E q a₀‖) := by
        apply Finset.sum_le_sum
        intro q _hq
        rw [hlinear]
        exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ Ks * x / (Real.log x) ^ A + Kr * x / (Real.log x) ^ A +
          Ko * x / (Real.log x) ^ A := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        exact add_le_add (add_le_add hs hr) he
      _ = Kraw * x / (Real.log x) ^ A := by dsimp only [Kraw]; ring
  have hprime := hmellin x hxm L U hscale hLU Q hQ (fun _ => a₀) hcop
    (Kraw * x / (Real.log x) ^ A) hraw
  simp only [pow_zero, one_mul] at hprime
  calc
    _ ≤ 1000 * (Kraw * x / (Real.log x) ^ A) + Km * x / (Real.log x) ^ A := hprime
    _ = (1000 * Kraw + Km) * x / (Real.log x) ^ A := by ring

open Classical in
theorem sourceT3_selected_dense_log_saving_of_analytic_inputs
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ (1 / 10 ^ 10 : ℝ))
    (density : ℕ) (hdensity : 1 ≤ density) («ω» δ : ℝ)
    (hω : 0 < «ω») (hωupper : «ω» < 1 / 12) (hδ : 0 < δ) :
    let a : ℝ := 41361 / 100000
    let _ζ : ℝ := 1 - 34941 / 100000 - a
    let σclass : ℝ := 1 / 2 - a + τ
    let γ₀ : ℝ := 34941 / 100000 - τ
    ∀ σdist σIII : ℝ, σclass < σdist → σdist < 1 / 2 →
      PrimeGap182.TypeIII.PositiveSmoothTypeIIIGlobalEstimate «ω» δ σIII →
      σIII < 2159 / 25000 - τ →
      1 / 4 + 7 * «ω» + 2 * δ < γ₀ →
      SourceBilinearEstimate density «ω» δ σdist →
      ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
        ∀ x : ℝ, X ≤ x →
        ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
        ∀ a₀ : ℕ, Nat.Coprime a₀ (∏ p ∈ I, p) →
          let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
            q ∣ (∏ p ∈ I, p) ∧
              Nonempty (DenseDivisibilityWitness
                ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q))
          let F : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            Finsupp.single n (sourceT3 x n : ℂ)
          (∑ q ∈ Q, ‖fullDiscrepancy F q a₀‖) ≤ K * x / (Real.log x) ^ A := by
  intro a _ζ σclass γ₀ σdist σIII hσclass hσdist hσIIIlo hσIIIhi hsmooth hsource A hA
  let θ : ℝ := 1 / 2 + 2 * «ω»
  have hθ0 : 0 < θ := by dsimp only [θ]; linarith
  have hθ1 : θ < 1 := by dsimp only [θ]; linarith
  let D : ℝ := A + 20
  let E : ℝ := 4 * (D + 1)
  have hD : 0 ≤ D := by dsimp only [D]; linarith
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  obtain ⟨Kb, Xb, hKb, _hXb, hbox⟩ :=
    sourceT3_closed_prime_boxes_log_saving_of_analytic_inputs τ hτ hτsmall
      density hdensity «ω» δ
      hω hωupper hδ σdist σIII hσclass hσdist hσIIIlo hσIIIhi hsmooth hsource
      (A + E) (by linarith)
  obtain ⟨Xn, _hXn, hnearby⟩ := sourceT3_nearby_original_box_bounds τ hτ hτsmall
  obtain ⟨Xf, _hXf, hcompact⟩ := sourceT3_eventually_compact_prime_finsupp
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
  refine ⟨K, max (Real.exp 100) (max Xb (max Xn (max Xf Xs))),
    hK, le_max_left _ _, ?_⟩
  intro x hx I hI a₀ ha Q F
  have hx100 : Real.exp 100 ≤ x := (le_max_left _ _).trans hx
  have htail : max Xb (max Xn (max Xf Xs)) ≤ x := (le_max_right _ _).trans hx
  have hxb : Xb ≤ x := (le_max_left _ _).trans htail
  have hxn : Xn ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans htail)
  have hxtail : max Xf Xs ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans htail)
  have hxf : Xf ≤ x := (le_max_left _ _).trans hxtail
  have hxs : Xs ≤ x := (le_max_right _ _).trans hxtail
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx100
  have hx2 : 2 ≤ x := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hx1 : 1 ≤ x := by linarith
  have hxgt : 1 < x := by linarith
  have hxexp : Real.exp 1 ≤ x :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 100)).trans hx100
  have hlog100 : 100 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx100
  have hlog1 : 1 ≤ Real.log x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
    ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
  let T := Fintype.piFinset (fun _ : Fin 3 => P)
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let R (n : ℕ) : Prop := n ∈ N
  have hRdef : R = fun n => n ∈ N := rfl
  clear_value R
  let C (p : Fin 3 → ℕ) : Prop :=
    (∏ i, p i) ∈ N ∧ sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true
  have hCdef : C = fun p =>
      (∏ i, p i) ∈ N ∧ sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true := rfl
  clear_value C
  let M := sourceT3MonomialCuts x
  have hMcard : M.card ≤ 32 := sourceT3MonomialCuts_card_le x
  have hM := sourceT3MonomialCuts_data x hx0
  have hprime (p : Fin 3 → ℕ) (hp : p ∈ T) (i : Fin 3) : (p i).Prime :=
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  have hboolean : ∀ p ∈ T, ∀ q ∈ T,
      (∀ d ∈ M,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (C p ↔ C q) := by
    intro p hp q hq ht
    rw [hCdef]
    exact sourceT3MonomialCuts_boolean x hxgt p q
      (fun i => (hprime p hp i).pos) (fun i => (hprime q hq i).pos) ht
  have hCR (p : Fin 3 → ℕ) (_hp : p ∈ T) (hCp : C p) : R (∏ i, p i) := by
    rw [hRdef]
    rw [hCdef] at hCp
    exact hCp.1
  have hF : F = ∑ p ∈ T,
      Finsupp.single (∏ i, p i) (if C p then (1 : ℂ) else 0) := by
    rw [hCdef]
    refine (hcompact x hxf).trans (Finset.sum_congr rfl ?_)
    intro p _hp
    apply congrArg (Finsupp.single (∏ i, p i))
    exact @ite_cond_congr ℂ _ _ inferInstance (Classical.propDecidable _) _ _ rfl
  rw [hF]
  let l : ℝ := Real.log x
  let h : ℝ := l ^ (-D)
  let bin (p : ℕ) := ⌊Real.logb (1 + h) (p : ℝ)⌋₊
  let label (p : Fin 3 → ℕ) : Fin 3 → ℕ := fun i => bin (p i)
  let B := T.image label
  let U (b : Fin 3 → ℕ) := T.filter (fun p => label p = b)
  let V := B.filter (fun b => ∃ p ∈ U b, C p)
  let W := V.filter (fun b => ¬∀ p ∈ U b, C p)
  let Fbox (b : Fin 3 → ℕ) : ℕ →₀ ℂ :=
    ∑ p ∈ U b, Finsupp.single (∏ i, p i) (if R (∏ i, p i) then 1 else 0)
  have hmesh := four_geometric_log_mesh_spec D x hD hxexp
  have hh : 0 < h := hmesh.1
  have hh1 : h ≤ 1 := hmesh.2.1
  have hcardB : (B.card : ℝ) ≤ (6 : ℝ) ^ 4 * l ^ E :=
    small_prime_geometric_box_card_polylog (arity := 2) (by decide) D x hD hxexp
  have hcardV : (V.card : ℝ) ≤ (6 : ℝ) ^ 4 * l ^ E :=
    (Nat.cast_le.mpr (Finset.card_filter_le B _)).trans hcardB
  have hBbound (b : Fin 3 → ℕ) (hb : b ∈ V) :
      (∑ q ∈ Q, ‖fullDiscrepancy (Fbox b) q a₀‖) ≤ Kb * x / l ^ (A + E) := by
    obtain ⟨p, hp, hCp⟩ := (Finset.mem_filter.mp hb).2
    have hpT := (Finset.mem_filter.mp hp).1
    have hlabel := (Finset.mem_filter.mp hp).2
    have hCp' := hCp
    rw [hCdef] at hCp'
    let Lb (i : Fin 3) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
    let Rb (i : Fin 3) : ℝ := min (x ^ ((9 : ℝ) / 10))
      ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ)
    have hscales := small_prime_geometric_active_scales (arity := 2) (by decide)
      x h hx2 hh hh1 b p (Fintype.mem_piFinset.mp hpT)
        (fun i => congrFun hlabel i) hCp'.1
    have hU : U b = Fintype.piFinset (fun i : Fin 3 =>
        (Finset.Icc ⌈Lb i⌉₊ ⌊Rb i⌋₊).filter Nat.Prime) := by
      have hboxes := (finite_small_prime_box_cut_decomposition P bin C).1 b
      change U b = Fintype.piFinset
        (fun i : Fin 3 => P.filter (fun p => bin p = b i)) at hboxes
      rw [hboxes]
      congr 1
      funext i
      exact small_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)
    have hpLU (i : Fin 3) : Lb i ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ Rb i ∧ Rb i ≤ 2 * Lb i := by
      have hpbox : p ∈ Fintype.piFinset (fun i : Fin 3 =>
          (Finset.Icc ⌈Lb i⌉₊ ⌊Rb i⌋₊).filter Nat.Prime) := hU ▸ hp
      have hpi := Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hpbox i)).1
      have hRb : 0 ≤ Rb i := le_min (Real.rpow_nonneg hx0.le _) (Nat.cast_nonneg _)
      exact ⟨Nat.ceil_le.mp hpi.1, (Nat.le_floor_iff hRb).mp hpi.2,
        (hscales.1 i).2.2⟩
    have hprod : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x :=
      (Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)).mp (Finset.mem_Icc.mp hCp'.1).2
    have hwide := hnearby x hxn p (hprime p hpT) hprod hCp'.2 Lb Rb hpLU
    have hcoeff : ((primeIntervalBoxAlgebra Lb Rb Finset.univ).coeff.filter R) = Fbox b := by
      have hbase : (primeIntervalBoxAlgebra Lb Rb Finset.univ).coeff =
          ∑ p ∈ U b, Finsupp.single (∏ i, p i) (1 : ℂ) := by
        simpa only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, hU] using
          congrArg (fun f : MonoidAlgebra ℂ ℕ => f.coeff)
            (primeIntervalBoxAlgebra_univ_eq_tuple_sum Lb Rb)
      rw [hbase, Finsupp.filter_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hr : R (∏ i, q i)
      · rw [Finsupp.filter_single_of_pos R hr, ite_eq_left hr]
      · rw [Finsupp.filter_single_of_neg R hr, ite_eq_right hr, Finsupp.single_zero]
    have hb' := hbox x hxb Lb Rb (fun i => (hwide i).1)
      (fun i => ⟨(hscales.1 i).2.1, (hscales.1 i).2.2⟩)
      (fun i => (hwide i).2.1) I hI a₀ ha
    change (∑ q ∈ Q, ‖fullDiscrepancy
      ((primeIntervalBoxAlgebra Lb Rb Finset.univ).coeff.filter (fun n => n ∈ N)) q a₀‖) ≤ _ at hb'
    have hcoeffN :
        ((primeIntervalBoxAlgebra Lb Rb Finset.univ).coeff.filter (fun n => n ∈ N)) =
          Fbox b := by
      simpa only [hRdef] using hcoeff
    rw [hcoeffN] at hb'
    exact hb'
  have hinterior :
      (∑ b ∈ V, ∑ q ∈ Q, ‖fullDiscrepancy (Fbox b) q a₀‖) ≤
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
    apply boolean_small_monomial_mixed_geometric_box_card
      (arity := 2) (by decide) x h hx2 hh hh1 M C hM hboolean
    intro p hp hCp
    have hN := hCR p hp hCp
    rw [hRdef] at hN
    exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hN).2).trans
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
  have hcover := finite_small_prime_box_relative_discrepancy_cover
    (arity := 2) P bin C R hCR Q (fun _ => a₀)
  exact hcover.trans ((add_le_add hinterior hboundary).trans_eq harith)

#print axioms sourceT3_closed_prime_boxes_log_saving_of_analytic_inputs
#print axioms sourceT3_selected_dense_log_saving_of_analytic_inputs

end PrimeGap182Analytic.Harman
