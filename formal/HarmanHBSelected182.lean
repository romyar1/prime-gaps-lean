import HarmanHBAnalytic182

/-! Selected Heath-Brown boxes at the actual new source geometry.
This applies the proved coefficient trichotomy and accounts for every
localized box and its logarithmic multiplicity. The explicit global
analytic arguments remain to be supplied by the local-to-global modules.
Adapted from Apache-2.0 PrimeGaps186; the generator checks its source hash. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sourceT3_coefficient_case_log_saving_of_analytic_inputs
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ (1 / 10 ^ 10 : ℝ))
    (density : ℕ) (hdensity : 1 ≤ density) (orders : Fin 3 → Fin 5)
    (D : ℕ) (hD : 1 ≤ D) («ω» δ : ℝ)
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
        ∀ x : ℝ, X ≤ x →
          let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
          ∀ t : Fin 3 → ℝ, (∀ c, 0 ≤ t c) → (∀ c, t c ≤ 10) →
          ∀ ν : (c : Fin 3) → Fin (2 * ((orders c).val + 1)) → ℕ,
            ν ∈ Fintype.piFinset (fun c : Fin 3 =>
              minorantHBBoxes ((orders c).val + 1)
                (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ) →
            let ιr := Σ c : Fin 3, Fin (2 * ((orders c).val + 1))
            let β : ιr → MonoidAlgebra ℂ ℕ := fun s =>
              minorantHBLocalizedSlot ((orders s.1).val + 1) (x ^ (9 / 100 : ℝ))
                Θ (t s.1) (ν s.1) s.2
            (∃ n : ℕ, x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 3 * x ∧
              (∏ s, β s).coeff n ≠ 0) →
            ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
            ∀ a₀ : ℕ, Nat.Coprime a₀ (∏ p ∈ I, p) →
              (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
                  q ∣ (∏ p ∈ I, p) ∧
                    Nonempty (DenseDivisibilityWitness
                      ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q)),
                ‖fullDiscrepancy (∏ s, β s).coeff q a₀‖) ≤
                  K * x / (Real.log x) ^ A := by
  intro a ζ σclass γ₀ σdist σIII hσσ hσdistHalf hσIIIlo hσIIIhi hgap hdist
  have hmiddleGeometry :
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (Ni : ι → ℝ) (x Cbase b : ℝ),
        (∀ i, 1 ≤ Ni i) → 1 < x → 1 < Cbase →
        2 * Cbase < x ^ b → x / Cbase ≤ ∏ i, Ni i →
        ∀ S : Finset ι,
          b ≤ ∑ i ∈ S, Real.logb x (Ni i) →
          (∑ i ∈ S, Real.logb x (Ni i)) ≤ 1 - b →
          ∃ S' T' : Finset ι,
            Disjoint S' T' ∧ S' ∪ T' = Finset.univ ∧
            S'.Nonempty ∧ T'.Nonempty ∧
            x ^ b / (2 * Cbase) < ∏ i ∈ S', Ni i ∧
            (∏ i ∈ S', Ni i) ≤ ∏ i ∈ T', Ni i := by
    intro ι _ _ Ni x Cbase b hNi hx hC hlarge hP S hSlo hShi
    classical
    have hxpos : 0 < x := zero_lt_one.trans hx
    have hCpos : 0 < Cbase := zero_lt_one.trans hC
    have hNpos (i : ι) : 0 < Ni i := zero_lt_one.trans_le (hNi i)
    let A : ℝ := ∏ i ∈ S, Ni i
    let B : ℝ := ∏ i ∈ Sᶜ, Ni i
    have hApos : 0 < A := Finset.prod_pos fun i _ => hNpos i
    have hBpos : 0 < B := Finset.prod_pos fun i _ => hNpos i
    have hprod : A * B = ∏ i, Ni i := Finset.prod_mul_prod_compl S Ni
    have hlog : Real.logb x A = ∑ i ∈ S, Real.logb x (Ni i) :=
      Real.logb_prod S Ni fun i _ => (hNpos i).ne'
    have hAlo : x ^ b ≤ A :=
      (Real.le_logb_iff_rpow_le hx hApos).mp (hSlo.trans_eq hlog.symm)
    have hAhi : A ≤ x ^ (1 - b) :=
      (Real.logb_le_iff_le_rpow hx hApos).mp (hlog.trans_le hShi)
    have hBbound : x ^ b / Cbase ≤ B := by
      apply (div_le_iff₀ hCpos).2
      apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hxpos (1 - b))).1
      calc
        x ^ b * x ^ (1 - b) = x := by
          rw [← Real.rpow_add hxpos, show b + (1 - b) = 1 by ring, Real.rpow_one]
        _ ≤ (A * B) * Cbase := (div_le_iff₀ hCpos).1 (hP.trans_eq hprod.symm)
        _ ≤ (x ^ (1 - b) * B) * Cbase :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hAhi hBpos.le) hCpos.le
        _ = (B * Cbase) * x ^ (1 - b) := by ring
    have hxbpos : 0 < x ^ b := Real.rpow_pos_of_pos hxpos b
    have hAbound : x ^ b / Cbase ≤ A :=
      (div_le_self hxbpos.le hC.le).trans hAlo
    have hstrict : x ^ b / (2 * Cbase) < x ^ b / Cbase :=
      div_lt_div_of_pos_left hxbpos hCpos (by linarith)
    have hAstrict : x ^ b / (2 * Cbase) < A := hstrict.trans_le hAbound
    have hBstrict : x ^ b / (2 * Cbase) < B := hstrict.trans_le hBbound
    have hthreshold : 1 < x ^ b / (2 * Cbase) :=
      (lt_div_iff₀ (mul_pos zero_lt_two hCpos)).2 (by simpa using hlarge)
    have hnonempty (U : Finset ι)
        (hU : x ^ b / (2 * Cbase) < ∏ i ∈ U, Ni i) : U.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hUempty
      exact (lt_irrefl (1 : ℝ)) (by simpa [hUempty] using hthreshold.trans hU)
    rcases le_total A B with hAB | hBA
    · exact ⟨S, Sᶜ, disjoint_compl_right, Finset.union_compl S,
        hnonempty S hAstrict, hnonempty Sᶜ hBstrict, hAstrict, hAB⟩
    · refine ⟨Sᶜ, S, disjoint_compl_left, ?_,
        hnonempty Sᶜ hBstrict, hnonempty S hAstrict, hBstrict, hBA⟩
      simpa only [Finset.union_comm] using Finset.union_compl S
  let Cbase : ℝ := 3 * (2 : ℝ) ^ 30
  let C0 : ℝ := 2 * Cbase
  have hCbase : 1 < Cbase := by norm_num [Cbase]
  have hCbasepos : 0 < Cbase := zero_lt_one.trans hCbase
  have hC0 : 1 ≤ C0 := by norm_num [C0, Cbase]
  have hCbaseC0 : Cbase ≤ C0 := by dsimp only [C0]; linarith
  have hσclass : 0 < σclass := by dsimp only [σclass, a]; linarith only [hτ, hτsmall]
  have hσclassHalf : σclass < 1 / 2 := by dsimp only [σclass, a]; linarith only [hτ, hτsmall]
  have hγ₀ : 0 < γ₀ := by dsimp only [γ₀]; linarith only [hτ, hτsmall]
  have hγ₀hi : γ₀ ≤ 1 / 2 := by dsimp only [γ₀]; linarith only [hτ, hτsmall]
  have hσIIIhalf : σIII < 1 / 2 := by
    linarith only [hσIIIhi, hτ]
  have hb : 0 < a - τ := by dsimp only [a]; linarith only [hτ, hτsmall]
  obtain ⟨Xcase, hXcase, hcases⟩ :=
    minorantHB_three_unmasked_coefficient_cases τ hτ hτsmall
  obtain ⟨Xlarge, hlarge⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hb).eventually_gt_atTop C0)
  intro A hA
  obtain ⟨Kone, Xone, hKone, hXone, hone⟩ :=
    sourceT3_one_smooth_slot_log_saving density hdensity orders D hD
      «ω» δ γ₀ C0 hω hδ hγ₀ hγ₀hi hC0 hgap A hA
  obtain ⟨Kmid, Xmid, hKmid, _, hmid⟩ :=
    sourceT3_middle_slots_log_saving_of_bilinear density orders D hD
      «ω» δ σclass σdist C0 hω hδ hσclass hσclassHalf hσσ
      hσdistHalf hC0 hdist A hA
  obtain ⟨Kthree, Xthree, hKthree, _, hthree⟩ :=
    sourceT3_three_smooth_slots_log_saving_of_global density hdensity D hD
      «ω» δ σIII C0 hω hωupper hδ hσIIIhalf hC0 hσIIIlo A hA
  refine ⟨Kone + Kmid + Kthree,
    max Xone (max Xmid (max Xthree (max Xcase Xlarge))), by positivity,
    hXone.trans (le_max_left _ _), ?_⟩
  intro x hx Θ t ht htten ν hν ιr β hactive I hI a₀ ha
  let Ni : ιr → ℝ := fun s => Θ ^ ν s.1 s.2
  have hxone : Xone ≤ x := (le_max_left _ _).trans hx
  have hxrest : max Xmid (max Xthree (max Xcase Xlarge)) ≤ x :=
    (le_max_right _ _).trans hx
  have hxmid : Xmid ≤ x := (le_max_left _ _).trans hxrest
  have hxrest' : max Xthree (max Xcase Xlarge) ≤ x :=
    (le_max_right _ _).trans hxrest
  have hxthree : Xthree ≤ x := (le_max_left _ _).trans hxrest'
  have hxlast : max Xcase Xlarge ≤ x := (le_max_right _ _).trans hxrest'
  have hxcase : Xcase ≤ x := (le_max_left _ _).trans hxlast
  have hxlarge : Xlarge ≤ x := (le_max_right _ _).trans hxlast
  have hxTwo : 2 ≤ x := hXcase.trans hxcase
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hxTwo
  have hxpos : 0 < x := zero_lt_one.trans hxOne
  have hxexp : Real.exp 1 ≤ x := hXone.trans hxone
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hΘ : 1 < Θ :=
    lt_add_of_pos_right 1 (Real.rpow_pos_of_pos hlogpos _)
  have hΘtwo : Θ ≤ 2 := by
    have hD0 : 0 ≤ (D : ℝ) := by exact_mod_cast (Nat.zero_le 1).trans hD
    have hh : (Real.log x) ^ (-(D : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlog (neg_nonpos.mpr hD0)
    change 1 + (Real.log x) ^ (-(D : ℝ)) ≤ 2
    linarith only [hh]
  have hNi (s : ιr) : 1 ≤ Ni s := one_le_pow₀ hΘ.le
  have hNipos (s : ιr) : 0 < Ni s := zero_lt_one.trans_le (hNi s)
  obtain ⟨n, hnlo, hnhi, hn⟩ := hactive
  obtain ⟨hcard30, hclass⟩ :=
    hcases x hxcase Θ hΘ hΘtwo orders t ht htten ν hν n hnlo hnhi hn
  let P : ℝ := ∏ s, Ni s
  have hPpos : 0 < P := Finset.prod_pos fun s _ => hNipos s
  have hslot (s : ιr) : ∀ m ∈ (β s).coeff.support,
      Ni s / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Ni s :=
    (sourceT3_localized_slot_support_norm ((orders s.1).val + 1)
      (x ^ (9 / 100 : ℝ)) Θ (t s.1) (ν s.1) s.2 hΘ hΘtwo (ht s.1)).1
  let Wslot : ℝ := ∑ s : ιr, ∑ m ∈ (β s).coeff.support, ‖(β s).coeff m‖
  have hWslot : 0 ≤ Wslot :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun m _ => norm_nonneg _
  have hslotnorm (s : ιr) (m : ℕ) : ‖(β s).coeff m‖ ≤ Wslot := by
    have hlocal : ‖(β s).coeff m‖ ≤
        ∑ l ∈ (β s).coeff.support, ‖(β s).coeff l‖ := by
      simpa only [Finsupp.sum] using
        Finsupp.single_eval_le_sum (β s).coeff norm_zero norm_nonneg m
    exact hlocal.trans
      (Finset.single_le_sum
        (f := fun u : ιr => ∑ l ∈ (β u).coeff.support, ‖(β u).coeff l‖)
        (fun u _ => Finset.sum_nonneg fun l _ => norm_nonneg _) (Finset.mem_univ s))
  have huniv : (Finset.univ : Finset ιr).Nonempty :=
    ⟨⟨0, ⟨0, by omega⟩⟩, Finset.mem_univ _⟩
  have hsupport := (heathBrown_box_product_support_norm_bound
    Finset.univ huniv β Ni Wslot hWslot
      (fun s _ => hNi s) (fun s _ => hslot s) (fun s _ => hslotnorm s)).1
        n (Finsupp.mem_support_iff.mpr hn)
  change P / (2 : ℝ) ^ Fintype.card ιr ≤ (n : ℝ) ∧
    (n : ℝ) ≤ (2 : ℝ) ^ Fintype.card ιr * P at hsupport
  have hpow30 : (2 : ℝ) ^ Fintype.card ιr ≤ (2 : ℝ) ^ 30 :=
    pow_le_pow_right₀ one_le_two hcard30
  have hpowBase : (2 : ℝ) ^ Fintype.card ιr ≤ Cbase :=
    hpow30.trans (le_mul_of_one_le_left (pow_nonneg zero_le_two _)
      (by norm_num : (1 : ℝ) ≤ 3))
  have hPlower : x / Cbase ≤ P := by
    apply (div_le_iff₀ hCbasepos).2
    calc
      x ≤ (n : ℝ) := hnlo
      _ ≤ (2 : ℝ) ^ Fintype.card ιr * P := hsupport.2
      _ ≤ Cbase * P := mul_le_mul_of_nonneg_right hpowBase hPpos.le
      _ = P * Cbase := mul_comm _ _
  have hPupper : P ≤ Cbase * x := by
    calc
      P ≤ (n : ℝ) * (2 : ℝ) ^ Fintype.card ιr :=
        (div_le_iff₀ (pow_pos zero_lt_two _)).1 hsupport.1
      _ ≤ (3 * x) * (2 : ℝ) ^ 30 :=
        mul_le_mul hnhi hpow30 (pow_nonneg zero_le_two _) (by positivity)
      _ = Cbase * x := by dsimp only [Cbase]; ring
  have hPlower0 : x / C0 ≤ P :=
    (div_le_div_of_nonneg_left hxpos.le hCbasepos hCbaseC0).trans hPlower
  have hPupper0 : P ≤ C0 * x :=
    hPupper.trans (mul_le_mul_of_nonneg_right hCbaseC0 hxpos.le)
  have hslotUpper (s : ιr) : Ni s ≤ C0 * Real.sqrt x := by
    have hνc := Fintype.mem_piFinset.mp hν s.1
    dsimp only [minorantHBBoxes] at hνc
    have hboxUpper := (Finset.mem_filter.mp hνc).2.2
    have hslots : 2 * ((orders s.1).val + 1) ≤ 10 := by
      have hh := (orders s.1).isLt
      omega
    have hΘpow : Θ ^ (2 * ((orders s.1).val + 1)) ≤ (2 : ℝ) ^ 10 :=
      (pow_le_pow_left₀ (zero_lt_one.trans hΘ).le hΘtwo _).trans
        (pow_le_pow_right₀ one_le_two hslots)
    have hxpow : x ^ (a + τ / 10) ≤ x ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hxOne.le (by dsimp only [a]; linarith only [hτ, hτsmall])
    calc
      Ni s ≤ ∏ i : Fin (2 * ((orders s.1).val + 1)), Θ ^ ν s.1 i :=
        Multiset.mem_le_prod_of_one_le (s := Finset.univ.val)
          (fun i => one_le_pow₀ hΘ.le) (Finset.mem_univ s.2)
      _ ≤ x ^ (a + τ / 10) * Θ ^ (2 * ((orders s.1).val + 1)) := hboxUpper
      _ ≤ x ^ (1 / 2 : ℝ) * (2 : ℝ) ^ 10 :=
        mul_le_mul hxpow hΘpow (pow_nonneg (zero_lt_one.trans hΘ).le _)
          (Real.rpow_nonneg hxpos.le _)
      _ = (2 : ℝ) ^ 10 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]; ring
      _ ≤ C0 * Real.sqrt x :=
        mul_le_mul_of_nonneg_right (by norm_num [C0, Cbase]) (Real.sqrt_nonneg x)
  let Err : ℝ :=
    ∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
        q ∣ (∏ p ∈ I, p) ∧
          Nonempty (DenseDivisibilityWitness
            ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q)),
      ‖fullDiscrepancy (∏ s, β s).coeff q a₀‖
  change Err ≤ (Kone + Kmid + Kthree) * x / (Real.log x) ^ A
  have hpromote (K : ℝ) (hK : K ≤ Kone + Kmid + Kthree)
      (h : Err ≤ K * x / (Real.log x) ^ A) :
      Err ≤ (Kone + Kmid + Kthree) * x / (Real.log x) ^ A :=
    h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK hxpos.le) (Real.rpow_nonneg hlogpos.le A))
  rcases hclass with honeCase | hmidCase | hthreeCase
  · obtain ⟨s, hs, hscale⟩ := honeCase
    have hsLower : x ^ γ₀ ≤ Ni s :=
      (Real.le_logb_iff_rpow_le hxOne (hNipos s)).mp hscale
    exact hpromote Kone (by linarith only [hKmid, hKthree])
      (hone x hxone t ht htten ν hPlower0 hPupper0 s hs hsLower (hslotUpper s) I hI a₀ ha)
  · obtain ⟨S, hSlo, hShi⟩ := hmidCase
    have hShi' : (∑ s ∈ S, Real.logb x (Ni s)) ≤ 1 - (a - τ) := by
      have ha : (58639 / 100000 : ℝ) + τ = 1 - (a - τ) := by
        dsimp only [a]
        ring
      exact hShi.trans_eq ha
    obtain ⟨S', T', hdisj, hunion, hSne, hTne, hSmall, hST⟩ :=
      hmiddleGeometry Ni x Cbase (a - τ) hNi hxOne hCbase
        (hlarge x hxlarge) hPlower S hSlo hShi'
    have hSmall' : x ^ (1 / 2 - σclass) / C0 < ∏ s ∈ S', Ni s := by
      have he : (1 / 2 : ℝ) - σclass = a - τ := by
        dsimp only [σclass]
        ring
      simpa only [he, C0] using hSmall
    exact hpromote Kmid (by linarith only [hKone, hKthree])
      (hmid x hxmid t ht htten ν hPlower0 hPupper0 S' T' hdisj hunion hSne hTne
        hSmall' hST I hI a₀ ha)
  · obtain ⟨s₁, s₂, s₃, h12, h13, h23, hμ₁, hμ₂, hμ₃,
      hsize₁, hsize₂, hsize₃, hpair12, hpair13, hpair23⟩ := hthreeCase
    have hpair (s u : ιr)
        (hh : 14659 / 25000 - τ ≤ Real.logb x (Ni s) + Real.logb x (Ni u)) :
        x ^ (1 / 2 + σIII) / C0 ≤ Ni s * Ni u := by
      have hraw : x ^ (14659 / 25000 - τ) ≤ Ni s * Ni u :=
        (Real.le_logb_iff_rpow_le hxOne (mul_pos (hNipos s) (hNipos u))).mp (by
          rw [Real.logb_mul (hNipos s).ne' (hNipos u).ne']
          exact hh)
      calc
        x ^ (1 / 2 + σIII) / C0 ≤ x ^ (1 / 2 + σIII) :=
          div_le_self (Real.rpow_nonneg hxpos.le _) hC0
        _ ≤ x ^ (14659 / 25000 - τ) :=
          Real.rpow_le_rpow_of_exponent_le hxOne.le (by linarith only [hσIIIhi])
        _ ≤ Ni s * Ni u := hraw
    have hupper (s : ιr) (hh : Real.logb x (Ni s) ≤ 10341 / 25000 + τ) :
        Ni s ≤ C0 * x ^ (1 / 2 - σIII) := by
      calc
        Ni s ≤ x ^ (10341 / 25000 + τ) :=
          (Real.logb_le_iff_le_rpow hxOne (hNipos s)).mp hh
        _ ≤ x ^ (1 / 2 - σIII) :=
          Real.rpow_le_rpow_of_exponent_le hxOne.le (by linarith only [hσIIIhi])
        _ ≤ C0 * x ^ (1 / 2 - σIII) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hxpos.le _) hC0
    exact hpromote Kthree (by linarith only [hKone, hKmid])
      (hthree x hxthree orders t ht htten ν hPlower0 hPupper0
        s₁ s₂ s₃ h12 h13 h23 hμ₁ hμ₂ hμ₃
        (hpair s₁ s₂ hpair12) (hpair s₁ s₃ hpair13) (hpair s₂ s₃ hpair23)
        (hupper s₁ hsize₁.2) (hupper s₂ hsize₂.2) (hupper s₃ hsize₃.2) I hI a₀ ha)

open Classical in
theorem sourceT3_selected_boxes_log_saving_of_analytic_inputs
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ (1 / 10 ^ 10 : ℝ))
    (density : ℕ) (hdensity : 1 ≤ density)
    (D : ℕ) (hD : 1 ≤ D) («ω» δ : ℝ)
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
        ∀ x : ℝ, X ≤ x →
          let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
          ∀ t : Fin 3 → ℝ, (∀ c, 0 ≤ t c) → (∀ c, t c ≤ 10) →
          ∀ Awin Bwin : Fin 3 → ℝ,
            (∀ c, x ^ (ζ - τ / 10) ≤ Awin c) →
            (∀ c, Awin c ≤ Bwin c) →
            (∀ c, Bwin c ≤ x ^ (a + τ / 10)) →
          let E : (r : Fin 3 → Fin 5) →
              Finset ((c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ) := fun r =>
            (Fintype.piFinset (fun c : Fin 3 =>
              minorantHBBoxes ((r c).val + 1)
                (Awin c) (Bwin c) Θ)).filter (fun ν =>
              x * Θ ^ 30 ≤ (∏ s : Σ c : Fin 3, Fin (2 * ((r c).val + 1)),
                Θ ^ ν s.1 s.2) ∧
              (∏ s : Σ c : Fin 3, Fin (2 * ((r c).val + 1)), Θ ^ ν s.1 s.2) *
                Θ ^ 30 ≤ 2 * x)
          let β : (r : Fin 3 → Fin 5) →
              ((c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ) →
              (Σ c : Fin 3, Fin (2 * ((r c).val + 1))) → MonoidAlgebra ℂ ℕ :=
            fun r ν s => minorantHBLocalizedSlot ((r s.1).val + 1)
              (x ^ (9 / 100 : ℝ)) Θ (t s.1) (ν s.1) s.2
          let selected : ℕ →₀ ℂ :=
            ∑ r : Fin 3 → Fin 5,
              (∏ c : Fin 3,
                (((-1 : ℝ) ^ (r c).val *
                  ((5 : ℕ).choose ((r c).val + 1) : ℝ) : ℝ) : ℂ)) •
                ∑ ν ∈ E r, (∏ s, β r ν s).coeff
          ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
          ∀ a₀ : ℕ, Nat.Coprime a₀ (∏ p ∈ I, p) →
            (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
                q ∣ (∏ p ∈ I, p) ∧
                  Nonempty (DenseDivisibilityWitness
                    ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q)),
              ‖fullDiscrepancy selected q a₀‖) ≤
                K * x / (Real.log x) ^ A := by
  intro a ζ σclass γ₀ σdist σIII hσσ hσdistHalf hσIIIlo hσIIIhi hgap hdist A hA
  let loss : ℕ := 30 * (D + 1)
  let Abox : ℝ := A + loss
  have hAbox : 0 < Abox := add_pos_of_pos_of_nonneg hA (Nat.cast_nonneg loss)
  have hcases (r : Fin 3 → Fin 5) :=
    sourceT3_coefficient_case_log_saving_of_analytic_inputs τ hτ hτsmall
      density hdensity r D hD «ω» δ hω hωupper hδ
      σdist σIII hσσ hσdistHalf hσIIIlo hσIIIhi hgap hdist Abox hAbox
  choose Kr Xr hKr hXr hcase using hcases
  let ar : (Fin 3 → Fin 5) → ℂ := fun r =>
    ∏ c : Fin 3, (((-1 : ℝ) ^ (r c).val *
      ((5 : ℕ).choose ((r c).val + 1) : ℝ) : ℝ) : ℂ)
  let Ksum : ℝ := 1 + ∑ r : Fin 3 → Fin 5, ‖ar r‖ * Kr r
  have hKsum : 0 < Ksum := by
    have hs : 0 ≤ ∑ r : Fin 3 → Fin 5, ‖ar r‖ * Kr r :=
      Finset.sum_nonneg fun r _ => mul_nonneg (norm_nonneg _) (hKr r).le
    dsimp only [Ksum]
    linarith only [hs]
  let Cgrid : ℝ := 125 * (8 : ℝ) ^ 30
  have hCgrid : 0 < Cgrid := by positivity
  let Xmax : ℝ := (Finset.univ : Finset (Fin 3 → Fin 5)).sup' Finset.univ_nonempty Xr
  have hXrmax (r : Fin 3 → Fin 5) : Xr r ≤ Xmax :=
    Finset.le_sup' Xr (Finset.mem_univ r)
  have hXmax : Real.exp 1 ≤ Xmax :=
    (hXr (fun _ => 0)).trans (hXrmax (fun _ => 0))
  refine ⟨Cgrid * Ksum, Xmax, mul_pos hCgrid hKsum, hXmax, ?_⟩
  intro x hx Θ t ht htten Awin Bwin hAwin hABwin hBwin E β selected I hI a₀ ha
  have hxexp : Real.exp 1 ≤ x := hXmax.trans hx
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxexp
  have hxone : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxexp
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hΘ : 1 < Θ := lt_add_of_pos_right 1 (Real.rpow_pos_of_pos hlogpos _)
  have hΘtwo : Θ ≤ 2 := by
    have hs : (Real.log x) ^ (-(D : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlog (neg_nonpos.mpr (Nat.cast_nonneg D))
    change 1 + (Real.log x) ^ (-(D : ℝ)) ≤ 2
    linarith only [hs]
  have hleft : 1 ≤ x ^ (ζ - τ / 10) :=
    Real.one_le_rpow hxone (by dsimp only [ζ, a]; linarith only [hτ, hτsmall])
  have hwindowLeft (c : Fin 3) : 1 ≤ Awin c := hleft.trans (hAwin c)
  have hboxesMono (c : Fin 3) (j : ℕ) :
      minorantHBBoxes j (Awin c) (Bwin c) Θ ⊆
        minorantHBBoxes j (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ := by
    have hBpos : 0 < Bwin c := (zero_lt_one.trans_le (hwindowLeft c)).trans_le (hABwin c)
    have hceil : ⌈Real.log (Bwin c) / Real.log Θ⌉₊ ≤
        ⌈Real.log (x ^ (a + τ / 10)) / Real.log Θ⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right
        (Real.log_le_log hBpos (hBwin c)) (Real.log_pos hΘ).le)
    intro ν hν
    dsimp only [minorantHBBoxes] at hν ⊢
    obtain ⟨hνgrid, hνlower, hνupper⟩ := Finset.mem_filter.mp hν
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_range.mpr
        ((Finset.mem_range.mp (Fintype.mem_piFinset.mp hνgrid i)).trans_le
          (Nat.add_le_add_right hceil 1))
    · exact (div_le_div_of_nonneg_right (hAwin c)
        (pow_nonneg (zero_lt_one.trans hΘ).le _)).trans hνlower
    · exact hνupper.trans (mul_le_mul_of_nonneg_right (hBwin c)
        (pow_nonneg (zero_lt_one.trans hΘ).le _))
  have hEwide (r : Fin 3 → Fin 5) : E r ⊆
      Fintype.piFinset (fun c : Fin 3 => minorantHBBoxes ((r c).val + 1)
        (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ) := by
    intro ν hν
    have hνbox := (Finset.mem_filter.mp hν).1
    exact Fintype.mem_piFinset.mpr fun c =>
      hboxesMono c ((r c).val + 1) (Fintype.mem_piFinset.mp hνbox c)
  let Q : Finset ℕ := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
    q ∣ (∏ p ∈ I, p) ∧ Nonempty (DenseDivisibilityWitness
      ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q))
  have hbox (r : Fin 3 → Fin 5)
      (ν : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ) (hν : ν ∈ E r) :
      (∑ q ∈ Q, ‖fullDiscrepancy (∏ s, β r ν s).coeff q a₀‖) ≤
        Kr r * x / (Real.log x) ^ Abox := by
    obtain ⟨hνbox, hradial⟩ := Finset.mem_filter.mp hν
    by_cases hzero : (∏ s, β r ν s).coeff = 0
    · simp only [hzero, fullDiscrepancy, progressionMass, reducedMass,
        Finsupp.support_zero, Finset.sum_empty, zero_div, sub_zero,
        norm_zero, Finset.sum_const_zero]
      exact div_nonneg (mul_nonneg (hKr r).le hxpos.le)
        (Real.rpow_nonneg hlogpos.le _)
    · obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hzero
      have hs := minorantHB_three_radial_selected_support
        Awin Bwin t (x ^ (9 / 100 : ℝ)) Θ x hwindowLeft hABwin
        hΘ hΘtwo ht htten r ν hνbox hradial.1 hradial.2 n hn
      exact hcase r x ((hXrmax r).trans hx) t ht htten ν (hEwide r hν)
        ⟨n, hs.1, hs.2.trans (by linarith only [hxpos]),
          Finsupp.mem_support_iff.mp hn⟩ I hI a₀ ha
  let M : ℕ := ⌈Real.log (2 * x) / Real.log Θ⌉₊
  have hMmono :
      ⌈Real.log (x ^ (a + τ / 10)) / Real.log Θ⌉₊ ≤ M := by
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ (Real.log_pos hΘ).le
    apply Real.log_le_log (Real.rpow_pos_of_pos hxpos _)
    exact (Real.rpow_le_rpow_of_exponent_le hxone
      (by dsimp only [a]; linarith only [hτ, hτsmall] : a + τ / 10 ≤ (1 : ℝ))).trans
        (by rw [Real.rpow_one]; linarith only [hxpos])
  have hgrid : (((M + 1 : ℕ) : ℝ) ^ 30) ≤
      (8 : ℝ) ^ 30 * (Real.log x) ^ loss := by
    have hg := heathBrown_geometric_grid_card_bound 30 D x hxexp
    simpa only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.cast_pow, M, loss] using hg
  have hcard (r : Fin 3 → Fin 5) :
      ((E r).card : ℝ) ≤ Cgrid * (Real.log x) ^ loss := by
    have htotal := minorantHB_three_box_count
      (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ
    have hsingle :
        (Fintype.piFinset (fun c : Fin 3 =>
          minorantHBBoxes ((r c).val + 1)
            (x ^ (ζ - τ / 10)) (x ^ (a + τ / 10)) Θ)).card ≤
          125 * (⌈Real.log (x ^ (a + τ / 10)) / Real.log Θ⌉₊ + 1) ^ 30 :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)).trans htotal
    have hncard : (E r).card ≤ 125 * (M + 1) ^ 30 :=
      (Finset.card_le_card (hEwide r)).trans (hsingle.trans
        (Nat.mul_le_mul_left 125 (pow_le_pow_left₀ (Nat.zero_le _)
          (Nat.add_le_add_right hMmono 1) 30)))
    have hrcard : ((E r).card : ℝ) ≤ 125 * (((M + 1 : ℕ) : ℝ) ^ 30) := by
      exact_mod_cast hncard
    exact hrcard.trans (by
      calc
        125 * (((M + 1 : ℕ) : ℝ) ^ 30) ≤
            125 * ((8 : ℝ) ^ 30 * (Real.log x) ^ loss) :=
          mul_le_mul_of_nonneg_left hgrid (by norm_num)
        _ = Cgrid * (Real.log x) ^ loss := by dsimp only [Cgrid]; ring)
  have hcancel : (Real.log x) ^ loss / (Real.log x) ^ Abox =
      1 / (Real.log x) ^ A := by
    dsimp only [Abox]
    rw [Real.rpow_add hlogpos, Real.rpow_natCast]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ)
      ((Real.log x) ^ A) (pow_ne_zero loss hlogpos.ne')
  have hsumBoxes (r : Fin 3 → Fin 5) :
      (∑ ν ∈ E r, ∑ q ∈ Q, ‖fullDiscrepancy (∏ s, β r ν s).coeff q a₀‖) ≤
        Cgrid * Kr r * x / (Real.log x) ^ A := by
    calc
      _ ≤ ((E r).card : ℝ) * (Kr r * x / (Real.log x) ^ Abox) := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (E r)
            (fun ν => ∑ q ∈ Q, ‖fullDiscrepancy (∏ s, β r ν s).coeff q a₀‖)
            (Kr r * x / (Real.log x) ^ Abox) (hbox r)
      _ ≤ (Cgrid * (Real.log x) ^ loss) *
          (Kr r * x / (Real.log x) ^ Abox) :=
        mul_le_mul_of_nonneg_right (hcard r)
          (div_nonneg (mul_nonneg (hKr r).le hxpos.le) (Real.rpow_nonneg hlogpos.le _))
      _ = (Cgrid * Kr r * x) *
          ((Real.log x) ^ loss / (Real.log x) ^ Abox) := by ring
      _ = Cgrid * Kr r * x / (Real.log x) ^ A := by rw [hcancel]; ring
  let Ldisc : ℕ → (ℕ →₀ ℂ) →ₗ[ℂ] ℂ := fun q =>
    Finsupp.linearCombination ℂ (fun n : ℕ =>
      (if n % q = a₀ % q then (1 : ℂ) else 0) -
        (if Nat.Coprime n q then (1 : ℂ) else 0) / (q.totient : ℂ))
  have hLdisc (q : ℕ) (f : ℕ →₀ ℂ) : Ldisc q f = fullDiscrepancy f q a₀ := by
    simp only [Ldisc, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
      fullDiscrepancy, progressionMass, reducedMass, mul_sub, mul_div, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_div]
  have hselected (q : ℕ) :
      fullDiscrepancy selected q a₀ =
        ∑ r : Fin 3 → Fin 5, ar r *
          ∑ ν ∈ E r, fullDiscrepancy (∏ s, β r ν s).coeff q a₀ := by
    rw [← hLdisc q selected]
    simp only [selected, map_sum, map_smul, smul_eq_mul]
    simp only [hLdisc, ar]
  have hnormsum :
      (∑ q ∈ Q, ‖fullDiscrepancy selected q a₀‖) ≤
        ∑ r : Fin 3 → Fin 5, ‖ar r‖ *
          ∑ ν ∈ E r, ∑ q ∈ Q, ‖fullDiscrepancy (∏ s, β r ν s).coeff q a₀‖ := by
    calc
      _ ≤ ∑ q ∈ Q, ∑ r : Fin 3 → Fin 5, ‖ar r‖ *
          ∑ ν ∈ E r, ‖fullDiscrepancy (∏ s, β r ν s).coeff q a₀‖ := by
        apply Finset.sum_le_sum
        intro q _
        rw [hselected]
        refine norm_sum_le_of_le _ fun r _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = ∑ r : Fin 3 → Fin 5, ‖ar r‖ *
          ∑ ν ∈ E r, ∑ q ∈ Q, ‖fullDiscrepancy (∏ s, β r ν s).coeff q a₀‖ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.mul_sum, Finset.sum_comm]
  change (∑ q ∈ Q, ‖fullDiscrepancy selected q a₀‖) ≤
    (Cgrid * Ksum) * x / (Real.log x) ^ A
  calc
    _ ≤ ∑ r : Fin 3 → Fin 5, ‖ar r‖ *
        (Cgrid * Kr r * x / (Real.log x) ^ A) :=
      hnormsum.trans (Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left (hsumBoxes r) (norm_nonneg _))
    _ = Cgrid * (∑ r : Fin 3 → Fin 5, ‖ar r‖ * Kr r) * x /
        (Real.log x) ^ A := by
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
        mul_div_assoc, mul_left_comm, mul_assoc]
    _ ≤ (Cgrid * Ksum) * x / (Real.log x) ^ A :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hCgrid.le)
          hxpos.le) (Real.rpow_nonneg hlogpos.le _)

#print axioms sourceT3_coefficient_case_log_saving_of_analytic_inputs
#print axioms sourceT3_selected_boxes_log_saving_of_analytic_inputs

end PrimeGap182Analytic.Harman
