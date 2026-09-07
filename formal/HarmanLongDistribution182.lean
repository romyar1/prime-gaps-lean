import HarmanLongIdentity182
import HarmanLongCells182

/-!
# Actual long remainder distribution from the common bilinear estimate

The conclusion is the full finite-modulus discrepancy estimate for the
actual new sifted-theta remainder. The signed interior, positive boundary,
boundary mass, and totient mean are combined explicitly.

Adapted from the hash-pinned Apache-2.0 public PrimeGaps186 source by
scripts/build_harman_long.py. No original source is modified.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

open Classical in
theorem sifted_long_pure_power_distribution_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ) (hω : 0 < «ω») (hδ : 0 < δ) (hσ : 0 < σ)
    (hωquarter : «ω» ≤ 1 / 4) (hσhalf : σ < 1 / 2)
    (hσa : (1 / 2 : ℝ) - σ < 41361 / 100000)
    (hsource : SourceBilinearEstimate j «ω» δ σ) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ l : Fin 6,
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ArithmeticFunction ℝ :=
        ⟨fun n => if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0, by simp⟩
      let ρx : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n
          (((siftedTheta x l (fun _ => 1) n -
            (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ)) : ℂ)
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
            q ∣ (∏ p ∈ I, p) ∧ Nonempty
              (DenseDivisibilityWitness
                ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ j q)),
          ‖fullDiscrepancy ρx q a‖) ≤ K * x / (Real.log x) ^ A := by
  intro A hA
  have hAmass : 0 < A + 2 := by linarith
  obtain ⟨D, E, hD, hE, Km, Xm, hKm, hXm, hmass⟩ :=
    harman_uniform_boundary_mass_log_saving (A + 2) hAmass
  let J : ℕ := 7 * (D + E + 1)
  let Abox : ℝ := A + (J : ℝ)
  have hAbox : 0 < Abox := by
    dsimp only [Abox]
    exact add_pos_of_pos_of_nonneg hA (Nat.cast_nonneg J)
  obtain ⟨Kb, Xb, hKb, _hXb, hbox⟩ :=
    sifted_long_active_feature_cell_log_saving_of_bilinear j «ω» δ σ
      hω hδ hσ hσhalf hσa hsource Abox hAbox
  let K : ℝ := 2 * (20 : ℝ) ^ 7 * Kb + 56 * Km
  let X : ℝ := max Xm Xb
  have hK : 0 < K := by dsimp only [K]; positivity
  have hX : Real.exp 100 ≤ X := hXm.trans (le_max_left _ _)
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx l
  have hxm : Xm ≤ x := (le_max_left _ _).trans hx
  have hxb : Xb ≤ x := (le_max_right _ _).trans hx
  have hx100 : Real.exp 100 ≤ x := hX.trans hx
  have hxpos : 0 < x := (Real.exp_pos 100).trans_le hx100
  have hxone : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 100)).trans_le hx100
  have hlog100 : 100 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx100
  have hlogone : 1 ≤ Real.log x := by linarith only [hlog100]
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlogone
  have hx2 : Real.exp 2 ≤ x :=
    (Real.exp_le_exp.mpr (by norm_num : (2 : ℝ) ≤ 100)).trans hx100
  let H := x ^ ((41361 : ℝ) / 100000)
  let z := x ^ ((8639 : ℝ) / 50000)
  let M0 := x ^ (1 - (34941 : ℝ) / 100000)
  let S := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
  let Bthreshold := x ^ ((58639 : ℝ) / 100000)
  let U := ⌊8 * x⌋₊
  let C := Finset.Icc 1 U
  let TA := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun a : Fin 3 → ℕ =>
    let u := a 0
    let v := a 1
    let h₀ := a 2
    let r := u * v
    let m := r * h₀
    m ≤ U ∧
      (match l.val with
        | 0 => u = 1 ∧ v = 1
        | 1 | 2 | 3 => u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)
        | 4 => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v
        | _ => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
      (r : ℝ) < H ∧ 1 < h₀ ∧ ((max 1 (h₀.primeFactors.sup id) : ℕ) : ℝ) < z ∧
      ((m / h₀.minFac : ℕ) : ℝ) < H ∧ H ≤ (m : ℝ))
  let TB := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun b : Fin 3 → ℕ =>
    let s := b 0
    let d := b 1
    let k := b 2
    let n := s * d * k
    n ≤ U ∧ (if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S)
  let feature (a b : Fin 3 → ℕ) : Fin 7 → ℕ :=
    ![a 0 * a 1 * a 2, (a 2).minFac, if l.val ≤ 3 then a 1 else a 0,
      b 0 * b 1 * b 2, b 0 * b 1, max 1 ((b 1).primeFactors.sup id), b 0]
  let Good (f : Fin 7 → ℕ) : Prop :=
    f 5 < f 1 ∧ M0 < ((f 0 * f 4 : ℕ) : ℝ) ∧
      x ≤ ((f 0 * f 3 : ℕ) : ℝ) ∧ ((f 0 * f 3 : ℕ) : ℝ) ≤ 2 * x ∧
      match l.val with
      | 2 => f 6 < f 2 ∧ ((f 2 * f 6 : ℕ) : ℝ) < H
      | 3 => f 6 < f 2 ∧ Bthreshold < ((f 2 * f 6 : ℕ) : ℝ)
      | 4 => f 6 < f 2
      | 5 => f 2 < f 6
      | _ => True
  let S0 : ArithmeticFunction ℝ :=
    ⟨fun n => if (n : ℝ) ≤ M0 then
      ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0, by simp⟩
  let ρx : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    Finsupp.single n
      ((siftedTheta x l (fun _ => 1) n -
        (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
  let T := TA ×ˢ TB
  let value (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) :=
    feature t.1 t.2 0 * feature t.1 t.2 3
  let weight (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : ℝ :=
    (ArithmeticFunction.moebius (t.1 2) : ℝ) *
      (ArithmeticFunction.moebius (t.2 1) : ℝ)
  let good (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : Prop := Good (feature t.1 t.2)
  have hfeature (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) (ht : t ∈ T) :
      ∀ r : Fin 7, 1 ≤ feature t.1 t.2 r ∧ feature t.1 t.2 r ≤ U := by
    clear hmass hbox
    obtain ⟨hta, htb⟩ := Finset.mem_product.mp ht
    obtain ⟨hpa, hca⟩ := Finset.mem_filter.mp hta
    obtain ⟨hpb, hcb⟩ := Finset.mem_filter.mp htb
    exact harman_long_feature_bounds l U t.1 t.2
      (fun i => Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hpa) i))
      (fun i => Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hpb) i))
      hca.1 hcb.1
  have hρ : ρx = ∑ t ∈ T, Finsupp.single (value t)
      (if good t then (weight t : ℂ) else 0) := by
    clear hmass hbox
    have hid := sifted_long_independent_factor_identity x hxone l
    change ρx = ∑ a ∈ TA, ∑ d ∈ TB,
      Finsupp.single (feature a d 0 * feature a d 3)
        ((if Good (feature a d) then
          (ArithmeticFunction.moebius (a 2) : ℝ) *
            (ArithmeticFunction.moebius (d 1) : ℝ) else 0 : ℝ) : ℂ) at hid
    rw [hid]
    change _ = ∑ t ∈ TA ×ˢ TB, Finsupp.single (value t)
      (if good t then (weight t : ℂ) else 0)
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro d _hd
    congr 1
    change ((if Good (feature a d) then weight (a, d) else 0 : ℝ) : ℂ) =
      if Good (feature a d) then (weight (a, d) : ℂ) else 0
    split_ifs <;> rfl
  let L : ℕ := ⌊Real.log x⌋₊ ^ E
  let h : ℝ := (Real.log x) ^ (-(D : ℝ))
  have hU : 1 ≤ U := Nat.le_floor
    (show ((1 : ℕ) : ℝ) ≤ 8 * x by norm_num; linarith only [hxone])
  have hL : 1 ≤ L := one_le_pow₀
    (Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Real.log x by
      simpa only [Nat.cast_one] using hlogone))
  have hh : 0 < h := Real.rpow_pos_of_pos hlogpos _
  have hh1 : h ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlogone (neg_nonpos.mpr (Nat.cast_nonneg D))
  obtain ⟨N, b, lo, hi, hN, hindex, hcell, hsingleton, hlow,
    _hopenends, _hhighends, horder, hdiameter, hlowends, hends⟩ :=
      harman_positive_feature_mesh U L h hU hL hh hh1
  let key (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : Fin 7 → ℕ :=
    fun r => b (feature t.1 t.2 r)
  let labels := T.image key
  let cell (c : Fin 7 → ℕ) := T.filter (fun t => key t = c)
  let interior := labels.filter (fun c => ∀ t ∈ cell c, good t)
  let boundary := labels.filter (fun c =>
    (∃ t ∈ cell c, good t) ∧ ∃ t ∈ cell c, ¬good t)
  let signed (c : Fin 7 → ℕ) : ℕ →₀ ℂ :=
    ∑ t ∈ cell c, Finsupp.single (value t) (weight t : ℂ)
  let positive (c : Fin 7 → ℕ) : ℕ →₀ ℂ :=
    ∑ t ∈ cell c, Finsupp.single (value t) ((|weight t| : ℝ) : ℂ)
  have hlabelcard : labels.card ≤ N ^ 7 :=
    harman_seven_feature_label_card_le T (fun t => feature t.1 t.2)
      U N b hfeature hindex
  have hlabelpoly : (N : ℝ) ^ 7 ≤ (20 : ℝ) ^ 7 * (Real.log x) ^ J :=
    harman_feature_mesh_seven_label_polylog D E hD hE x hx2 N hN
  have hmassx := hmass x hxm
  have hboundarymass :
      (∑ c ∈ boundary, ∑ t ∈ cell c, |weight t|) ≤
        7 * Km * x / (Real.log x) ^ (A + 2) :=
    harman_long_mixed_cell_mass_le x (A + 2) Km h L l
      hx100 hL hh.le hh1 hmassx.1 hmassx.2 b lo hi
      hlow hsingleton horder hdiameter hends
  clear hmass hmassx
  change ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
    ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
      (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧ Nonempty
            (DenseDivisibilityWitness
              ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ j q)),
        ‖fullDiscrepancy ρx q a‖) ≤ K * x / (Real.log x) ^ A
  intro I hI a ha
  let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
    q ∣ (∏ p ∈ I, p) ∧ Nonempty
      (DenseDivisibilityWitness
        ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ j q))
  change (∑ q ∈ Q, ‖fullDiscrepancy ρx q a‖) ≤ K * x / (Real.log x) ^ A
  have hcover := signed_finite_box_discrepancy_cover T key value weight good Q (fun _ => a)
  change (∑ q ∈ Q,
      ‖fullDiscrepancy
        (∑ t ∈ T, Finsupp.single (value t) (if good t then (weight t : ℂ) else 0))
        q a‖) ≤
      (∑ c ∈ interior, ∑ q ∈ Q, ‖fullDiscrepancy (signed c) q a‖) +
        (∑ c ∈ boundary, ∑ q ∈ Q, ‖fullDiscrepancy (positive c) q a‖) +
        2 * (∑ c ∈ boundary, ∑ t ∈ cell c, |weight t|) *
          ∑ q ∈ Q, 1 / (q.totient : ℝ) at hcover
  rw [← hρ] at hcover
  have hactive (c : Fin 7 → ℕ)
      (hc : (∃ t ∈ cell c, good t)) :
      ∃ a ∈ TA, ∃ d ∈ TB, Good (feature a d) ∧
        ∀ r : Fin 7, b (feature a d r) = c r := by
    obtain ⟨t, ht, hgood⟩ := hc
    obtain ⟨htT, htc⟩ := Finset.mem_filter.mp ht
    obtain ⟨hta, htd⟩ := Finset.mem_product.mp htT
    exact ⟨t.1, hta, t.2, htd, hgood, fun r => congrFun htc r⟩
  have hactiveInterior (c : Fin 7 → ℕ) (hc : c ∈ interior) :
      ∃ t ∈ cell c, good t := by
    obtain ⟨hcLabel, hcGood⟩ := Finset.mem_filter.mp hc
    obtain ⟨t, ht, htc⟩ := Finset.mem_image.mp hcLabel
    have htcell : t ∈ cell c := Finset.mem_filter.mpr ⟨ht, htc⟩
    exact ⟨t, htcell, hcGood t htcell⟩
  have hfiltered (c : Fin 7 → ℕ)
      (f : ((Fin 3 → ℕ) × (Fin 3 → ℕ)) → ℂ) :
      (∑ t ∈ cell c, Finsupp.single (value t) (f t)) =
        ∑ aa ∈ TA, ∑ d ∈ TB,
          Finsupp.single (feature aa d 0 * feature aa d 3)
            (if ∀ r : Fin 7, b (feature aa d r) = c r then f (aa, d) else 0) := by
    change (∑ t ∈ T.filter (fun t => key t = c),
      Finsupp.single (value t) (f t)) = _
    rw [Finset.sum_filter]
    change (∑ t ∈ TA ×ˢ TB,
      if key t = c then Finsupp.single (value t) (f t) else 0) = _
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro aa _haa
    apply Finset.sum_congr rfl
    intro d _hd
    by_cases heq : key (aa, d) = c
    · have heq' : ∀ r : Fin 7, b (feature aa d r) = c r :=
        fun r => congrFun heq r
      simp only [ite_eq_left heq, ite_eq_left heq']
      rfl
    · have heq' : ¬∀ r : Fin 7, b (feature aa d r) = c r :=
        fun heq' => heq (funext heq')
      simp only [ite_eq_right heq, ite_eq_right heq', Finsupp.single_zero]
  have hcellbound (c : Fin 7 → ℕ) (hc : ∃ t ∈ cell c, good t)
      (takeAbs : Bool) :
      (∑ q ∈ Q,
        ‖fullDiscrepancy
          (∑ t ∈ cell c, Finsupp.single (value t)
            ((if takeAbs then |weight t| else weight t : ℝ) : ℂ)) q a‖) ≤
        Kb * x / (Real.log x) ^ Abox := by
    have hb := hbox x hxb l L b lo hi h hh hh1 hcell hlowends hends
      c (hactive c hc) takeAbs I hI a ha
    have hcoeff (aa d : Fin 3 → ℕ) :
        ((if takeAbs then |weight (aa, d)| else weight (aa, d) : ℝ) : ℂ) =
          ((if takeAbs then |ArithmeticFunction.moebius (aa 2)|
            else ArithmeticFunction.moebius (aa 2) : ℤ) : ℂ) *
          ((if takeAbs then |ArithmeticFunction.moebius (d 1)|
            else ArithmeticFunction.moebius (d 1) : ℤ) : ℂ) := by
      clear * - aa d takeAbs weight
      cases takeAbs
      · dsimp only [Bool.false_eq_true, ite_false, weight]
        norm_cast
      · simp only [ite_true, weight]
        rw [abs_mul, Complex.ofReal_mul]
        congr 1 <;> norm_cast
    have hF :
        (∑ t ∈ cell c, Finsupp.single (value t)
          ((if takeAbs then |weight t| else weight t : ℝ) : ℂ)) =
          ∑ aa ∈ TA, ∑ d ∈ TB,
            Finsupp.single (feature aa d 0 * feature aa d 3)
              (if ∀ r : Fin 7, b (feature aa d r) = c r then
                ((if takeAbs then |ArithmeticFunction.moebius (aa 2)|
                  else ArithmeticFunction.moebius (aa 2) : ℤ) : ℂ) *
                ((if takeAbs then |ArithmeticFunction.moebius (d 1)|
                  else ArithmeticFunction.moebius (d 1) : ℤ) : ℂ)
                else 0) := by
      rw [hfiltered]
      apply Finset.sum_congr rfl
      intro aa _haa
      apply Finset.sum_congr rfl
      intro d _hd
      rw [hcoeff aa d]
    rw [hF]
    exact hb
  have hIbound (c : Fin 7 → ℕ) (hc : c ∈ interior) :
      (∑ q ∈ Q, ‖fullDiscrepancy (signed c) q a‖) ≤
        Kb * x / (Real.log x) ^ Abox := by
    simpa only [Bool.false_eq_true, ite_false] using
      hcellbound c (hactiveInterior c hc) false
  have hDbound (c : Fin 7 → ℕ) (hc : c ∈ boundary) :
      (∑ q ∈ Q, ‖fullDiscrepancy (positive c) q a‖) ≤
        Kb * x / (Real.log x) ^ Abox := by
    simpa only [Bool.coe_sort_true, ite_true] using
      hcellbound c (Finset.mem_filter.mp hc).2.1 true
  clear hbox hcellbound hactive hactiveInterior hfiltered
  have hbudget : 0 ≤ Kb * x / (Real.log x) ^ Abox := by
    clear * - Kb x Abox hKb hxpos hlogpos
    positivity
  have hinteriorcard : (interior.card : ℝ) ≤ (N : ℝ) ^ 7 := by
    have hc : interior.card ≤ labels.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast hc.trans hlabelcard
  have hboundarycard : (boundary.card : ℝ) ≤ (N : ℝ) ^ 7 := by
    have hc : boundary.card ≤ labels.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast hc.trans hlabelcard
  have hlevel : 0 < (1 / 2 : ℝ) + 2 * «ω» ∧ (1 / 2 : ℝ) + 2 * «ω» ≤ 1 := by
    constructor <;> linarith only [hω, hωquarter]
  have htotient :
      (∑ q ∈ Q, 1 / (q.totient : ℝ)) ≤ 4 * (Real.log x) ^ 2 :=
    harman_dense_moduli_inv_totient_le x (1 / 2 + 2 * «ω»)
      hx100 hlevel.1 hlevel.2 Q (Finset.filter_subset _ _)
  have htotientnonneg : 0 ≤ ∑ q ∈ Q, 1 / (q.totient : ℝ) :=
    Finset.sum_nonneg fun q _ => by positivity
  clear_value key labels cell interior boundary signed positive Q
  clear * - hcover hIbound hDbound hinteriorcard hboundarycard hlabelpoly
    hboundarymass hbudget htotient htotientnonneg hlogpos hKb hKm hxpos
  have hsumInterior :
      (∑ c ∈ interior, ∑ q ∈ Q, ‖fullDiscrepancy (signed c) q a‖) ≤
        (N : ℝ) ^ 7 * (Kb * x / (Real.log x) ^ Abox) := by
    calc
      _ ≤ ∑ _c ∈ interior, Kb * x / (Real.log x) ^ Abox :=
        Finset.sum_le_sum hIbound
      _ = (interior.card : ℝ) * (Kb * x / (Real.log x) ^ Abox) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hinteriorcard hbudget
  have hsumBoundary :
      (∑ c ∈ boundary, ∑ q ∈ Q, ‖fullDiscrepancy (positive c) q a‖) ≤
        (N : ℝ) ^ 7 * (Kb * x / (Real.log x) ^ Abox) := by
    calc
      _ ≤ ∑ _c ∈ boundary, Kb * x / (Real.log x) ^ Abox :=
        Finset.sum_le_sum hDbound
      _ = (boundary.card : ℝ) * (Kb * x / (Real.log x) ^ Abox) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hboundarycard hbudget
  have hpolyCancellation :
      ((20 : ℝ) ^ 7 * (Real.log x) ^ J) *
          (Kb * x / (Real.log x) ^ Abox) =
        (20 : ℝ) ^ 7 * Kb * x / (Real.log x) ^ A := by
    clear * - A J Abox Kb x hlogpos
    dsimp only [Abox]
    rw [Real.rpow_add hlogpos, Real.rpow_natCast]
    field_simp [hlogpos.ne', (Real.rpow_pos_of_pos hlogpos A).ne']
  have hsinglebudget :
      (N : ℝ) ^ 7 * (Kb * x / (Real.log x) ^ Abox) ≤
        (20 : ℝ) ^ 7 * Kb * x / (Real.log x) ^ A := by
    calc
      _ ≤ ((20 : ℝ) ^ 7 * (Real.log x) ^ J) *
          (Kb * x / (Real.log x) ^ Abox) :=
        mul_le_mul_of_nonneg_right hlabelpoly hbudget
      _ = _ := hpolyCancellation
  have hmeanbound :
      2 * (∑ c ∈ boundary, ∑ t ∈ cell c, |weight t|) *
          (∑ q ∈ Q, 1 / (q.totient : ℝ)) ≤
        56 * Km * x / (Real.log x) ^ A := by
    calc
      _ ≤ 2 * (7 * Km * x / (Real.log x) ^ (A + 2)) *
          (4 * (Real.log x) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hboundarymass (by norm_num))
          htotient htotientnonneg (by positivity)
      _ = _ := by
        clear * - x A Km hlogpos
        rw [Real.rpow_add hlogpos, Real.rpow_two]
        field_simp [hlogpos.ne', (Real.rpow_pos_of_pos hlogpos A).ne']
        ring
  calc
    _ ≤ (∑ c ∈ interior, ∑ q ∈ Q, ‖fullDiscrepancy (signed c) q a‖) +
        (∑ c ∈ boundary, ∑ q ∈ Q, ‖fullDiscrepancy (positive c) q a‖) +
        2 * (∑ c ∈ boundary, ∑ t ∈ cell c, |weight t|) *
          ∑ q ∈ Q, 1 / (q.totient : ℝ) := hcover
    _ ≤ ((20 : ℝ) ^ 7 * Kb * x / (Real.log x) ^ A) +
        ((20 : ℝ) ^ 7 * Kb * x / (Real.log x) ^ A) +
        56 * Km * x / (Real.log x) ^ A :=
      add_le_add (add_le_add (hsumInterior.trans hsinglebudget)
        (hsumBoundary.trans hsinglebudget)) hmeanbound
    _ = K * x / (Real.log x) ^ A := by
      clear * - A Km Kb K x
      dsimp only [K]
      ring

#print axioms sifted_long_pure_power_distribution_of_bilinear

end PrimeGap182Analytic.Harman

end
