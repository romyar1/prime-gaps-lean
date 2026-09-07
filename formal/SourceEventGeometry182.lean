import PhysicalSources182

/-!
The nonlinear owner allocation reduces to the linear order-5/2 offender
cover using the actual row plateau.  This is a finite atomic lemma; the
probabilistic event covering and all literal bin inventories are separate.
-/

noncomputable section
open scoped BigOperators
namespace PrimeGap182

theorem trialSource_balanced_failure_of_offender {ι : Type} [Fintype ι]
    (f : ι → ℝ) (a : ι) (k : Fin 3) (R : TrialSourceRow) (cap : ℝ)
    (hpositive : ∀ b, 0 < f b) (hcap : f a ≤ cap)
    (_hC : 0 < (R.innerThreshold : ℝ))
    (hL : 2 < R.order → 3 * (R.innerThreshold : ℝ) ≤ 7 * (R.plateau : ℝ))
    (hcapOwner :
      let L : ℝ := (R.plateau : ℝ)
      if k = 0 then
        if R.order ≤ 2 then 2 * cap ≤ (R.outerThreshold : ℝ)
        else cap + min ((3 / 2) * cap) L ≤ (R.outerThreshold : ℝ) ∧
          3 * cap - min ((3 / 2) * cap) L ≤ (R.innerThreshold : ℝ)
      else
        if R.order ≤ 2 then 2 * cap ≤ (R.innerThreshold : ℝ)
        else cap + (3 * cap - min ((3 / 2) * cap) L) ≤
            (R.innerThreshold : ℝ) ∧
          min ((3 / 2) * cap) L ≤ (R.outerThreshold : ℝ))
    (hfailure :
      let p := f a
      let tail := ∑ b ∈ Finset.univ.filter (fun b : ι => p ≤ f b), f b
      let L : ℝ := (R.plateau : ℝ)
      if k = 0 then
        if R.order ≤ 2 then (R.outerThreshold : ℝ) < tail + p
        else (R.outerThreshold : ℝ) < tail + min ((3 / 2) * p) L ∨
          (R.innerThreshold : ℝ) < 3 * p - min ((3 / 2) * p) L
      else
        if R.order ≤ 2 then (R.innerThreshold : ℝ) < tail + p
        else (R.innerThreshold : ℝ) < tail + (3 * p - min ((3 / 2) * p) L) ∨
          (R.outerThreshold : ℝ) < min ((3 / 2) * p) L) :
    2 ≤ (Finset.univ.filter (fun b : ι => f a ≤ f b)).card ∧
      ((if k = 0 then R.outerThreshold else R.innerThreshold : ℚ) : ℝ) <
        (∑ b ∈ Finset.univ.filter (fun b : ι => f a ≤ f b), f b) +
          (((if R.order ≤ 2 then 2 else 5 / 2 : ℚ) : ℝ) - 1) * f a := by
  classical
  let p := f a
  let I : Finset ι := Finset.univ.filter (fun b : ι => p ≤ f b)
  let tail : ℝ := ∑ b ∈ I, f b
  let L : ℝ := (R.plateau : ℝ)
  have ha : a ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩
  have hp : 0 < p := hpositive a
  have hD : min ((3 / 2) * p) L ≤ min ((3 / 2) * cap) L :=
    min_le_min_right L (mul_le_mul_of_nonneg_left hcap (by norm_num))
  have hE : 3 * p - min ((3 / 2) * p) L ≤
      3 * cap - min ((3 / 2) * cap) L := by
    rw [← max_sub_sub_left, ← max_sub_sub_left]
    apply max_le_max <;> linarith only [hcap]
  have hcapAtP :
      if k = 0 then
        if R.order ≤ 2 then 2 * p ≤ (R.outerThreshold : ℝ)
        else p + min ((3 / 2) * p) L ≤ (R.outerThreshold : ℝ) ∧
          3 * p - min ((3 / 2) * p) L ≤ (R.innerThreshold : ℝ)
      else
        if R.order ≤ 2 then 2 * p ≤ (R.innerThreshold : ℝ)
        else p + (3 * p - min ((3 / 2) * p) L) ≤
            (R.innerThreshold : ℝ) ∧
          min ((3 / 2) * p) L ≤ (R.outerThreshold : ℝ) := by
    by_cases hk : k = 0 <;> by_cases ho : R.order ≤ 2 <;>
      simp only [hk, ho, ↓reduceIte] at hcapOwner ⊢
    · linarith only [hcap, hcapOwner]
    · exact ⟨(add_le_add hcap hD).trans hcapOwner.1, hE.trans hcapOwner.2⟩
    · linarith only [hcap, hcapOwner]
    · exact ⟨(add_le_add hcap hE).trans hcapOwner.1, hD.trans hcapOwner.2⟩
  have htwo : 2 ≤ I.card := by
    by_contra hsmall
    have hI : I = {a} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨ha, fun b hb => Finset.card_le_one.mp (by omega) b hb a ha⟩
    have htail : tail = p := by simp only [tail, hI, Finset.sum_singleton, p]
    change (if k = 0 then
      if R.order ≤ 2 then (R.outerThreshold : ℝ) < tail + p
      else (R.outerThreshold : ℝ) < tail + min ((3 / 2) * p) L ∨
        (R.innerThreshold : ℝ) < 3 * p - min ((3 / 2) * p) L
      else if R.order ≤ 2 then (R.innerThreshold : ℝ) < tail + p
      else (R.innerThreshold : ℝ) < tail + (3 * p - min ((3 / 2) * p) L) ∨
        (R.outerThreshold : ℝ) < min ((3 / 2) * p) L) at hfailure
    rw [htail] at hfailure
    by_cases hk : k = 0 <;> by_cases ho : R.order ≤ 2 <;>
      simp only [hk, ho, ↓reduceIte] at hfailure hcapAtP
    · linarith only [hfailure, hcapAtP]
    · exact hfailure.elim (not_lt_of_ge hcapAtP.1) (not_lt_of_ge hcapAtP.2)
    · linarith only [hfailure, hcapAtP]
    · exact hfailure.elim (not_lt_of_ge hcapAtP.1) (not_lt_of_ge hcapAtP.2)
  have htail2 : 2 * p ≤ tail := by
    have hsum : (I.card : ℝ) * p ≤ tail := by
      calc
        _ = ∑ _b ∈ I, p := by simp
        _ ≤ _ := Finset.sum_le_sum fun b hb => (Finset.mem_filter.mp hb).2
    have hcard : (2 : ℝ) ≤ I.card := by exact_mod_cast htwo
    exact (mul_le_mul_of_nonneg_right hcard hp.le).trans hsum
  refine ⟨htwo, ?_⟩
  change ((if k = 0 then R.outerThreshold else R.innerThreshold : ℚ) : ℝ) <
    tail + (((if R.order ≤ 2 then 2 else 5 / 2 : ℚ) : ℝ) - 1) * p
  by_cases hk : k = 0 <;> by_cases ho : R.order ≤ 2 <;>
    simp only [hk, ho, ↓reduceIte, Rat.cast_ofNat, Rat.cast_div] at hfailure hcapAtP ⊢
  · linarith only [hfailure]
  · have hmain := hfailure.resolve_right (not_lt_of_ge hcapAtP.2)
    have hmin := min_le_left ((3 / 2 : ℝ) * p) L
    linarith only [hmain, hmin]
  · linarith only [hfailure]
  · have hmain := hfailure.resolve_right (not_lt_of_ge hcapAtP.2)
    by_cases hsmall : (3 / 2 : ℝ) * p ≤ L
    · rw [min_eq_left hsmall] at hmain
      linarith only [hmain]
    · have hlarge : L < (3 / 2 : ℝ) * p := lt_of_not_ge hsmall
      dsimp only [L] at hlarge
      have hL := hL (lt_of_not_ge ho)
      nlinarith only [hlarge, htail2, _hC, hL]


theorem trialSourceRows_plateau_bound :
    ∀ R ∈ trialOldSourceRows ++ trialNewSourceRows,
      2 < R.order → 0 < R.innerThreshold ∧ 3 * R.innerThreshold ≤ 7 * R.plateau := by
  decide +kernel

#print axioms trialSource_balanced_failure_of_offender
#print axioms trialSourceRows_plateau_bound

end PrimeGap182
