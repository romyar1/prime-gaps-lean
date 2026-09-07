import IncidenceRankFour

/-!
# Exact entries of the actual twisted prime incidence Gram matrices

The complete sums, pole masks, change of variables, and diagonal cases are
proved here. No Deligne bound or matrix-mode bound is needed for these identities.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {p : ℕ} [Fact p.Prime]

def incidenceSquareMode (A ν : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  fun b b' => ∑ u : (ZMod p)ˣ,
    ZMod.stdAddChar (-A * (b' - b) / (u : ZMod p) ^ 2 + ν * (u : ZMod p))

private theorem incidence_mode_char_star (t : ZMod p) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  have hp : 0 < ringChar (ZMod p) := by
    simpa only [ringChar.eq (ZMod p) p] using (Fact.out : p.Prime).pos
  exact AddChar.starComp_apply hp t

private theorem incidence_sum_omit_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (a : ι) :
    (∑ x, if x = a then 0 else f x) = (∑ x, f x) - f a := by
  calc
    _ = ∑ x, (f x - if x = a then f a else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a <;> simp [hx]
    _ = _ := by simp [Finset.sum_sub_distrib]

private theorem incidence_offDiagonal_unit_sum (f : ZMod p → ZMod p → ℂ) :
    (∑ u : ZMod p, ∑ v : ZMod p,
      if u = 0 ∨ v = 0 ∨ u = v then 0 else f u v) =
      (∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, f u v) -
        ∑ u : (ZMod p)ˣ, f u u := by
  have hbridge : (∑ u : ZMod p, ∑ v : ZMod p,
      if u = 0 ∨ v = 0 ∨ u = v then 0 else f u v) =
      ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
        if (u : ZMod p) = (v : ZMod p) then 0 else f u v := by
    rw [PrimeGap186.sum_units_eq_sum_ite p (fun u : ZMod p =>
      ∑ v : (ZMod p)ˣ, if u = (v : ZMod p) then 0 else f u v)]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u = 0
    · simp [hu]
    rw [ite_eq_left hu, PrimeGap186.sum_units_eq_sum_ite p (fun v : ZMod p =>
      if u = v then 0 else f u v)]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v = 0 <;> simp [hu, hv]
  rw [hbridge]
  have hinner (u : (ZMod p)ˣ) :
      (∑ v : (ZMod p)ˣ, if (u : ZMod p) = (v : ZMod p) then 0 else f u v) =
        (∑ v : (ZMod p)ˣ, f u v) - f u u := by
    simpa only [Units.val_inj, eq_comm] using
      incidence_sum_omit_one (fun v : (ZMod p)ˣ => f (u : ZMod p) (v : ZMod p)) u
  simp_rw [hinner]
  rw [Finset.sum_sub_distrib]

private def incidencePairPhase (A h ν b b' u v : ZMod p) : ℂ :=
  ZMod.stdAddChar ((-A * (b' - b)) / (u * v) +
    ((ν * b' - h) / (b' - b)) * u + ((h - ν * b) / (b' - b)) * v)

private def incidencePairKernel (A h ν b b' : ZMod p) (z : ZMod p × ZMod p) : ℂ :=
  if z.1 = 0 ∨ z.2 = 0 ∨ z.1 = z.2 then 0
  else incidencePairPhase A h ν b b' z.1 z.2

private theorem incidence_mode_pair_summand (A h ν b b' : ZMod p) (hbb : b ≠ b')
    (z : ZMod p × ZMod p) :
    incidenceJointChar (h, ν) z * star (primeIncidenceMatrix A z b) *
        primeIncidenceMatrix A z b' =
      incidencePairKernel A h ν b b' (incidencePairEquiv b b' hbb z) := by
  rcases z with ⟨e, γ⟩
  have hd : b' - b ≠ 0 := sub_ne_zero.mpr hbb.symm
  by_cases he : e = 0
  · simp [primeIncidenceMatrix, incidenceReciprocal, incidencePairEquiv,
      incidencePairKernel, he]
  by_cases hu : γ + e * b = 0
  · simp [primeIncidenceMatrix, incidenceReciprocal, incidencePairEquiv,
      incidencePairKernel, hu]
  by_cases hv : γ + e * b' = 0
  · simp [primeIncidenceMatrix, incidenceReciprocal, incidencePairEquiv,
      incidencePairKernel, hv]
  have huv : γ + e * b ≠ γ + e * b' := by
    intro h'
    exact hbb ((mul_left_cancel₀ he) (add_left_cancel h'))
  simp only [primeIncidenceMatrix, incidenceReciprocal,
    ite_eq_right (mul_ne_zero he hu), ite_eq_right (mul_ne_zero he hv),
    incidencePairEquiv, Equiv.coe_fn_mk, incidencePairKernel, hu, hv, huv,
    false_or, ↓reduceIte, incidence_mode_char_star, incidenceJointChar,
    incidencePairPhase]
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  field_simp
  ring

theorem primeIncidenceMode_offDiagonal_raw (A h ν b b' : ZMod p) (hbb : b ≠ b') :
    primeIncidenceMode A (h, ν) b b' =
      PrimeGap186.reciprocalProductCompleteSum p
        ((ν * b' - h) / (b' - b)) ((h - ν * b) / (b' - b)) (-A * (b' - b)) -
      incidenceSquareMode A ν b b' := by
  rw [primeIncidenceMode, incidenceMode, incidenceWeightedGram_apply]
  calc
    _ = ∑ z, incidencePairKernel A h ν b b' z :=
      Fintype.sum_equiv (incidencePairEquiv b b' hbb) _ _
        (incidence_mode_pair_summand A h ν b b' hbb)
    _ = (∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, incidencePairPhase A h ν b b' u v) -
        ∑ u : (ZMod p)ˣ, incidencePairPhase A h ν b b' u u := by
      rw [Fintype.sum_prod_type]
      exact incidence_offDiagonal_unit_sum _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      have hd : b' - b ≠ 0 := sub_ne_zero.mpr hbb.symm
      dsimp [incidencePairPhase, incidenceSquareMode]
      congr 1
      field_simp
      ring

private theorem incidence_complete_classification (a b c : ZMod p) (hc : c ≠ 0) :
    PrimeGap186.reciprocalProductCompleteSum p a b c =
      (p : ℂ) * PrimeGap186.normalizedKloosterman3 p (c * a * b) -
        if a = 0 ∧ b = 0 then (p : ℂ) else 0 := by
  rw [PrimeGap186.reciprocalProductCompleteSum_classification]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [hc, ha, hb, PrimeGap186.normalizedKloosterman3_zero]

/-- The exact off-diagonal identity, including all zero additive coefficients. -/
theorem primeIncidenceMode_offDiagonal (A h ν b b' : ZMod p)
    (hA : A ≠ 0) (hbb : b ≠ b') :
    primeIncidenceMode A (h, ν) b b' =
      (p : ℂ) * PrimeGap186.normalizedKloosterman3 p
        (A * (h - ν * b) * (h - ν * b') / (b' - b)) -
      incidenceSquareMode A ν b b' -
        if h = 0 ∧ ν = 0 then (p : ℂ) else 0 := by
  have hd : b' - b ≠ 0 := sub_ne_zero.mpr hbb.symm
  rw [primeIncidenceMode_offDiagonal_raw A h ν b b' hbb,
    incidence_complete_classification _ _ _ (mul_ne_zero (neg_ne_zero.mpr hA) hd)]
  have harg : (-A * (b' - b)) * ((ν * b' - h) / (b' - b)) *
      ((h - ν * b) / (b' - b)) =
      A * (h - ν * b) * (h - ν * b') / (b' - b) := by
    field_simp
    ring
  have hz : ((ν * b' - h) / (b' - b) = 0 ∧
      (h - ν * b) / (b' - b) = 0) ↔ h = 0 ∧ ν = 0 := by
    simp only [div_eq_zero_iff, hd, or_false]
    constructor
    · rintro ⟨h₁, h₂⟩
      have hνd : ν * (b' - b) = 0 := by linear_combination h₁ + h₂
      have hν : ν = 0 := (mul_eq_zero.mp hνd).resolve_right hd
      simpa [hν] using And.intro h₂ hν
    · rintro ⟨rfl, rfl⟩
      simp
  simp only [harg, hz]
  ring

private theorem incidence_reciprocal_star_self (A x : ZMod p) :
    star (incidenceReciprocal A x) * incidenceReciprocal A x =
      if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · simp [incidenceReciprocal, hx]
  simp only [incidenceReciprocal, ite_eq_right hx, incidence_mode_char_star]
  rw [← AddChar.map_add_eq_mul]
  simp

/-- Factored diagonal formula; it includes both zero and nonzero frequency cases. -/
theorem primeIncidenceMode_diagonal (A h ν b : ZMod p) :
    primeIncidenceMode A (h, ν) b b =
      (if h - ν * b = 0 then (p : ℂ) - 1 else -1) *
        (if ν = 0 then (p : ℂ) - 1 else -1) := by
  rw [primeIncidenceMode, incidenceMode, incidenceWeightedGram_apply]
  simp only [primeIncidenceMatrix, mul_assoc, incidence_reciprocal_star_self,
    Fintype.sum_prod_type, incidenceJointChar]
  have hrow (e : ZMod p) :
      (∑ γ : ZMod p, ZMod.stdAddChar (h * e + ν * γ) *
        (if e * (γ + e * b) = 0 then 0 else 1)) =
        if e = 0 then 0 else
          ZMod.stdAddChar ((h - ν * b) * e) *
            ∑ u : (ZMod p)ˣ, ZMod.stdAddChar (ν * (u : ZMod p)) := by
    by_cases he : e = 0
    · simp [he]
    rw [ite_eq_right he, PrimeGap186.sum_units_eq_sum_ite p
      (fun u : ZMod p => ZMod.stdAddChar (ν * u)), Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (e * b)) _ _ ?_
    intro γ
    change ZMod.stdAddChar (h * e + ν * γ) *
      (if e * (γ + e * b) = 0 then 0 else 1) =
      ZMod.stdAddChar ((h - ν * b) * e) *
        (if γ + e * b ≠ 0 then ZMod.stdAddChar (ν * (γ + e * b)) else 0)
    by_cases hu : γ + e * b = 0
    · simp [hu]
    rw [ite_eq_right (mul_ne_zero he hu), ite_eq_left hu, mul_one]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hrow]
  have hunit : (∑ e : ZMod p, if e = 0 then 0 else
      ZMod.stdAddChar ((h - ν * b) * e) *
        ∑ u : (ZMod p)ˣ, ZMod.stdAddChar (ν * (u : ZMod p))) =
      ∑ e : (ZMod p)ˣ, ZMod.stdAddChar ((h - ν * b) * (e : ZMod p)) *
        ∑ u : (ZMod p)ˣ, ZMod.stdAddChar (ν * (u : ZMod p)) := by
    rw [PrimeGap186.sum_units_eq_sum_ite p (fun e : ZMod p =>
      ZMod.stdAddChar ((h - ν * b) * e) *
        ∑ u : (ZMod p)ˣ, ZMod.stdAddChar (ν * (u : ZMod p)))]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e = 0 <;> simp [he]
  rw [hunit]
  rw [← Finset.sum_mul, PrimeGap186.stdAddChar_sum_units,
    PrimeGap186.stdAddChar_sum_units]

theorem incidenceSquareMode_diagonal (A ν b : ZMod p) :
    incidenceSquareMode A ν b b = if ν = 0 then (p : ℂ) - 1 else -1 := by
  simp only [incidenceSquareMode, sub_self, mul_zero, zero_div, zero_add]
  exact PrimeGap186.stdAddChar_sum_units p ν

#print axioms primeIncidenceMode_offDiagonal_raw
#print axioms primeIncidenceMode_offDiagonal
#print axioms primeIncidenceMode_diagonal
#print axioms incidenceSquareMode_diagonal

end PrimeGap182Audit
