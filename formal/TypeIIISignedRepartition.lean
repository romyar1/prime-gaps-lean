import TypeIIIResidualNonzero

/-!
# The signed selected-factor correlation and its exact gcd coordinates

The coefficient and physical-frequency sums are identified before applying a norm.
The auxiliary coprimality and original finite coefficient support remain literal masks.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- A selected row, extended by zero to the positive coefficient interval. -/
def selectedRowCoefficient (b d : ℕ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N : ℕ) (m : IntegerIntervalIndex 1 N) : ℂ :=
  if m.1 ∈ M ∧ Int.gcd m.1 ((b * d : ℕ) : ℤ) = 1 then
    η (b * d) * α m.1
  else 0

theorem selectedRowCoefficient_norm_le (b d : ℕ) (M : Finset ℤ)
    (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ) (E L : ℝ)
    (hE : ‖η (b * d)‖ ≤ E) (hL : 0 ≤ L)
    (hα : ∀ m ∈ M, ‖α m‖ ≤ L) (m : IntegerIntervalIndex 1 N) :
    ‖selectedRowCoefficient b d M η α N m‖ ≤ E * L := by
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  unfold selectedRowCoefficient
  split_ifs with h
  · rw [norm_mul]
    exact mul_le_mul hE (hα m.1 h.1) (norm_nonneg _) hE0
  · exact (norm_zero : ‖(0 : ℂ)‖ = 0).le.trans (mul_nonneg hE0 hL)

private theorem unit_of_selected_gcd (b d : ℕ) (m : ℤ)
    (hm : Int.gcd m ((b * d : ℕ) : ℤ) = 1) : IsUnit (m : ZMod d) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime m d).mpr
  have hc := Int.isCoprime_iff_gcd_eq_one.mpr hm
  exact (hc.of_isCoprime_of_dvd_right (by
    exact_mod_cast (dvd_mul_left d b : d ∣ b * d))).symm

/-- The complete signed pair in the public selected-factor expansion. -/
def selectedSignedCorrelation (b d₁ d₂ q : ℕ) [NeZero d₁] [NeZero d₂]
    (a : ℤ) (M : Finset ℤ)
    (η : ℕ → ℂ) (α : ℤ → ℂ) (T H : ℝ) (ψ : ℝ → ℝ) : ℂ :=
  ∑ m ∈ M, ∑ n ∈ M,
    if Int.gcd m ((b * d₁ : ℕ) : ℤ) = 1 ∧
        Int.gcd n ((b * d₂ : ℕ) : ℤ) = 1 then
      (η (b * d₁) * star (η (b * d₂))) * (α m * star (α n)) *
        ∑ ℓ ∈ Finset.Icc ⌈-T * H⌉ ⌊T * H⌋,
          if IsUnit (ℓ : ZMod q) then
            (ψ ((ℓ : ℝ) / H) : ℂ) *
              PrimeGap186.normalizedKloosterman3Mod d₁
                (((a : ZMod d₁) * (m : ZMod d₁)⁻¹) * (ℓ : ZMod d₁)) *
              star (PrimeGap186.normalizedKloosterman3Mod d₂
                (((a : ZMod d₂) * (n : ZMod d₂)⁻¹) * (ℓ : ZMod d₂)))
          else 0
    else 0

theorem selectedSignedCorrelation_moduli_congr (b d₁ d₂ q e₁ e₂ r : ℕ)
    [NeZero d₁] [NeZero d₂] [NeZero e₁] [NeZero e₂]
    (h₁ : d₁ = e₁) (h₂ : d₂ = e₂) (hq : q = r)
    (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (T H : ℝ) (ψ : ℝ → ℝ) :
    selectedSignedCorrelation b d₁ d₂ q a M η α T H ψ =
      selectedSignedCorrelation b e₁ e₂ r a M η α T H ψ := by
  subst e₁ e₂ r
  rfl

private theorem sum_mask_subset {E : Type*} [AddCommMonoid E]
    (M I : Finset ℤ) (hM : M ⊆ I) (f : ℤ → E) :
    (∑ m ∈ I, if m ∈ M then f m else 0) = ∑ m ∈ M, f m := by
  calc
    _ = ∑ m ∈ M, if m ∈ M then f m else 0 :=
      (Finset.sum_subset hM (fun m _ hm => ite_eq_right hm)).symm
    _ = _ := Finset.sum_congr rfl (fun m hm => ite_eq_left hm)

theorem sharedOriginalFunction_selectedRows
    (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (b : ℕ) (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N : ℕ) (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (ℓ : ZMod (u * (v * w))) :
    sharedOriginalFunction u v w a 1 1 N N
      (selectedRowCoefficient b (u * w) M η α N)
      (selectedRowCoefficient b (v * w) M η α N) ℓ =
      ∑ m ∈ M, ∑ n ∈ M,
        if Int.gcd m ((b * (u * w) : ℕ) : ℤ) = 1 ∧
            Int.gcd n ((b * (v * w) : ℕ) : ℤ) = 1 then
          (η (b * (u * w)) * star (η (b * (v * w)))) *
            (α m * star (α n)) * sharedInverseFunction u v w a m n ℓ
        else 0 := by
  let f (m n : ℤ) : ℂ :=
    if Int.gcd m ((b * (u * w) : ℕ) : ℤ) = 1 ∧
        Int.gcd n ((b * (v * w) : ℕ) : ℤ) = 1 then
      (η (b * (u * w)) * star (η (b * (v * w)))) *
        (α m * star (α n)) * sharedInverseFunction u v w a m n ℓ
    else 0
  have hpoint (m n : IntegerIntervalIndex 1 N) :
      (if IsUnit (m.1 : ZMod (u * w)) ∧ IsUnit (n.1 : ZMod (v * w)) then
        selectedRowCoefficient b (u * w) M η α N m *
          sharedInverseFunction u v w a m.1 n.1 ℓ *
          star (selectedRowCoefficient b (v * w) M η α N n)
       else 0) = if m.1 ∈ M then if n.1 ∈ M then f m.1 n.1 else 0 else 0 := by
    by_cases hm : m.1 ∈ M
    · by_cases hn : n.1 ∈ M
      · by_cases hmg : Int.gcd m.1 ((b * (u * w) : ℕ) : ℤ) = 1
        · by_cases hng : Int.gcd n.1 ((b * (v * w) : ℕ) : ℤ) = 1
          · have hmu := unit_of_selected_gcd b (u * w) m.1 hmg
            have hnu := unit_of_selected_gcd b (v * w) n.1 hng
            simp only [selectedRowCoefficient, f, hm, hn, hmg, hng, hmu, hnu,
              and_self, ite_true, star_mul]
            ring
          · simp only [selectedRowCoefficient, f, hm, hn, hmg, hng,
              and_true, and_false, ite_true, ite_false, star_zero, mul_zero, ite_self]
        · simp only [selectedRowCoefficient, f, hm, hn, hmg,
            true_and, false_and, ite_false, zero_mul, ite_self]
      · simp only [selectedRowCoefficient, hn, hm, false_and, ite_false,
          star_zero, mul_zero, ite_self]
    · simp only [selectedRowCoefficient, hm, false_and, ite_false, zero_mul, ite_self]
  unfold sharedOriginalFunction
  simp_rw [hpoint]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_integerIntervalIndex 1 N
    (fun m => if m ∈ M then
      ∑ n : IntegerIntervalIndex 1 N, if n.1 ∈ M then f m n.1 else 0
      else 0)]
  rw [sum_mask_subset M _ hM]
  apply Finset.sum_congr rfl
  intro m _
  rw [sum_integerIntervalIndex 1 N (fun n => if n ∈ M then f m n else 0)]
  exact sum_mask_subset M _ hM (f m)

/-- Exact finite physical completion of each selected pair. No norm or triangle
inequality has been used at this stage. -/
theorem sharedProfileCoefficientSum_selectedRows
    (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (b : ℕ) (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N : ℕ) (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (T H : ℝ) (ψ : ℝ → ℝ) :
    sharedProfileCoefficientSum u v w a 1 1 N N
      (selectedRowCoefficient b (u * w) M η α N)
      (selectedRowCoefficient b (v * w) M η α N)
      T H 0 (fun t => (ψ t : ℂ)) =
      selectedSignedCorrelation b (u * w) (v * w) (u * (v * w))
        a M η α T H ψ := by
  unfold sharedProfileCoefficientSum selectedSignedCorrelation
  simp only [zero_sub, zero_add, sub_zero, neg_mul]
  simp_rw [sharedOriginalFunction_selectedRows u v w b a M η α N hM,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : Int.gcd m ((b * (u * w) : ℕ) : ℤ) = 1 ∧
      Int.gcd n ((b * (v * w) : ℕ) : ℤ) = 1
  · simp only [h, and_self, ite_true]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [sharedInverseFunction_int]
    by_cases hℓ : IsUnit (ℓ : ZMod (u * (v * w)))
    · simp only [hℓ, ite_true]
      ring
    · simp only [hℓ, ite_false, mul_zero]
  · simp only [h, ite_false, mul_zero, Finset.sum_const_zero]

/-- Positive gcd coordinates, usable as moduli without any auxiliary hypotheses. -/
def selectedGcd (r₁ r₂ : ℕ+) : ℕ+ :=
  ⟨Nat.gcd (r₁ : ℕ) (r₂ : ℕ), Nat.gcd_pos_of_pos_left _ r₁.pos⟩

def selectedLeft (r₁ r₂ : ℕ+) : ℕ+ :=
  ⟨(r₁ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ), Nat.div_gcd_pos_of_pos_left _ r₁.pos⟩

def selectedRight (r₁ r₂ : ℕ+) : ℕ+ :=
  ⟨(r₂ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ), Nat.div_gcd_pos_of_pos_right _ r₂.pos⟩

theorem selected_gcd_coordinates (s r₁ r₂ : ℕ+) :
    let g := (selectedGcd r₁ r₂ : ℕ)
    let u := (selectedLeft r₁ r₂ : ℕ)
    let v := (selectedRight r₁ r₂ : ℕ)
    (r₁ : ℕ) = g * u ∧ (r₂ : ℕ) = g * v ∧
      u * ((s : ℕ) * g) = (r₁ : ℕ) * s ∧
      v * ((s : ℕ) * g) = (r₂ : ℕ) * s ∧
      u * (v * ((s : ℕ) * g)) = (s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ) := by
  dsimp only [selectedGcd, selectedLeft, selectedRight]
  simp only [PNat.mk_coe]
  have hh := PrimeGap186.gcd_repartition_arithmetic (s : ℕ) (r₁ : ℕ) (r₂ : ℕ)
  dsimp only at hh
  have hc : Nat.Coprime ((r₁ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ))
      ((r₂ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ)) :=
    Nat.gcd_div_gcd_div_gcd_of_pos_left r₁.pos
  refine ⟨by simpa only [mul_comm] using hh.1,
    by simpa only [mul_comm] using hh.2.1, ?_, ?_, ?_⟩
  · calc
      _ = ((r₁ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ) *
        Nat.gcd (r₁ : ℕ) (r₂ : ℕ)) * s := by ring
      _ = _ := by rw [← hh.1]
  · calc
      _ = ((r₂ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ) *
        Nat.gcd (r₁ : ℕ) (r₂ : ℕ)) * s := by ring
      _ = _ := by rw [← hh.2.1]
  · rw [hh.2.2, hc.lcm_eq_mul]
    ring

theorem selected_unit_of_dvd (q d : ℕ) (h : d ∣ q) (a : ℤ)
    (ha : IsUnit (a : ZMod q)) : IsUnit (a : ZMod d) := by
  simpa only [map_intCast] using ha.map (ZMod.castHom h (ZMod d))

/-- Every supported selected pair meets all arithmetic guards in the completed
residual estimates, including primitivity of the shared modulus. -/
theorem selected_gcd_admissible (s r₁ r₂ : ℕ+) (a : ℤ)
    (hs : Squarefree (s : ℕ)) (h₁ : Squarefree (r₁ : ℕ))
    (h₂ : Squarefree (r₂ : ℕ))
    (hcop : Nat.Coprime (s : ℕ) ((r₁ : ℕ) * (r₂ : ℕ)))
    (ha : IsUnit (a : ZMod ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ)))) :
    let w := (s : ℕ) * (selectedGcd r₁ r₂ : ℕ)
    Squarefree w ∧ IsUnit (a : ZMod w) ∧
      SharedOuterAdmissible w a (selectedLeft r₁ r₂ : ℕ) (selectedRight r₁ r₂ : ℕ) := by
  have hh := PrimeGap186.squarefree_gcd_repartition (s : ℕ) (r₁ : ℕ) (r₂ : ℕ)
    hs h₁ h₂ hcop
  change Squarefree ((s : ℕ) * (selectedGcd r₁ r₂ : ℕ)) ∧
    Squarefree (selectedLeft r₁ r₂ : ℕ) ∧ Squarefree (selectedRight r₁ r₂ : ℕ) ∧
    Nat.Coprime (selectedLeft r₁ r₂ : ℕ) (selectedRight r₁ r₂ : ℕ) ∧
    Nat.Coprime ((s : ℕ) * (selectedGcd r₁ r₂ : ℕ))
      ((selectedLeft r₁ r₂ : ℕ) * (selectedRight r₁ r₂ : ℕ)) at hh
  have hq := (selected_gcd_coordinates s r₁ r₂).2.2.2.2
  have ha' : IsUnit (a : ZMod ((selectedLeft r₁ r₂ : ℕ) *
      ((selectedRight r₁ r₂ : ℕ) * ((s : ℕ) * (selectedGcd r₁ r₂ : ℕ))))) :=
    (congrArg (fun q => IsUnit (a : ZMod q)) hq).mpr ha
  have hparts := Nat.coprime_mul_iff_right.mp hh.2.2.2.2
  refine ⟨hh.1, selected_unit_of_dvd _ _
    (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) a ha',
    hh.2.2.2.1, hparts.1.symm, hparts.2.symm, hh.2.1, hh.2.2.1,
    selected_unit_of_dvd _ _ (dvd_mul_right _ _) a ha',
    selected_unit_of_dvd _ _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) a ha'⟩

/-- One entire signed coefficient/frequency block in its positive gcd coordinates. -/
def selectedGcdProfile (b : ℕ) (s r₁ r₂ : ℕ+) (a : ℤ) (M : Finset ℤ)
    (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ) (T H : ℝ) (ψ : ℝ → ℝ) : ℂ :=
  let u := selectedLeft r₁ r₂
  let v := selectedRight r₁ r₂
  let w := s * selectedGcd r₁ r₂
  sharedProfileCoefficientSum (u : ℕ) (v : ℕ) (w : ℕ) a 1 1 N N
    (selectedRowCoefficient b ((u : ℕ) * (w : ℕ)) M η α N)
    (selectedRowCoefficient b ((v : ℕ) * (w : ℕ)) M η α N)
    T H 0 (fun t => (ψ t : ℂ))

theorem selectedGcdProfile_eq_correlation (b : ℕ) (s r₁ r₂ : ℕ+)
    (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N : ℕ) (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (T H : ℝ) (ψ : ℝ → ℝ) :
    selectedGcdProfile b s r₁ r₂ a M η α N T H ψ =
      selectedSignedCorrelation b ((r₁ : ℕ) * (s : ℕ)) ((r₂ : ℕ) * (s : ℕ))
        ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ)) a M η α T H ψ := by
  unfold selectedGcdProfile
  rw [sharedProfileCoefficientSum_selectedRows _ _ _ b a M η α N hM]
  have hc := selected_gcd_coordinates s r₁ r₂
  apply selectedSignedCorrelation_moduli_congr
  · simpa only [PNat.mul_coe] using hc.2.2.1
  · simpa only [PNat.mul_coe] using hc.2.2.2.1
  · simpa only [PNat.mul_coe] using hc.2.2.2.2

#print axioms selectedRowCoefficient_norm_le
#print axioms sharedOriginalFunction_selectedRows
#print axioms sharedProfileCoefficientSum_selectedRows
#print axioms selected_gcd_admissible
#print axioms selectedGcdProfile_eq_correlation

end

end PrimeGap182.TypeIII
