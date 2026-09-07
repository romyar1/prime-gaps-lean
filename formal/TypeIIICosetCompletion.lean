import PrimeGaps186

/-!
# Interval Fourier mass on an actual residue coset

This is the elementary coset estimate used in the squarefree exceptional-frequency
completion. The interval has arbitrary natural length, with no assumption that its length
is shorter than the modulus. No Kloosterman or exceptional-Fourier hypothesis is used.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- The unnormalized negative-phase Fourier sum of the integer interval `[A,A+N)`. -/
def intervalFourier (s : ℕ) [NeZero s] (A : ℤ) (N : ℕ) (h : ZMod s) : ℂ :=
  ∑ n ∈ Finset.range N,
    ZMod.stdAddChar (-(((A + n : ℤ) : ZMod s) * h))

/-- An actual frequency residue coset, represented inside `ZMod s`. -/
def frequencyCoset (s q a : ℕ) [NeZero s] : Finset (ZMod s) :=
  Finset.univ.filter (fun h => h.val % q = a)

theorem intervalFourier_eq_dft (s : ℕ) [NeZero s] (A : ℤ) (N : ℕ) (h : ZMod s) :
    intervalFourier s A N h =
      ZMod.dft (PrimeGap186.integerIntervalResidueWeight s A N (fun _ => 1)) h := by
  simpa only [intervalFourier, one_mul] using
    ((PrimeGap186.integerIntervalResidueWeight_spec s A N (fun _ => 1)).2.1 h).symm

theorem intervalFourier_norm_le_length
    (s : ℕ) [NeZero s] (A : ℤ) (N : ℕ) (h : ZMod s) :
    ‖intervalFourier s A N h‖ ≤ (N : ℝ) := by
  unfold intervalFourier
  calc
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro n hn
      simp only [ZMod.stdAddChar_apply, Circle.norm_coe, le_refl]
    _ = N := by simp

theorem intervalFourier_norm_le_geometric
    (s : ℕ) [NeZero s] (A : ℤ) (N : ℕ) (h : ZMod s) (hh : h ≠ 0) :
    ‖intervalFourier s A N h‖ ≤
      (s : ℝ) / (2 * ((min h.val (s - h.val) : ℕ) : ℝ)) := by
  rw [intervalFourier_eq_dft]
  exact ((PrimeGap186.integerIntervalResidueWeight_geometric_l1 s A N).2.2.1 h hh).2.trans
    (min_le_right _ _)

private theorem coset_index_lt (q L a j : ℕ) (ha : a < q) (hj : j < L) :
    a + q * j < q * L := by
  calc
    a + q * j < q + q * j := Nat.add_lt_add_right ha _
    _ = q * (j + 1) := by ring
    _ ≤ q * L := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hj)

/-- Exact enumeration of a frequency coset, with no assumption about a preferred
representative of the additive character. -/
theorem sum_frequencyCoset
    (s q a : ℕ) [NeZero s] (hq : 0 < q) (hqs : q ∣ s) (ha : a < q)
    (f : ZMod s → ℝ) :
    (∑ h ∈ frequencyCoset s q a, f h) =
      ∑ j ∈ Finset.range (s / q), f ((a + q * j : ℕ) : ZMod s) := by
  classical
  have hprod : q * (s / q) = s := Nat.mul_div_cancel' hqs
  have hval (j : ℕ) (hj : j ∈ Finset.range (s / q)) :
      (((a + q * j : ℕ) : ZMod s).val) = a + q * j := by
    rw [ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    exact (coset_index_lt q (s / q) a j ha (Finset.mem_range.mp hj)).trans_eq hprod
  symm
  apply Finset.sum_bij (fun j _ => ((a + q * j : ℕ) : ZMod s))
  · intro j hj
    simp only [frequencyCoset, Finset.mem_filter, Finset.mem_univ, true_and, hval j hj]
    simp [Nat.add_mod, Nat.mod_eq_of_lt ha]
  · intro i hi j hj heq
    have hv := congrArg ZMod.val heq
    rw [hval i hi, hval j hj] at hv
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel hv)
  · intro h hh
    have hmod : h.val % q = a := (Finset.mem_filter.mp hh).2
    refine ⟨h.val / q, Finset.mem_range.mpr ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hq).mpr
      simpa [Nat.mul_comm, hprod] using ZMod.val_lt h
    · have heq : a + q * (h.val / q) = h.val := by
        simpa only [hmod] using Nat.mod_add_div h.val q
      rw [heq, ZMod.natCast_zmod_val]
  · intro j hj
    rfl

private def endpointMajorant (N F : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then N else F / j

private theorem endpointMajorant_nonneg (N F : ℝ) (hN : 0 ≤ N) (hF : 0 ≤ F) (j : ℕ) :
    0 ≤ endpointMajorant N F j := by
  unfold endpointMajorant
  split_ifs <;> positivity

private theorem reciprocal_min_le (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (min x y)⁻¹ ≤ x⁻¹ + y⁻¹ := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hy.le)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (inv_nonneg.mpr hx.le)

private theorem coset_point_majorant
    (s q a : ℕ) [NeZero s] (A : ℤ) (N : ℕ)
    (hq : 0 < q) (hqs : q ∣ s) (ha : a < q)
    (j : ℕ) (hj : j < s / q) :
    ‖intervalFourier s A N ((a + q * j : ℕ) : ZMod s)‖ ≤
      endpointMajorant N ((s : ℝ) / (2 * q)) j +
        endpointMajorant N ((s : ℝ) / (2 * q)) (s / q - 1 - j) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hF : 0 ≤ (s : ℝ) / (2 * q) := by positivity
  by_cases hj0 : j = 0
  · rw [endpointMajorant, ite_eq_left hj0]
    exact (intervalFourier_norm_le_length s A N _).trans
      (le_add_of_nonneg_right (endpointMajorant_nonneg _ _ hN hF _))
  by_cases hk0 : s / q - 1 - j = 0
  · rw [endpointMajorant, ite_eq_right hj0, endpointMajorant, ite_eq_left hk0]
    exact (intervalFourier_norm_le_length s A N _).trans
      (le_add_of_nonneg_left (by positivity))
  let L := s / q
  let v := a + q * j
  let k := L - 1 - j
  have hprod : q * L = s := Nat.mul_div_cancel' hqs
  have hvlt : v < s := (coset_index_lt q L a j ha hj).trans_eq hprod
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hvpos : 0 < v := (Nat.mul_pos hq hjpos).trans_le (Nat.le_add_left _ _)
  have hvval : ((v : ZMod s).val) = v := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hvlt]
  have hξ : (v : ZMod s) ≠ 0 := by
    intro hz
    have hh := congrArg ZMod.val hz
    rw [hvval, ZMod.val_zero] at hh
    exact hvpos.ne' hh
  have hjk : j + k = L - 1 := by dsimp [k]; omega
  have hLpos : 0 < L := by omega
  have hkNat : q * k ≤ s - v := by
    apply Nat.le_sub_of_add_le
    calc
      q * k + v = a + q * (j + k) := by dsimp [v]; ring
      _ = a + q * (L - 1) := by rw [hjk]
      _ ≤ q + q * (L - 1) := Nat.add_le_add_right ha.le _
      _ = q * L := by
        rw [show q + q * (L - 1) = q * ((L - 1) + 1) by ring,
          Nat.sub_add_cancel hLpos]
      _ = s := hprod
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hvpos
  have hwR : 0 < ((s - v : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hvlt
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hjpos
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hvlo : (q : ℝ) * j ≤ (v : ℝ) := by
    exact_mod_cast (show q * j ≤ v from Nat.le_add_left _ _)
  have hwlo : (q : ℝ) * k ≤ ((s - v : ℕ) : ℝ) := by exact_mod_cast hkNat
  have hb := intervalFourier_norm_le_geometric s A N (v : ZMod s) hξ
  rw [hvval, Nat.cast_min] at hb
  rw [endpointMajorant, ite_eq_right hj0, endpointMajorant, ite_eq_right hk0]
  change ‖intervalFourier s A N (v : ZMod s)‖ ≤
    (s : ℝ) / (2 * q) / j + (s : ℝ) / (2 * q) / k
  calc
    _ ≤ (s : ℝ) / (2 * min (v : ℝ) ((s - v : ℕ) : ℝ)) := hb
    _ = (s : ℝ) / 2 * (min (v : ℝ) ((s - v : ℕ) : ℝ))⁻¹ := by ring
    _ ≤ (s : ℝ) / 2 * ((v : ℝ)⁻¹ + (((s - v : ℕ) : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left (reciprocal_min_le _ _ hvR hwR) (by positivity)
    _ ≤ (s : ℝ) / 2 * (((q : ℝ) * j)⁻¹ + ((q : ℝ) * k)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (inv_anti₀ (mul_pos hqR hjR) hvlo)
        (inv_anti₀ (mul_pos hqR hkR) hwlo)
    _ = (s : ℝ) / (2 * q) / j + (s : ℝ) / (2 * q) / k := by ring

private theorem sum_range_inv_le_log (L s : ℕ) (hLs : L ≤ s + 1) :
    (∑ j ∈ Finset.range L, (j : ℝ)⁻¹) ≤ 1 + Real.log (s : ℝ) := by
  have hsum : (∑ j ∈ Finset.range (s + 1), (j : ℝ)⁻¹) = (harmonic s : ℝ) := by
    have hset : Finset.range (s + 1) = insert 0 (Finset.Icc 1 s) := by
      ext j
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp [harmonic_eq_sum_Icc]
  calc
    _ ≤ ∑ j ∈ Finset.range (s + 1), (j : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hLs) (by intros; positivity)
    _ = (harmonic s : ℝ) := hsum
    _ ≤ 1 + Real.log (s : ℝ) := harmonic_le_one_add_log s

private theorem sum_endpointMajorant (N F : ℝ) (L : ℕ) (hL : 0 < L) :
    (∑ j ∈ Finset.range L, endpointMajorant N F j) =
      N + F * ∑ j ∈ Finset.range L, (j : ℝ)⁻¹ := by
  have heq (j : ℕ) : endpointMajorant N F j =
      (if j = 0 then N else 0) + F * (j : ℝ)⁻¹ := by
    by_cases hj : j = 0 <;> simp [endpointMajorant, hj, div_eq_mul_inv]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [hL]

/-- The actual frequency-coset `ℓ¹` estimate. This covers all interval lengths `N`, including
`N>s`, all residue classes, and modulus one. The explicit constant is sufficient for the
paper's `O(N+(s/q)log(2s))` statement. -/
theorem intervalFourier_coset_l1
    (s q a : ℕ) [NeZero s] (A : ℤ) (N : ℕ)
    (hq : 0 < q) (hqs : q ∣ s) (ha : a < q) :
    (∑ h ∈ frequencyCoset s q a, ‖intervalFourier s A N h‖) ≤
      2 * (N : ℝ) + (s : ℝ) / q * (1 + Real.log (s : ℝ)) := by
  have hL : 0 < s / q := Nat.div_pos (Nat.le_of_dvd (NeZero.pos s) hqs) hq
  have hF : 0 ≤ (s : ℝ) / (2 * q) := by positivity
  rw [sum_frequencyCoset s q a hq hqs ha]
  calc
    _ ≤ ∑ j ∈ Finset.range (s / q),
        (endpointMajorant N ((s : ℝ) / (2 * q)) j +
          endpointMajorant N ((s : ℝ) / (2 * q)) (s / q - 1 - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact coset_point_majorant s q a A N hq hqs ha j (Finset.mem_range.mp hj)
    _ = 2 * ((N : ℝ) + (s : ℝ) / (2 * q) *
        ∑ j ∈ Finset.range (s / q), (j : ℝ)⁻¹) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_reflect,
        sum_endpointMajorant _ _ _ hL]
      ring
    _ ≤ 2 * ((N : ℝ) + (s : ℝ) / (2 * q) * (1 + Real.log (s : ℝ))) := by
      gcongr
      exact sum_range_inv_le_log (s / q) s ((Nat.div_le_self _ _).trans (Nat.le_succ s))
    _ = 2 * (N : ℝ) + (s : ℝ) / q * (1 + Real.log (s : ℝ)) := by ring

#print axioms intervalFourier_eq_dft
#print axioms sum_frequencyCoset
#print axioms intervalFourier_coset_l1

end

end PrimeGap182.TypeIII
