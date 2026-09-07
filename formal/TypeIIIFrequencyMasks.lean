import TypeIIICurveFibers
import TypeIIICosetCompletion

/-!
# Positive weighted frequency masks

The lemmas here apply the proved coset estimate to actual residue restrictions. They retain
the dependence of the allowed second-coordinate residues on the first coordinate. This is
needed for the nonvertical part of an exceptional curve.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- The proved numerical majorant for one residue coset. -/
def intervalMassBound (s q N : ℕ) : ℝ :=
  2 * (N : ℝ) + (s : ℝ) / q * (1 + Real.log (s : ℝ))

theorem intervalMassBound_nonneg (s : ℕ) [NeZero s] (q N : ℕ) :
    0 ≤ intervalMassBound s q N := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s from NeZero.one_le)
  have hlog : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs
  unfold intervalMassBound
  positivity

theorem intervalFourier_total_l1 (s : ℕ) [NeZero s] (A : ℤ) (N : ℕ) :
    (∑ h : ZMod s, ‖intervalFourier s A N h‖) ≤ intervalMassBound s 1 N := by
  have hh := intervalFourier_coset_l1 s 1 0 A N (by omega) (one_dvd s) (by omega)
  have hset : frequencyCoset s 1 0 = Finset.univ := by
    ext h
    simp [frequencyCoset, Nat.mod_one]
  rw [hset] at hh
  simpa only [intervalMassBound, Nat.cast_one, div_one] using hh

/-- Frequencies whose reduction modulo a divisor belongs to the specified finite set. -/
def residueSet (s q : ℕ) [NeZero s] [NeZero q] (R : Finset (ZMod q)) :
    Finset (ZMod s) :=
  Finset.univ.filter (fun h => (h.val : ZMod q) ∈ R)

theorem mem_frequencyCoset_iff_residue_eq
    (s q : ℕ) [NeZero s] [NeZero q] (a : ZMod q) (h : ZMod s) :
    h ∈ frequencyCoset s q a.val ↔ (h.val : ZMod q) = a := by
  simp only [frequencyCoset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hh
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using hh
  · intro hh
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hh

/-- Exact partition into residue cosets, before taking any estimates. -/
theorem sum_residueSet_eq_sum_cosets
    (s q : ℕ) [NeZero s] [NeZero q] (R : Finset (ZMod q)) (f : ZMod s → ℝ) :
    (∑ h ∈ residueSet s q R, f h) =
      ∑ a ∈ R, ∑ h ∈ frequencyCoset s q a.val, f h := by
  classical
  simp only [residueSet, frequencyCoset, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  simp_rw [show ∀ a : ZMod q, (h.val % q = a.val) ↔ (h.val : ZMod q) = a from by
    intro a
    exact (by simpa only [frequencyCoset, Finset.mem_filter, Finset.mem_univ, true_and] using
      mem_frequencyCoset_iff_residue_eq s q a h)]
  simp

/-- Uniform weighted bound for any finite set of allowed residue classes. -/
theorem intervalFourier_residueSet_l1
    (s q : ℕ) [NeZero s] [NeZero q] (A : ℤ) (N : ℕ) (hqs : q ∣ s)
    (R : Finset (ZMod q)) :
    (∑ h ∈ residueSet s q R, ‖intervalFourier s A N h‖) ≤
      (R.card : ℝ) * intervalMassBound s q N := by
  rw [sum_residueSet_eq_sum_cosets]
  calc
    _ ≤ ∑ _a ∈ R, intervalMassBound s q N := by
      apply Finset.sum_le_sum
      intro a ha
      exact intervalFourier_coset_l1 s q a.val A N (NeZero.pos q) hqs (ZMod.val_lt a)
    _ = _ := by simp

/-- The allowed second-coordinate residue set may depend on the actual first frequency.
The proof uses a uniform cardinal bound and does not choose a measurable selector. -/
theorem dependent_residue_rectangle_mass
    (s qh qk : ℕ) [NeZero s] [NeZero qh] [NeZero qk]
    (Ah Ak : ℤ) (Nh Nk M : ℕ) (hqh : qh ∣ s) (hqk : qk ∣ s)
    (H : Finset (ZMod qh)) (K : ZMod s → Finset (ZMod qk))
    (hK : ∀ h : ZMod s, (K h).card ≤ M) :
    (∑ h ∈ residueSet s qh H, ∑ k ∈ residueSet s qk (K h),
      ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) ≤
      (H.card : ℝ) * (M : ℝ) * intervalMassBound s qh Nh * intervalMassBound s qk Nk := by
  have hBh := intervalMassBound_nonneg s qh Nh
  have hBk := intervalMassBound_nonneg s qk Nk
  calc
    _ = ∑ h ∈ residueSet s qh H, ‖intervalFourier s Ah Nh h‖ *
        (∑ k ∈ residueSet s qk (K h), ‖intervalFourier s Ak Nk k‖) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ h ∈ residueSet s qh H,
        ‖intervalFourier s Ah Nh h‖ * ((M : ℝ) * intervalMassBound s qk Nk) := by
      apply Finset.sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (intervalFourier_residueSet_l1 s qk Ak Nk hqk (K h)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hK h) hBk)
    _ = (∑ h ∈ residueSet s qh H, ‖intervalFourier s Ah Nh h‖) *
        ((M : ℝ) * intervalMassBound s qk Nk) := by rw [Finset.sum_mul]
    _ ≤ ((H.card : ℝ) * intervalMassBound s qh Nh) *
        ((M : ℝ) * intervalMassBound s qk Nk) :=
      mul_le_mul_of_nonneg_right (intervalFourier_residueSet_l1 s qh Ah Nh hqh H)
        (mul_nonneg (Nat.cast_nonneg M) hBk)
    _ = _ := by ring

/-- The positive Fourier mass on an actual set of frequency pairs. -/
def frequencyMass (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (E : Finset (ZMod s × ZMod s)) : ℝ :=
  ∑ z ∈ E, ‖intervalFourier s Ah Nh z.1‖ * ‖intervalFourier s Ak Nk z.2‖

theorem frequencyMass_eq_double
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (E : Finset (ZMod s × ZMod s)) :
    frequencyMass s Ah Ak Nh Nk E =
      ∑ h : ZMod s, ∑ k : ZMod s,
        if (h, k) ∈ E then
          ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ else 0 := by
  classical
  calc
    _ = ∑ z ∈ E, if z ∈ E then
        ‖intervalFourier s Ah Nh z.1‖ * ‖intervalFourier s Ak Nk z.2‖ else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [ite_eq_left hz]
    _ = ∑ z : ZMod s × ZMod s, if z ∈ E then
        ‖intervalFourier s Ah Nh z.1‖ * ‖intervalFourier s Ak Nk z.2‖ else 0 := by
      apply Finset.sum_subset (Finset.subset_univ E)
      intro z hz hzE
      rw [ite_eq_right hzE]
    _ = _ := by rw [Fintype.sum_prod_type]

/-- Finite exceptional sets cost at most their cardinality times the interval lengths. -/
theorem frequencyMass_le_card
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (E : Finset (ZMod s × ZMod s)) :
    frequencyMass s Ah Ak Nh Nk E ≤ (E.card : ℝ) * Nh * Nk := by
  calc
    _ ≤ ∑ _z ∈ E, (Nh : ℝ) * Nk := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (intervalFourier_norm_le_length s Ah Nh z.1)
        (intervalFourier_norm_le_length s Ak Nk z.2) (norm_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by simp [mul_assoc]

private theorem sum_pairs_eq_rows
    {F G : Type*} [Fintype F] [Fintype G]
    (E : Finset (F × G)) (f : F × G → ℝ) :
    (∑ z ∈ E, f z) =
      ∑ h : F, ∑ k ∈ Finset.univ.filter (fun k : G => (h, k) ∈ E), f (h, k) := by
  classical
  calc
    _ = ∑ z ∈ E, if z ∈ E then f z else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [ite_eq_left hz]
    _ = ∑ z : F × G, if z ∈ E then f z else 0 := by
      apply Finset.sum_subset (Finset.subset_univ E)
      intro z hz hzE
      rw [ite_eq_right hzE]
    _ = _ := by rw [Fintype.sum_prod_type]; simp only [Finset.sum_filter]

/-- A proved fiber bound controls a positive separable weight on the curve. The bad
vertical fibers are counted explicitly; the other fiber cardinalities are also explicit. -/
theorem boundedVerticalFibers_weighted_sum_le
    (s : ℕ) [NeZero s] (D : ℕ) (E : Finset (ZMod s × ZMod s))
    (hE : BoundedVerticalFibers s D E)
    (a b : ZMod s → ℝ) (Ca Cb : ℝ)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (ha : ∀ h, 0 ≤ a h) (hb : ∀ k, 0 ≤ b k)
    (haC : ∀ h, a h ≤ Ca) (hbC : ∀ k, b k ≤ Cb) :
    (∑ z ∈ E, a z.1 * b z.2) ≤
      (D : ℝ) * (Ca * ∑ k : ZMod s, b k) +
        (D : ℝ) * (Cb * ∑ h : ZMod s, a h) := by
  classical
  obtain ⟨V, hV, hfiber⟩ := hE
  let row (h : ZMod s) := Finset.univ.filter (fun k : ZMod s => (h, k) ∈ E)
  have htotalb : 0 ≤ ∑ k : ZMod s, b k := Finset.sum_nonneg (fun k _ => hb k)
  have hrow (h : ZMod s) : (∑ k ∈ row h, b k) ≤ ∑ k : ZMod s, b k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hb k)
  have hrowC (h : ZMod s) : (∑ k ∈ row h, b k) ≤ ((row h).card : ℝ) * Cb := by
    calc
      _ ≤ ∑ _k ∈ row h, Cb := Finset.sum_le_sum (fun k _ => hbC k)
      _ = _ := by simp
  have heach (h : ZMod s) :
      a h * (∑ k ∈ row h, b k) ≤
        (if h ∈ V then Ca * ∑ k : ZMod s, b k else 0) + a h * ((D : ℝ) * Cb) := by
    by_cases hh : h ∈ V
    · rw [ite_eq_left hh]
      exact (mul_le_mul (haC h) (hrow h)
        (Finset.sum_nonneg (fun k _ => hb k)) hCa).trans
          (le_add_of_nonneg_right (mul_nonneg (ha h) (mul_nonneg (Nat.cast_nonneg D) hCb)))
    · rw [ite_eq_right hh, zero_add]
      apply mul_le_mul_of_nonneg_left _ (ha h)
      exact (hrowC h).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber h hh) hCb)
  have heq : (∑ z ∈ E, a z.1 * b z.2) =
      ∑ h : ZMod s, a h * ∑ k ∈ row h, b k := by
    rw [sum_pairs_eq_rows]
    simp only [row, Finset.mul_sum]
    apply Finset.sum_congr (by ext h; simp)
    intro h hh
    apply Finset.sum_congr (by ext k; simp only [Finset.mem_filter])
    intro k hk
    rfl
  have hVR : (V.card : ℝ) ≤ D := by exact_mod_cast hV
  rw [heq]
  calc
    _ ≤ ∑ h : ZMod s,
        ((if h ∈ V then Ca * ∑ k : ZMod s, b k else 0) + a h * ((D : ℝ) * Cb)) :=
      Finset.sum_le_sum (fun h _ => heach h)
    _ = (V.card : ℝ) * (Ca * ∑ k : ZMod s, b k) +
        (∑ h : ZMod s, a h) * ((D : ℝ) * Cb) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp
    _ ≤ (D : ℝ) * (Ca * ∑ k : ZMod s, b k) +
        (∑ h : ZMod s, a h) * ((D : ℝ) * Cb) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hVR (mul_nonneg hCa htotalb)) le_rfl
    _ = _ := by ring

/-- The actual exceptional-curve Fourier mass, using the proven fiber theorem and the
actual total interval Fourier sums. -/
theorem frequencyMass_le_of_boundedVerticalFibers
    (s : ℕ) [NeZero s] (D : ℕ) (Ah Ak : ℤ) (Nh Nk : ℕ)
    (E : Finset (ZMod s × ZMod s)) (hE : BoundedVerticalFibers s D E) :
    frequencyMass s Ah Ak Nh Nk E ≤
      (D : ℝ) * ((Nh : ℝ) * intervalMassBound s 1 Nk) +
        (D : ℝ) * ((Nk : ℝ) * intervalMassBound s 1 Nh) := by
  have hh := boundedVerticalFibers_weighted_sum_le s D E hE
    (fun h => ‖intervalFourier s Ah Nh h‖) (fun k => ‖intervalFourier s Ak Nk k‖)
    Nh Nk (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (intervalFourier_norm_le_length s Ah Nh)
    (intervalFourier_norm_le_length s Ak Nk)
  apply hh.trans
  gcongr
  · exact intervalFourier_total_l1 s Ak Nk
  · exact intervalFourier_total_l1 s Ah Nh

#print axioms sum_residueSet_eq_sum_cosets
#print axioms intervalFourier_residueSet_l1
#print axioms dependent_residue_rectangle_mass
#print axioms frequencyMass_le_card
#print axioms boundedVerticalFibers_weighted_sum_le
#print axioms frequencyMass_le_of_boundedVerticalFibers

end

end PrimeGap182.TypeIII
