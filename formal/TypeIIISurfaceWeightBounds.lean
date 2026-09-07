import TypeIIIFrobeniusTraceBounds

/-!
# Explicit numerical consequences of the standard weight convention

For a complex of upper weight v, ordinary degree i has upper weight v+i.
At a rational point over F_p this bounds each Frobenius eigenvalue by
p^((v+i)/2). `SurfaceStalk.weightsLe` records precisely this convention
in degrees -2, -1, and 0. Supplying that predicate for an actual geometric
complex is the external Deligne weight theorem; all weakenings to the
displayed Type III powers are proved below.
-/

noncomputable section

namespace PrimeGap182.TypeIII.SurfaceStalk

def weightsLe (V : SurfaceStalk) (p : ℕ) (v : ℝ) : Prop :=
  V.eigenvaluesLe ((p : ℝ) ^ ((v - 2) / 2))
    ((p : ℝ) ^ ((v - 1) / 2)) ((p : ℝ) ^ (v / 2))

theorem weightsLe_mono (V : SurfaceStalk) (p : ℕ) (hp : 1 ≤ p)
    {v w : ℝ} (hvw : v ≤ w) (hV : V.weightsLe p v) : V.weightsLe p w := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (hV.1 i).trans (Real.rpow_le_rpow_of_exponent_le hpR (by linarith))
  · intro i
    exact (hV.2.1 i).trans (Real.rpow_le_rpow_of_exponent_le hpR (by linarith))
  · intro i
    exact (hV.2.2 i).trans (Real.rpow_le_rpow_of_exponent_le hpR (by linarith))

theorem rpow_nat_add_half (p n : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ ((n : ℝ) + 1 / 2) = (p : ℝ) ^ n * Real.sqrt p := by
  rw [Real.rpow_add (by exact_mod_cast hp), Real.rpow_natCast, Real.sqrt_eq_rpow]

theorem physical_eigenvaluesLe_of_weightsLe (V : SurfaceStalk) (p : ℕ)
    (hp : 0 < p) {v : ℝ} (hv : v ≤ 6) (hV : V.weightsLe p v) :
    V.eigenvaluesLe ((p : ℝ) ^ 2) ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3) := by
  have h := V.weightsLe_mono p hp hv hV
  change V.eigenvaluesLe ((p : ℝ) ^ (((6 : ℝ) - 2) / 2))
    ((p : ℝ) ^ (((6 : ℝ) - 1) / 2)) ((p : ℝ) ^ ((6 : ℝ) / 2)) at h
  norm_num only [show ((6 : ℝ) - 2) / 2 = (2 : ℕ) by norm_num,
    show ((6 : ℝ) - 1) / 2 = (2 : ℝ) + 1 / 2 by norm_num,
    show (6 : ℝ) / 2 = (3 : ℕ) by norm_num, Real.rpow_natCast] at h
  have hh : (p : ℝ) ^ ((5 : ℝ) / 2) = (p : ℝ) ^ 2 * Real.sqrt p := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] using
      rpow_nat_add_half p 2 hp
  rw [hh] at h
  simpa only [Real.rpow_ofNat] using h

theorem fourier_eigenvaluesLe_of_weightsLe (V : SurfaceStalk) (p : ℕ)
    (hp : 0 < p) {v : ℝ} (hv : v ≤ 8) (hV : V.weightsLe p v) :
    V.eigenvaluesLe ((p : ℝ) ^ 3) ((p : ℝ) ^ 3 * Real.sqrt p) ((p : ℝ) ^ 4) := by
  have h := V.weightsLe_mono p hp hv hV
  change V.eigenvaluesLe ((p : ℝ) ^ (((8 : ℝ) - 2) / 2))
    ((p : ℝ) ^ (((8 : ℝ) - 1) / 2)) ((p : ℝ) ^ ((8 : ℝ) / 2)) at h
  norm_num only [show ((8 : ℝ) - 2) / 2 = (3 : ℕ) by norm_num,
    show ((8 : ℝ) - 1) / 2 = (3 : ℝ) + 1 / 2 by norm_num,
    show (8 : ℝ) / 2 = (4 : ℕ) by norm_num, Real.rpow_natCast] at h
  have hh : (p : ℝ) ^ ((7 : ℝ) / 2) = (p : ℝ) ^ 3 * Real.sqrt p := by
    simpa only [Nat.cast_ofNat, show (3 : ℝ) + 1 / 2 = 7 / 2 by norm_num] using
      rpow_nat_add_half p 3 hp
  rw [hh] at h
  simpa only [Real.rpow_ofNat] using h

/-- Every one of the fifteen nonempty products has at most four weight-one
factors, hence intermediate-extension weight at most six. -/
theorem core_physical_eigenvaluesLe (V : SurfaceStalk) (p : ℕ) (hp : 0 < p)
    (S : Finset (Fin 4)) (hV : V.weightsLe p ((S.card : ℝ) + 2)) :
    V.eigenvaluesLe ((p : ℝ) ^ 2) ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3) := by
  have hS : S.card ≤ 4 := (Finset.card_le_univ S).trans_eq (Fintype.card_fin 4)
  apply V.physical_eigenvaluesLe_of_weightsLe p hp _ hV
  have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  linarith

/-- The unnormalized plane Fourier transform increases complex weight by
two, so the same products have transformed weight at most eight. -/
theorem core_fourier_eigenvaluesLe (V : SurfaceStalk) (p : ℕ) (hp : 0 < p)
    (S : Finset (Fin 4)) (hV : V.weightsLe p ((S.card : ℝ) + 4)) :
    V.eigenvaluesLe ((p : ℝ) ^ 3) ((p : ℝ) ^ 3 * Real.sqrt p) ((p : ℝ) ^ 4) := by
  have hS : S.card ≤ 4 := (Finset.card_le_univ S).trans_eq (Fintype.card_fin 4)
  apply V.fourier_eigenvaluesLe_of_weightsLe p hp _ hV
  have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  linarith

#print axioms weightsLe
#print axioms weightsLe_mono
#print axioms rpow_nat_add_half
#print axioms physical_eigenvaluesLe_of_weightsLe
#print axioms fourier_eigenvaluesLe_of_weightsLe
#print axioms core_physical_eigenvaluesLe
#print axioms core_fourier_eigenvaluesLe

end PrimeGap182.TypeIII.SurfaceStalk
