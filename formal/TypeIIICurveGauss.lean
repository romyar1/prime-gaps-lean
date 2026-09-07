import TypeIIICurveTangents
import TypeIIICurveDirection

/-! Pointwise constant tangent directions force an actual affine line.

The pointwise-to-polynomial step uses the Nullstellensatz and a proved strict
degree drop for partial derivatives. No geometric Gauss map or sheaf is assumed
to have this property by this module.
-/

noncomputable section
open scoped Classical
open MvPolynomial

namespace PrimeGap182.TypeIII.CurvePolynomial

variable {k σ : Type*} [Field k]

theorem totalDegree_pos_of_irreducible {f : MvPolynomial σ k} (hf : Irreducible f) :
    0 < f.totalDegree := by
  by_contra hn
  have hd0 : f.totalDegree = 0 := by omega
  have he := totalDegree_eq_zero_iff_eq_C.mp hd0
  have hc : coeff 0 f ≠ 0 := by
    intro hc
    exact hf.ne_zero (by rw [he, hc, map_zero])
  exact hf.not_isUnit (by rw [he]; exact (isUnit_iff_ne_zero.mpr hc).map C)

theorem totalDegree_affine_le_one (a b c : k) :
    (C a * X 0 + C b * X 1 + C c : MvPolynomial (Fin 2) k).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simpa only [totalDegree_C, totalDegree_X, zero_add] using
        totalDegree_mul (C a) (X (0 : Fin 2))
    · simpa only [totalDegree_C, totalDegree_X, zero_add] using
        totalDegree_mul (C b) (X (1 : Fin 2))
  · simp only [totalDegree_C, Nat.zero_le]

theorem totalDegree_pderiv_le_tsub_one (f : MvPolynomial σ k) (i : σ) :
    (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  apply Finset.sup_le
  intro m hm
  have hcoeff : coeff (m + Finsupp.single i 1) f ≠ 0 := by
    exact (mul_ne_zero_iff.mp (by simpa only [mem_support_iff, coeff_pderiv] using hm)).1
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  change (m + Finsupp.single i 1).degree ≤ f.totalDegree at hd
  simp only [map_add, Finsupp.degree_single] at hd
  change m.degree ≤ f.totalDegree - 1
  omega

theorem totalDegree_direction_le_tsub_one (f : MvPolynomial (Fin 2) k) (a b : k) :
    (C a * pderiv 0 f + C b * pderiv 1 f).totalDegree ≤ f.totalDegree - 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using totalDegree_pderiv_le_tsub_one f 0)
  · exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using totalDegree_pderiv_le_tsub_one f 1)

theorem direction_zero_of_dvd {f : MvPolynomial (Fin 2) k}
    (hd : 0 < f.totalDegree) (a b : k)
    (hdiv : f ∣ C a * pderiv 0 f + C b * pderiv 1 f) :
    C a * pderiv 0 f + C b * pderiv 1 f = 0 := by
  by_contra hn
  have hle := totalDegree_le_of_dvd_of_isDomain hdiv hn
  have hlt := totalDegree_direction_le_tsub_one f a b
  omega

theorem direction_not_dvd_of_nonlinear_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hp : f.totalDegree < p) (hd : 1 < f.totalDegree)
    (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ f ∣ C a * pderiv 0 f + C b * pderiv 1 f := by
  intro hdiv
  obtain ⟨u, v, w, _, he⟩ := CurveDirection.irreducible_direction_eq_affine_charP
    p hf hp a b hab (direction_zero_of_dvd (by omega) a b hdiv)
  have hdegree : f.totalDegree ≤ 1 := he ▸ totalDegree_affine_le_one u v w
  omega

theorem direction_not_dvd_of_nonlinear_charZero [IsAlgClosed k] [CharZero k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f) (hd : 1 < f.totalDegree)
    (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ f ∣ C a * pderiv 0 f + C b * pderiv 1 f := by
  intro hdiv
  obtain ⟨u, v, w, _, he⟩ := CurveDirection.irreducible_direction_eq_affine_charZero
    hf a b hab (direction_zero_of_dvd (by omega) a b hdiv)
  have hdegree : f.totalDegree ≤ 1 := he ▸ totalDegree_affine_le_one u v w
  omega

theorem zeroLocus_direction_eq_affine_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hp : f.totalDegree < p)
    (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hvan : ∀ x : Fin 2 → k, eval x f = 0 →
      a * eval x (pderiv 0 f) + b * eval x (pderiv 1 f) = 0) :
    ∃ u v w : k, (u ≠ 0 ∨ v ≠ 0) ∧ f = C u * X 0 + C v * X 1 + C w := by
  apply CurveDirection.irreducible_direction_eq_affine_charP p hf hp a b hab
  apply direction_zero_of_dvd (totalDegree_pos_of_irreducible hf) a b
  apply irreducible_dvd_of_zeroLocus_vanishing hf
  intro x hx
  simpa only [eval_add, eval_mul, eval_C] using hvan x hx

theorem zeroLocus_direction_eq_affine_charZero [IsAlgClosed k] [CharZero k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hvan : ∀ x : Fin 2 → k, eval x f = 0 →
      a * eval x (pderiv 0 f) + b * eval x (pderiv 1 f) = 0) :
    ∃ u v w : k, (u ≠ 0 ∨ v ≠ 0) ∧ f = C u * X 0 + C v * X 1 + C w := by
  apply CurveDirection.irreducible_direction_eq_affine_charZero hf a b hab
  apply direction_zero_of_dvd (totalDegree_pos_of_irreducible hf) a b
  apply irreducible_dvd_of_zeroLocus_vanishing hf
  intro x hx
  simpa only [eval_add, eval_mul, eval_C] using hvan x hx

#print axioms totalDegree_pderiv_le_tsub_one
#print axioms totalDegree_direction_le_tsub_one
#print axioms direction_zero_of_dvd
#print axioms direction_not_dvd_of_nonlinear_charP
#print axioms direction_not_dvd_of_nonlinear_charZero
#print axioms zeroLocus_direction_eq_affine_charP
#print axioms zeroLocus_direction_eq_affine_charZero

end PrimeGap182.TypeIII.CurvePolynomial
