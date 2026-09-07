import IncidenceTensor

/-!
# The actual incidence kernel under the Chinese remainder theorem

Composite moduli use an actual unit mask on the full denominator. Thus the
zero rows and the q=1 convention are retained. Both amplitude and frequency
parameters receive the complement inverse required by the standard additive
character. Complete modes are proved to be reindexed Kronecker products.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

/-- The genuine composite-modulus kernel; nonunit denominators give zero. -/
def incidenceMatrixMod {q : ℕ} [NeZero q] (A : ZMod q) :
    Matrix (ZMod q × ZMod q) (ZMod q) ℂ := by
  classical
  exact fun z b => if IsUnit (z.1 * (z.2 + z.1 * b)) then
    ZMod.stdAddChar (A * (z.1 * (z.2 + z.1 * b))⁻¹) else 0

def incidenceModeMod {q : ℕ} [NeZero q] (A : ZMod q) (ξ : ZMod q × ZMod q) :
    Matrix (ZMod q) (ZMod q) ℂ := incidenceMode (incidenceMatrixMod A) ξ

theorem incidenceMatrixMod_eq_prime {p : ℕ} [Fact p.Prime] (A : ZMod p) :
    incidenceMatrixMod A = primeIncidenceMatrix A := by
  ext z b
  simp only [incidenceMatrixMod, isUnit_iff_ne_zero, primeIncidenceMatrix,
    incidenceReciprocal, incidenceCharacter, div_eq_mul_inv]
  by_cases hd : z.1 * (z.2 + z.1 * b) = 0 <;> simp [hd]

theorem incidenceModeMod_eq_prime {p : ℕ} [Fact p.Prime]
    (A : ZMod p) (ξ : ZMod p × ZMod p) :
    incidenceModeMod A ξ = primeIncidenceMode A ξ := by
  rw [incidenceModeMod, incidenceMatrixMod_eq_prime]
  rfl

def incidenceCRTLeft {m n : ℕ} (hmn : m.Coprime n) :
    ZMod (m * n) →+* ZMod m :=
  (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder hmn).toRingHom

def incidenceCRTRight {m n : ℕ} (hmn : m.Coprime n) :
    ZMod (m * n) →+* ZMod n :=
  (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder hmn).toRingHom

def incidenceCRTScaledLeft {m n : ℕ} (hmn : m.Coprime n) (z : ZMod (m * n)) :
    ZMod m := (n : ZMod m)⁻¹ * incidenceCRTLeft hmn z

def incidenceCRTScaledRight {m n : ℕ} (hmn : m.Coprime n) (z : ZMod (m * n)) :
    ZMod n := (m : ZMod n)⁻¹ * incidenceCRTRight hmn z

def incidenceCRTRows {m n : ℕ} (hmn : m.Coprime n) :
    (ZMod (m * n) × ZMod (m * n)) ≃ ((ZMod m × ZMod m) × (ZMod n × ZMod n)) :=
  (((ZMod.chineseRemainder hmn).toEquiv).prodCongr
    (ZMod.chineseRemainder hmn).toEquiv).trans
      (Equiv.prodProdProdComm (ZMod m) (ZMod n) (ZMod m) (ZMod n))

@[simp] theorem incidenceCRTScaledLeft_zero {m n : ℕ} (hmn : m.Coprime n) :
    incidenceCRTScaledLeft hmn 0 = 0 := by simp [incidenceCRTScaledLeft]

@[simp] theorem incidenceCRTScaledRight_zero {m n : ℕ} (hmn : m.Coprime n) :
    incidenceCRTScaledRight hmn 0 = 0 := by simp [incidenceCRTScaledRight]

theorem incidenceCRTScaledLeft_mul_intCast {m n : ℕ} (hmn : m.Coprime n)
    (t : ZMod (m * n)) (a : ℤ) :
    incidenceCRTScaledLeft hmn (t * (a : ZMod (m * n))) =
      incidenceCRTScaledLeft hmn t * (a : ZMod m) := by
  simp [incidenceCRTScaledLeft, mul_assoc]

theorem incidenceCRTScaledRight_mul_intCast {m n : ℕ} (hmn : m.Coprime n)
    (t : ZMod (m * n)) (a : ℤ) :
    incidenceCRTScaledRight hmn (t * (a : ZMod (m * n))) =
      incidenceCRTScaledRight hmn t * (a : ZMod n) := by
  simp [incidenceCRTScaledRight, mul_assoc]

theorem incidenceCRT_isUnit_iff {m n : ℕ} (hmn : m.Coprime n) (z : ZMod (m * n)) :
    IsUnit z ↔ IsUnit (incidenceCRTLeft hmn z) ∧ IsUnit (incidenceCRTRight hmn z) := by
  change IsUnit z ↔ IsUnit ((ZMod.chineseRemainder hmn) z).1 ∧
    IsUnit ((ZMod.chineseRemainder hmn) z).2
  rw [← Prod.isUnit_iff]
  exact (MulEquiv.isUnit_map (ZMod.chineseRemainder hmn)).symm

theorem incidenceCRTScaledLeft_isUnit {m n : ℕ} (hmn : m.Coprime n)
    (A : ZMod (m * n)) (hA : IsUnit A) : IsUnit (incidenceCRTScaledLeft hmn A) := by
  have hi : IsUnit ((n : ZMod m)⁻¹) := by
    simpa only [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime] using
      ((ZMod.unitOfCoprime n hmn.symm)⁻¹).isUnit
  exact hi.mul (hA.map (incidenceCRTLeft hmn))

theorem incidenceCRTScaledRight_isUnit {m n : ℕ} (hmn : m.Coprime n)
    (A : ZMod (m * n)) (hA : IsUnit A) : IsUnit (incidenceCRTScaledRight hmn A) := by
  have hi : IsUnit ((m : ZMod n)⁻¹) := by
    simpa only [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime] using
      ((ZMod.unitOfCoprime m hmn)⁻¹).isUnit
  exact hi.mul (hA.map (incidenceCRTRight hmn))

/-- CRT for the full kernel, before summing and without deleting zero rows. -/
theorem incidenceMatrixMod_crt {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (A : ZMod (m * n))
    (z : ZMod (m * n) × ZMod (m * n)) (b : ZMod (m * n)) :
    incidenceMatrixMod A z b =
      incidenceMatrixMod (incidenceCRTScaledLeft hmn A)
        (incidenceCRTLeft hmn z.1, incidenceCRTLeft hmn z.2)
        (incidenceCRTLeft hmn b) *
      incidenceMatrixMod (incidenceCRTScaledRight hmn A)
        (incidenceCRTRight hmn z.1, incidenceCRTRight hmn z.2)
        (incidenceCRTRight hmn b) := by
  let d := z.1 * (z.2 + z.1 * b)
  have hdL : incidenceCRTLeft hmn d =
      incidenceCRTLeft hmn z.1 *
        (incidenceCRTLeft hmn z.2 + incidenceCRTLeft hmn z.1 * incidenceCRTLeft hmn b) := by
    simp only [d, map_mul, map_add]
  have hdR : incidenceCRTRight hmn d =
      incidenceCRTRight hmn z.1 *
        (incidenceCRTRight hmn z.2 + incidenceCRTRight hmn z.1 * incidenceCRTRight hmn b) := by
    simp only [d, map_mul, map_add]
  change (if IsUnit d then ZMod.stdAddChar (A * d⁻¹) else 0) = _
  simp only [incidenceMatrixMod, ← hdL, ← hdR]
  by_cases hd : IsUnit d
  · have hL := (incidenceCRT_isUnit_iff hmn d).mp hd |>.1
    have hR := (incidenceCRT_isUnit_iff hmn d).mp hd |>.2
    simp only [ite_eq_left hd, ite_eq_left hL, ite_eq_left hR]
    have hc := PrimeGap186.stdAddChar_coprime_crt m n hmn (A * d⁻¹)
    change ZMod.stdAddChar (A * d⁻¹) =
      ZMod.stdAddChar ((n : ZMod m)⁻¹ * incidenceCRTLeft hmn (A * d⁻¹)) *
        ZMod.stdAddChar ((m : ZMod n)⁻¹ * incidenceCRTRight hmn (A * d⁻¹)) at hc
    simpa only [map_mul, PrimeGap186.phaseCRT_map_inv _ hd,
      incidenceCRTScaledLeft, incidenceCRTScaledRight, mul_assoc] using hc
  · rcases not_and_or.mp (mt (incidenceCRT_isUnit_iff hmn d).mpr hd) with hL | hR
    · simp only [ite_eq_right hd, ite_eq_right hL, zero_mul]
    · simp only [ite_eq_right hd, ite_eq_right hR, mul_zero]

theorem incidenceJointChar_crt {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (ξ z : ZMod (m * n) × ZMod (m * n)) :
    incidenceJointChar ξ z =
      incidenceJointChar (incidenceCRTScaledLeft hmn ξ.1, incidenceCRTScaledLeft hmn ξ.2)
        (incidenceCRTLeft hmn z.1, incidenceCRTLeft hmn z.2) *
      incidenceJointChar (incidenceCRTScaledRight hmn ξ.1, incidenceCRTScaledRight hmn ξ.2)
        (incidenceCRTRight hmn z.1, incidenceCRTRight hmn z.2) := by
  have hc := PrimeGap186.stdAddChar_coprime_crt m n hmn (ξ.1 * z.1 + ξ.2 * z.2)
  change ZMod.stdAddChar (ξ.1 * z.1 + ξ.2 * z.2) =
    ZMod.stdAddChar ((n : ZMod m)⁻¹ * incidenceCRTLeft hmn (ξ.1 * z.1 + ξ.2 * z.2)) *
      ZMod.stdAddChar ((m : ZMod n)⁻¹ * incidenceCRTRight hmn (ξ.1 * z.1 + ξ.2 * z.2)) at hc
  simpa only [incidenceJointChar, incidenceCRTScaledLeft, incidenceCRTScaledRight,
    map_add, map_mul, mul_add, mul_assoc] using hc

/-- The complete twisted Gram matrix is an actual reindexed tensor product. -/
theorem incidenceModeMod_crt {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (A : ZMod (m * n)) (ξ : ZMod (m * n) × ZMod (m * n)) :
    incidenceModeMod A ξ =
      (incidenceModeMod (incidenceCRTScaledLeft hmn A)
          (incidenceCRTScaledLeft hmn ξ.1, incidenceCRTScaledLeft hmn ξ.2) ⊗ₖ
        incidenceModeMod (incidenceCRTScaledRight hmn A)
          (incidenceCRTScaledRight hmn ξ.1, incidenceCRTScaledRight hmn ξ.2)).submatrix
            (ZMod.chineseRemainder hmn) (ZMod.chineseRemainder hmn) := by
  ext b b'
  let f (z : ZMod m × ZMod m) : ℂ :=
    incidenceJointChar (incidenceCRTScaledLeft hmn ξ.1, incidenceCRTScaledLeft hmn ξ.2) z *
      star (incidenceMatrixMod (incidenceCRTScaledLeft hmn A) z (incidenceCRTLeft hmn b)) *
        incidenceMatrixMod (incidenceCRTScaledLeft hmn A) z (incidenceCRTLeft hmn b')
  let g (z : ZMod n × ZMod n) : ℂ :=
    incidenceJointChar (incidenceCRTScaledRight hmn ξ.1, incidenceCRTScaledRight hmn ξ.2) z *
      star (incidenceMatrixMod (incidenceCRTScaledRight hmn A) z (incidenceCRTRight hmn b)) *
        incidenceMatrixMod (incidenceCRTScaledRight hmn A) z (incidenceCRTRight hmn b')
  change incidenceWeightedGram (incidenceMatrixMod A) (incidenceJointChar ξ) b b' = _
  rw [incidenceWeightedGram_apply]
  calc
    _ = ∑ z : (ZMod m × ZMod m) × (ZMod n × ZMod n), f z.1 * g z.2 := by
      refine Fintype.sum_equiv (incidenceCRTRows hmn) _ _ ?_
      intro z
      rw [incidenceJointChar_crt hmn, incidenceMatrixMod_crt hmn,
        incidenceMatrixMod_crt hmn]
      simp only [star_mul]
      change _ = f (incidenceCRTLeft hmn z.1, incidenceCRTLeft hmn z.2) *
        g (incidenceCRTRight hmn z.1, incidenceCRTRight hmn z.2)
      dsimp only [f, g]
      ring
    _ = (∑ z, f z) * ∑ z, g z := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by
      simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, incidenceModeMod,
        incidenceMode, incidenceWeightedGram_apply, incidenceCRTLeft, incidenceCRTRight,
        RingHom.comp_apply, f, g]
      rfl

theorem incidenceModeMod_crt_norm_le {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (A : ZMod (m * n)) (ξ : ZMod (m * n) × ZMod (m * n)) :
    ‖incidenceModeMod A ξ‖ ≤
      ‖incidenceModeMod (incidenceCRTScaledLeft hmn A)
        (incidenceCRTScaledLeft hmn ξ.1, incidenceCRTScaledLeft hmn ξ.2)‖ *
      ‖incidenceModeMod (incidenceCRTScaledRight hmn A)
        (incidenceCRTScaledRight hmn ξ.1, incidenceCRTScaledRight hmn ξ.2)‖ := by
  rw [incidenceModeMod_crt hmn]
  change ‖Matrix.submatrix _ (ZMod.chineseRemainder hmn).toEquiv
    (ZMod.chineseRemainder hmn).toEquiv‖ ≤ _
  rw [incidence_submatrix_equiv_norm]
  exact incidence_kronecker_norm_le _ _

#print axioms incidenceMatrixMod_eq_prime
#print axioms incidenceMatrixMod_crt
#print axioms incidenceJointChar_crt
#print axioms incidenceModeMod_crt
#print axioms incidenceModeMod_crt_norm_le

end PrimeGap182Audit
