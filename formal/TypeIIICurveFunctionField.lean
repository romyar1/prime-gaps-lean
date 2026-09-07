import TypeIIICurveGauss
import TypeIIIConstantField

/-! The actual rational Gauss slope of a nonlinear irreducible plane curve.

The function field is the fraction field of its actual coordinate ring.
Transcendence of the slope is the algebraic generic-direction conclusion;
this file does not construct a ramified projection or a Fourier sheaf.
-/

noncomputable section
open scoped Classical
open MvPolynomial IntermediateField

namespace PrimeGap182.TypeIII.CurveFunctionField

variable {k : Type*} [Field k]

abbrev coordinateRing (f : MvPolynomial (Fin 2) k) :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {f}

instance coordinateRing_isDomain (f : MvPolynomial (Fin 2) k)
    [Fact (Irreducible f)] : IsDomain (coordinateRing f) := by
  let : (Ideal.span {f}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime (Fact.out : Irreducible f).prime
  exact Ideal.Quotient.isDomain _

abbrev functionField (f : MvPolynomial (Fin 2) k) := FractionRing (coordinateRing f)

def polynomialMap (f : MvPolynomial (Fin 2) k) :
    MvPolynomial (Fin 2) k →ₐ[k] functionField f :=
  (IsScalarTower.toAlgHom k (coordinateRing f) (functionField f)).comp
    (Ideal.Quotient.mkₐ k (Ideal.span {f}))

theorem polynomialMap_eq_zero_iff (f g : MvPolynomial (Fin 2) k) :
    polynomialMap f g = 0 ↔ f ∣ g := by
  change algebraMap (coordinateRing f) (functionField f)
    (Ideal.Quotient.mk (Ideal.span {f}) g) = 0 ↔ f ∣ g
  rw [map_eq_zero_iff _ (IsFractionRing.injective (coordinateRing f) (functionField f)),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

variable {f : MvPolynomial (Fin 2) k} [Fact (Irreducible f)]

def gaussSlope (f : MvPolynomial (Fin 2) k) [Fact (Irreducible f)] :
    functionField f := polynomialMap f (pderiv 1 f) / polynomialMap f (pderiv 0 f)

theorem partial_zero_ne_zero_charP [IsAlgClosed k] (p : ℕ) [CharP k p]
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) :
    polynomialMap f (pderiv 0 f) ≠ 0 := by
  rw [ne_eq, polynomialMap_eq_zero_iff]
  simpa only [C_1, C_0, one_mul, zero_mul, add_zero] using
    CurvePolynomial.direction_not_dvd_of_nonlinear_charP p
      (Fact.out : Irreducible f) hp hd (1 : k) 0 (Or.inl one_ne_zero)

theorem partial_zero_ne_zero_charZero [IsAlgClosed k] [CharZero k]
    (hd : 1 < f.totalDegree) : polynomialMap f (pderiv 0 f) ≠ 0 := by
  rw [ne_eq, polynomialMap_eq_zero_iff]
  simpa only [C_1, C_0, one_mul, zero_mul, add_zero] using
    CurvePolynomial.direction_not_dvd_of_nonlinear_charZero
      (Fact.out : Irreducible f) hd (1 : k) 0 (Or.inl one_ne_zero)

private theorem slope_ne_constant_of_direction_not_dvd (c : k)
    (hden : polynomialMap f (pderiv 0 f) ≠ 0)
    (hdir : ¬f ∣ C (-c) * pderiv 0 f + C 1 * pderiv 1 f) :
    gaussSlope f ≠ algebraMap k (functionField f) c := by
  intro he
  have hr := (div_eq_iff hden).mp he
  apply hdir
  apply (polynomialMap_eq_zero_iff f _).mp
  simp only [map_add, map_mul, map_neg, map_one, one_mul]
  change -(algebraMap k (functionField f) c) * polynomialMap f (pderiv 0 f) +
    polynomialMap f (pderiv 1 f) = 0
  rw [hr]
  ring

theorem gaussSlope_ne_constant_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) (c : k) :
    gaussSlope f ≠ algebraMap k (functionField f) c :=
  slope_ne_constant_of_direction_not_dvd c (partial_zero_ne_zero_charP p hp hd)
    (CurvePolynomial.direction_not_dvd_of_nonlinear_charP p
      (Fact.out : Irreducible f) hp hd (-c) 1 (Or.inr one_ne_zero))

theorem gaussSlope_ne_constant_charZero [IsAlgClosed k] [CharZero k]
    (hd : 1 < f.totalDegree) (c : k) :
    gaussSlope f ≠ algebraMap k (functionField f) c :=
  slope_ne_constant_of_direction_not_dvd c (partial_zero_ne_zero_charZero hd)
    (CurvePolynomial.direction_not_dvd_of_nonlinear_charZero
      (Fact.out : Irreducible f) hd (-c) 1 (Or.inr one_ne_zero))

theorem gaussSlope_transcendental_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) :
    Transcendental k (gaussSlope f) := by
  intro ha
  obtain ⟨c, hc⟩ := exists_constant_of_isAlgebraic ha
  exact gaussSlope_ne_constant_charP p hp hd c hc.symm

theorem gaussSlope_transcendental_charZero [IsAlgClosed k] [CharZero k]
    (hd : 1 < f.totalDegree) : Transcendental k (gaussSlope f) := by
  intro ha
  obtain ⟨c, hc⟩ := exists_constant_of_isAlgebraic ha
  exact gaussSlope_ne_constant_charZero hd c hc.symm

/-- The actual rational projection value at the generic tangent point. -/
def criticalValue (f : MvPolynomial (Fin 2) k) [Fact (Irreducible f)] :
    functionField f := polynomialMap f (X 0) + gaussSlope f * polynomialMap f (X 1)

omit [Fact (Irreducible f)] in
theorem defining_equation : polynomialMap f f = 0 :=
  (polynomialMap_eq_zero_iff f f).mpr dvd_rfl

theorem critical_direction_equation (hden : polynomialMap f (pderiv 0 f) ≠ 0) :
    polynomialMap f (pderiv 1 f) -
      gaussSlope f * polynomialMap f (pderiv 0 f) = 0 := by
  rw [gaussSlope, div_mul_cancel₀ _ hden, sub_self]

theorem partial_mul_criticalValue (hden : polynomialMap f (pderiv 0 f) ≠ 0) :
    polynomialMap f (pderiv 0 f) * criticalValue f =
      polynomialMap f (X 0 * pderiv 0 f + X 1 * pderiv 1 f) := by
  simp only [criticalValue, gaussSlope, map_add, map_mul]
  field_simp

theorem criticalValue_ne_zero_charP [IsAlgClosed k] (p : ℕ) [CharP k p]
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) : criticalValue f ≠ 0 := by
  intro hzero
  have hE : polynomialMap f (X 0 * pderiv 0 f + X 1 * pderiv 1 f) = 0 := by
    rw [← partial_mul_criticalValue (partial_zero_ne_zero_charP p hp hd), hzero, mul_zero]
  have hdiv := (polynomialMap_eq_zero_iff f _).mp hE
  obtain ⟨a, b, _, he⟩ := CurvePolynomial.irreducible_bivariate_dvd_euler_eq_linear_charP
    p (Fact.out : Irreducible f) hp hdiv
  have hdeg : f.totalDegree ≤ 1 := by
    simpa only [C_0, add_zero, ← he] using CurvePolynomial.totalDegree_affine_le_one a b 0
  omega

theorem criticalValue_ne_zero_charZero [IsAlgClosed k] [CharZero k]
    (hd : 1 < f.totalDegree) : criticalValue f ≠ 0 := by
  intro hzero
  have hE : polynomialMap f (X 0 * pderiv 0 f + X 1 * pderiv 1 f) = 0 := by
    rw [← partial_mul_criticalValue (partial_zero_ne_zero_charZero hd), hzero, mul_zero]
  have hdiv := (polynomialMap_eq_zero_iff f _).mp hE
  obtain ⟨a, b, _, he⟩ := CurvePolynomial.irreducible_bivariate_dvd_euler_eq_linear_charZero
    (Fact.out : Irreducible f) hdiv
  have hdeg : f.totalDegree ≤ 1 := by
    simpa only [C_0, add_zero, ← he] using CurvePolynomial.totalDegree_affine_le_one a b 0
  omega

def parameterEmbedding (ht : Transcendental k (gaussSlope f)) :
    RatFunc k →ₐ[k] functionField f :=
  (k⟮gaussSlope f⟯.val).comp
    (RatFunc.algEquivOfTranscendental (gaussSlope f) ht).toAlgHom

theorem parameterEmbedding_X (ht : Transcendental k (gaussSlope f)) :
    parameterEmbedding ht RatFunc.X = gaussSlope f := by
  change ((RatFunc.algEquivOfTranscendental (gaussSlope f) ht) RatFunc.X : functionField f) = _
  exact RatFunc.algEquivOfTranscendental_X (gaussSlope f) ht

theorem parameterEmbedding_injective (ht : Transcendental k (gaussSlope f)) :
    Function.Injective (parameterEmbedding ht) := (parameterEmbedding ht).injective

#print axioms polynomialMap_eq_zero_iff
#print axioms partial_zero_ne_zero_charP
#print axioms gaussSlope_ne_constant_charP
#print axioms gaussSlope_transcendental_charP
#print axioms gaussSlope_transcendental_charZero
#print axioms defining_equation
#print axioms critical_direction_equation
#print axioms criticalValue_ne_zero_charP
#print axioms criticalValue_ne_zero_charZero
#print axioms parameterEmbedding_X
#print axioms parameterEmbedding_injective

end PrimeGap182.TypeIII.CurveFunctionField
