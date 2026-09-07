import TypeIIICoefficientCovariance
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Coefficient covariance over arbitrary finite fields

The actual Kloosterman, correlation, kernel, four-cycle, and positive Fourier
sums are defined over a finite field `K`, with normalization `1 / #K` and an
explicit complex additive character.  Their coefficient covariance is an
exact change of finite summation variables.  The same complex automorphism
works for every field of characteristic `p` and every additive character,
because all character values are `p`th roots of unity.

The standard character composed with the field trace supplies the canonical
nontrivial character over each finite extension.  These are arithmetic
identities; no sheaf comparison, exceptional support, or Fourier estimate
is asserted.
-/

noncomputable section

open scoped BigOperators Classical

universe u v

namespace PrimeGap182.TypeIII.FiniteFieldSums

section FiniteSums

variable {K : Type u} [Field K] [Fintype K] (ψ : AddChar K ℂ)

/-- The normalized rank-three sum over `K`, including its value at zero. -/
def kl3 (t : K) : ℂ :=
  (Fintype.card K : ℂ)⁻¹ *
    ∑ u : Kˣ, ∑ v : Kˣ,
      ψ ((u : K) + (v : K) + t / ((u : K) * (v : K)))

/-- The actual common-unit correlation with additive frequency `c`. -/
def correlation (A B c : K) : ℂ :=
  ∑ h : Kˣ, kl3 ψ (A * (h : K)) * star (kl3 ψ (B * (h : K))) * ψ (c * (h : K))

/-- The same nonlinear torus substitution and zero extension as over `ZMod p`. -/
def kernel (α m n x y : K) : ℂ :=
  if x = 0 ∨ y = 0 then 0 else
    correlation ψ (α * y / (m * x ^ 2)) (α * x / (n * y ^ 2)) 1

/-- The original four-factor conjugation pattern, over `K`. -/
def fourCycle (α m m' n n' x y : K) : ℂ :=
  kernel ψ α m n x y * star (kernel ψ α m' n x y) *
    kernel ψ α m' n' x y * star (kernel ψ α m n' x y)

/-- The unnormalized two-variable Fourier sum with positive additive phase. -/
def fourier₂ (f : K → K → ℂ) (h k : K) : ℂ :=
  ∑ x : K, ∑ y : K, f x y * ψ (h * x + k * y)

/-- Finite-field character values conjugate by negating the argument. -/
theorem character_star (t : K) : star (ψ t) = ψ (-t) := by
  have hK : 0 < ringChar K :=
    Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite K)
  exact AddChar.starComp_apply hK t

/-- The finite-sum involution for rank three works over every finite field. -/
theorem kl3_star (t : K) : star (kl3 ψ t) = kl3 ψ (-t) := by
  unfold kl3
  simp only [star_mul, star_inv₀, star_natCast, star_sum, character_star]
  rw [mul_comm]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft (-1 : Kˣ)) _ _ ?_
  intro u
  refine Fintype.sum_equiv (Equiv.mulLeft (-1 : Kˣ)) _ _ ?_
  intro v
  simp only [Equiv.coe_mulLeft, Units.val_neg, neg_one_mul]
  congr 1
  simp only [neg_mul_neg, neg_div]
  ring

/-- The actual correlation is real, without a pointwise bound. -/
theorem correlation_star (A B c : K) :
    star (correlation ψ A B c) = correlation ψ A B c := by
  unfold correlation
  simp only [star_sum, star_mul, star_star, character_star]
  refine Fintype.sum_equiv (Equiv.mulLeft (-1 : Kˣ)) _ _ ?_
  intro h
  simp only [Equiv.coe_mulLeft, Units.val_neg, neg_one_mul, mul_neg,
    ← kl3_star, star_star]
  ring

/-- Reality includes the prescribed zero values on the axes. -/
theorem kernel_star (α m n x y : K) :
    star (kernel ψ α m n x y) = kernel ψ α m n x y := by
  unfold kernel
  split_ifs
  · exact star_zero _
  · exact correlation_star ψ _ _ _

/-- Cubic covariance follows by scaling the two Kloosterman variables. -/
theorem kl3_coefficient_covariance (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (t : K) :
    σ (kl3 ψ t) = kl3 ψ (a ^ 3 * t) := by
  simp only [kl3, map_mul, map_inv₀, map_natCast, map_sum, hσ]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 a ha)) _ _ ?_
  intro u
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 a ha)) _ _ ?_
  intro v
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0]
  congr 1
  field_simp

/-- The coefficient map commutes with conjugation on these specific sums. -/
theorem kl3_star_coefficient_covariance (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (t : K) :
    σ (star (kl3 ψ t)) = star (kl3 ψ (a ^ 3 * t)) := by
  rw [kl3_star, kl3_coefficient_covariance ψ σ a ha hσ, kl3_star, mul_neg]

/-- Reindexing the shared unit variable gives quadratic parameter scaling. -/
theorem correlation_coefficient_covariance (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (A B c : K) :
    σ (correlation ψ A B c) = correlation ψ (a ^ 2 * A) (a ^ 2 * B) c := by
  simp only [correlation, map_sum, map_mul,
    kl3_coefficient_covariance ψ σ a ha hσ,
    kl3_star_coefficient_covariance ψ σ a ha hσ, hσ]
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 a ha)) _ _ ?_
  intro h
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0]
  have hA : a ^ 3 * (A * (h : K)) = a ^ 2 * A * (a * (h : K)) := by ring
  have hB : a ^ 3 * (B * (h : K)) = a ^ 2 * B * (a * (h : K)) := by ring
  have hc : a * (c * (h : K)) = c * (a * (h : K)) := by ring
  rw [hA, hB, hc]

/-- Coefficient covariance preserves the exact torus substitution. -/
theorem kernel_coefficient_covariance (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (α m n x y : K) :
    σ (kernel ψ α m n x y) = kernel ψ (a ^ 2 * α) m n x y := by
  by_cases hxy : x = 0 ∨ y = 0
  · simp [kernel, hxy]
  · rw [kernel, ite_eq_right hxy, kernel, ite_eq_right hxy,
      correlation_coefficient_covariance ψ σ a ha hσ]
    congr 1 <;> ring

/-- Covariance of all four actual kernel factors. -/
theorem fourCycle_coefficient_covariance (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (α m m' n n' x y : K) :
    σ (fourCycle ψ α m m' n n' x y) =
      fourCycle ψ (a ^ 2 * α) m m' n n' x y := by
  simp only [fourCycle, kernel_star, map_mul,
    kernel_coefficient_covariance ψ σ a ha hσ]

/-- The simultaneous physical and common-parameter dilation. -/
theorem kernel_common_parameter_dilation (α m n b x y : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hb : b ≠ 0) :
    kernel ψ (b * α) m n (b * x) (b * y) = kernel ψ α m n x y := by
  by_cases hx : x = 0
  · subst x
    simp [kernel]
  by_cases hy : y = 0
  · subst y
    simp [kernel]
  rw [kernel, ite_eq_right (not_or.mpr ⟨mul_ne_zero hb hx, mul_ne_zero hb hy⟩),
    kernel, ite_eq_right (not_or.mpr ⟨hx, hy⟩)]
  congr 1 <;> field_simp

/-- The corresponding exact identity for the four-cycle. -/
theorem fourCycle_common_parameter_dilation (α m m' n n' b x y : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) (hb : b ≠ 0) :
    fourCycle ψ (b * α) m m' n n' (b * x) (b * y) =
      fourCycle ψ α m m' n n' x y := by
  simp only [fourCycle,
    kernel_common_parameter_dilation ψ α m n b x y hm hn hb,
    kernel_common_parameter_dilation ψ α m' n b x y hm' hn hb,
    kernel_common_parameter_dilation ψ α m' n' b x y hm' hn' hb,
    kernel_common_parameter_dilation ψ α m n' b x y hm hn' hb]

/-- An exact Fourier change of variables over an arbitrary finite field. -/
theorem fourier₂_scale (f : K → K → ℂ) (a b h k : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    fourier₂ ψ (fun x y => f (a * x) (b * y)) h k =
      fourier₂ ψ f (h / a) (k / b) := by
  unfold fourier₂
  refine Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ ?_
  intro x
  refine Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ ?_
  intro y
  change f (a * x) (b * y) * ψ (h * x + k * y) =
    f (a * x) (b * y) * ψ ((h / a) * (a * x) + (k / b) * (b * y))
  congr 2
  field_simp

/-- The original positive Fourier transform has cubic frequency covariance. -/
theorem fourier₂_fourCycle_coefficient_covariance (σ : ℂ →+* ℂ) (a : K) (ha : a ≠ 0)
    (hσ : ∀ t : K, σ (ψ t) = ψ (a * t)) (α m m' n n' h k : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    σ (fourier₂ ψ (fourCycle ψ α m m' n n') h k) =
      fourier₂ ψ (fourCycle ψ α m m' n n') (a ^ 3 * h) (a ^ 3 * k) := by
  have he : σ (fourier₂ ψ (fourCycle ψ α m m' n n') h k) =
      fourier₂ ψ (fourCycle ψ (a ^ 2 * α) m m' n n') (a * h) (a * k) := by
    simp only [fourier₂, map_sum, map_mul,
      fourCycle_coefficient_covariance ψ σ a ha hσ, hσ]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    congr 2
    ring
  rw [he]
  have hb : a ^ 2 ≠ 0 := pow_ne_zero _ ha
  have hs := fourier₂_scale ψ (fourCycle ψ (a ^ 2 * α) m m' n n')
    (a ^ 2) (a ^ 2) (a ^ 3 * h) (a ^ 3 * k) hb hb
  have hh : (a ^ 3 * h) / (a ^ 2) = a * h := by field_simp
  have hk : (a ^ 3 * k) / (a ^ 2) = a * k := by field_simp
  rw [hh, hk] at hs
  rw [← hs]
  congr 1
  funext x y
  exact fourCycle_common_parameter_dilation ψ α m m' n n' (a ^ 2) x y hm hm' hn hn' hb

end FiniteSums

section PrimeCoefficientAction

variable (p : ℕ) [Fact p.Prime]

/-- The same coefficient map acts on every characteristic-`p` additive
character, because each value is a `p`th root of unity. -/
theorem character_coefficient_covariance (σ : ℂ →+* ℂ) (a : ZMod p)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (K : Type u) [Field K] [CharP K p] (ψ : AddChar K ℂ) (t : K) :
    σ (ψ t) = ψ ((a.val : K) * t) := by
  have hp : ψ t ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero,
      zero_mul, AddChar.map_zero_eq_one]
  obtain ⟨j, _, hj⟩ := (stdAddChar_one_isPrimitiveRoot p).eq_pow_of_pow_eq_one hp
  have ha : ZMod.stdAddChar a = ZMod.stdAddChar (1 : ZMod p) ^ a.val := by
    simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one] using
      (ZMod.stdAddChar (N := p)).map_nsmul_eq_pow a.val (1 : ZMod p)
  calc
    σ (ψ t) = (ψ t) ^ a.val := by
      rw [← hj, map_pow, hσ, mul_one, ha]
      simp only [← pow_mul, Nat.mul_comm]
    _ = ψ ((a.val : K) * t) := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

/-- A nonzero prime-field scalar remains nonzero in every extension. -/
theorem prime_scalar_ne_zero (a : ZMod p) (ha : a ≠ 0)
    (K : Type u) [Field K] [CharP K p] : (a.val : K) ≠ 0 := by
  have h := (ZMod.castHom (dvd_refl p) K).injective.ne ha
  simpa only [map_zero, ZMod.castHom_apply, ZMod.cast_eq_val] using h

/-- One actual complex automorphism is chosen before the finite extension,
its additive character, and every parameter of the arithmetic transform.
The character may be any nontrivial one; the identity also holds for the
trivial character. -/
theorem exists_uniform_fourier_coefficient_automorphism (a : ZMod p) (ha : a ≠ 0) :
    ∃ σ : ℂ ≃+* ℂ,
      (∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t)) ∧
      ∀ (K : Type u) [Field K] [Fintype K] [CharP K p] (ψ : AddChar K ℂ),
        (∀ t : K, σ (ψ t) = ψ ((a.val : K) * t)) ∧
        ∀ α m m' n n' h k : K,
          m ≠ 0 → m' ≠ 0 → n ≠ 0 → n' ≠ 0 →
          σ (fourier₂ ψ (fourCycle ψ α m m' n n') h k) =
            fourier₂ ψ (fourCycle ψ α m m' n n')
              ((a.val : K) ^ 3 * h) ((a.val : K) ^ 3 * k) := by
  obtain ⟨σ, hσ⟩ := exists_stdAddChar_coefficient_automorphism p a ha
  refine ⟨σ, hσ, ?_⟩
  intro K _ _ _ ψ
  have hψ := character_coefficient_covariance p σ.toRingHom a hσ K ψ
  refine ⟨hψ, ?_⟩
  intro α m m' n n' h k hm hm' hn hn'
  exact fourier₂_fourCycle_coefficient_covariance ψ σ.toRingHom (a.val : K)
    (prime_scalar_ne_zero p a ha K) hψ α m m' n n' h k hm hm' hn hn'

/-- Vanishing of the actual extension-field Fourier coefficient is
invariant under this prime-field cubic dilation. -/
theorem fourCycle_fourier_zero_iff_prime_dilation (a : ZMod p) (ha : a ≠ 0)
    (K : Type u) [Field K] [Fintype K] [CharP K p] (ψ : AddChar K ℂ)
    (α m m' n n' h k : K)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourier₂ ψ (fourCycle ψ α m m' n n') h k = 0 ↔
      fourier₂ ψ (fourCycle ψ α m m' n n')
        ((a.val : K) ^ 3 * h) ((a.val : K) ^ 3 * k) = 0 := by
  obtain ⟨σ, _, hσ⟩ := exists_uniform_fourier_coefficient_automorphism p a ha
  rw [← (hσ K ψ).2 α m m' n n' h k hm hm' hn hn']
  constructor
  · intro hz
    simp only [hz, map_zero]
  · intro hz
    exact σ.injective (by simpa only [map_zero] using hz)

end PrimeCoefficientAction

section TraceCharacters

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [Fintype K] [Algebra (ZMod p) K]

/-- The canonical Artin--Schreier trace character over the finite extension. -/
def traceAddChar : AddChar K ℂ :=
  (ZMod.stdAddChar (N := p)).compAddMonoidHom (Algebra.trace (ZMod p) K).toAddMonoidHom

/-- The trace is surjective even when the extension degree is divisible
by `p`; hence this character is nontrivial in every finite extension. -/
theorem traceAddChar_ne_one : traceAddChar p K ≠ 1 := by
  obtain ⟨t, ht⟩ := Algebra.trace_surjective (ZMod p) K (1 : ZMod p)
  intro he
  have hv := DFunLike.congr_fun he t
  change ZMod.stdAddChar (Algebra.trace (ZMod p) K t) = 1 at hv
  rw [ht, ← (ZMod.stdAddChar (N := p)).map_zero_eq_one] at hv
  exact one_ne_zero (ZMod.injective_stdAddChar hv)

/-- Over a field, nontriviality gives primitivity for the trace character. -/
theorem traceAddChar_isPrimitive : (traceAddChar p K).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one (traceAddChar_ne_one p K)

/-- On prime-field elements the trace character is raised to the extension
degree, rather than being silently identified with its base character. -/
theorem traceAddChar_algebraMap (a : ZMod p) :
    traceAddChar p K (algebraMap (ZMod p) K a) =
      ZMod.stdAddChar a ^ Module.finrank (ZMod p) K := by
  simp only [traceAddChar, AddChar.compAddMonoidHom_apply,
    LinearMap.toAddMonoidHom_coe, Algebra.trace_algebraMap, AddChar.map_nsmul_eq_pow]

/-- The explicit finite-field trace polynomial fixes the extension-field
Artin--Schreier normalization. -/
theorem trace_eq_sum_prime_powers (t : K) :
    algebraMap (ZMod p) K (Algebra.trace (ZMod p) K t) =
      ∑ i ∈ Finset.range (Module.finrank (ZMod p) K), t ^ (p ^ i) := by
  simpa only [Nat.card_zmod] using FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) K t

/-- Field trace is unchanged by the prime Frobenius. -/
theorem trace_prime_frobenius (t : K) :
    Algebra.trace (ZMod p) K (t ^ p) = Algebra.trace (ZMod p) K t := by
  simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using
    Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K) t

/-- The trace character annihilates an Artin--Schreier coboundary. -/
theorem traceAddChar_artinSchreier (t : K) : traceAddChar p K (t ^ p - t) = 1 := by
  simp only [traceAddChar, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
    map_sub, trace_prime_frobenius p K, sub_self, AddChar.map_zero_eq_one]

/-- Extending the character through a tower agrees with taking the trace
directly to the prime field. -/
theorem traceAddChar_tower (L : Type v) [Field L] [Fintype L]
    [Algebra K L] [Algebra (ZMod p) L] [IsScalarTower (ZMod p) K L] (t : L) :
    traceAddChar p L t = traceAddChar p K (Algebra.trace K L t) := by
  simp only [traceAddChar, AddChar.compAddMonoidHom_apply,
    LinearMap.toAddMonoidHom_coe, Algebra.trace_trace]

end TraceCharacters

section UniformTraceCovariance

variable (p : ℕ) [Fact p.Prime]

/-- The single coefficient automorphism acts on the canonical trace-character
transform over every finite extension, using the actual algebra-map image
of the prime-field scalar. -/
theorem exists_uniform_trace_fourier_coefficient_automorphism (a : ZMod p) (ha : a ≠ 0) :
    ∃ σ : ℂ ≃+* ℂ,
      (∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t)) ∧
      ∀ (K : Type u) [Field K] [Fintype K] [Algebra (ZMod p) K],
        (∀ t : K, σ (traceAddChar p K t) =
          traceAddChar p K (algebraMap (ZMod p) K a * t)) ∧
        ∀ α m m' n n' h k : K,
          m ≠ 0 → m' ≠ 0 → n ≠ 0 → n' ≠ 0 →
          σ (fourier₂ (traceAddChar p K)
            (fourCycle (traceAddChar p K) α m m' n n') h k) =
          fourier₂ (traceAddChar p K) (fourCycle (traceAddChar p K) α m m' n n')
            ((algebraMap (ZMod p) K a) ^ 3 * h) ((algebraMap (ZMod p) K a) ^ 3 * k) := by
  obtain ⟨σ, hσ, he⟩ := exists_uniform_fourier_coefficient_automorphism p a ha
  refine ⟨σ, hσ, ?_⟩
  intro K _ _ _
  let : CharP K p := ((algebraMap (ZMod p) K).charP_iff_charP p).mp inferInstance
  have hmap : algebraMap (ZMod p) K a = (a.val : K) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [map_natCast]
  simpa only [hmap] using he K (traceAddChar p K)

end UniformTraceCovariance

section PrimeFieldCompatibility

variable (p : ℕ) [Fact p.Prime]

/-- For the degree-one extension the trace character is exactly the
standard character used in the existing formalization. -/
theorem traceAddChar_prime : traceAddChar p (ZMod p) = ZMod.stdAddChar := by
  ext t
  simp only [traceAddChar, AddChar.compAddMonoidHom_apply,
    LinearMap.toAddMonoidHom_coe, Algebra.trace_self_apply]

/-- Compatibility includes the full normalization and the zero argument. -/
theorem kl3_prime (t : ZMod p) :
    kl3 (traceAddChar p (ZMod p)) t = PrimeGap182.TypeIII.kl3 p t := by
  simp only [traceAddChar_prime, kl3, PrimeGap182.TypeIII.kl3, ZMod.card]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro u _
  apply Finset.sum_congr (by ext; simp)
  intro v _
  rfl

/-- The extension definition specializes to the actual prime-field correlation. -/
theorem correlation_prime (A B c : ZMod p) :
    correlation (traceAddChar p (ZMod p)) A B c =
      PrimeGap182.TypeIII.correlation p A B c := by
  unfold correlation PrimeGap182.TypeIII.correlation
  simp_rw [kl3_prime]
  rw [traceAddChar_prime]
  apply Finset.sum_congr (by ext; simp)
  intro h _
  rfl

/-- The axes and nonlinear parameters also agree exactly. -/
theorem kernel_prime (α m n x y : ZMod p) :
    kernel (traceAddChar p (ZMod p)) α m n x y =
      PrimeGap182.TypeIII.kernel p α m n x y := by
  simp only [kernel, correlation_prime, PrimeGap182.TypeIII.kernel]

/-- Compatibility of the actual four-cycle. -/
theorem fourCycle_prime (α m m' n n' x y : ZMod p) :
    fourCycle (traceAddChar p (ZMod p)) α m m' n n' x y =
      PrimeGap182.TypeIII.fourCycle p α m m' n n' x y := by
  simp only [fourCycle, kernel_prime, PrimeGap182.TypeIII.fourCycle]

/-- Compatibility of the positive Fourier transform, with no omitted axes. -/
theorem fourier₂_prime (f : ZMod p → ZMod p → ℂ) (h k : ZMod p) :
    fourier₂ (traceAddChar p (ZMod p)) f h k = PrimeGap182.TypeIII.fourier₂ p f h k := by
  simp only [fourier₂, traceAddChar_prime, PrimeGap182.TypeIII.fourier₂]

/-- The complete extension-field arithmetic coefficient reduces to the
existing Type III coefficient in degree one. -/
theorem fourier₂_fourCycle_prime (α m m' n n' h k : ZMod p) :
    fourier₂ (traceAddChar p (ZMod p))
      (fourCycle (traceAddChar p (ZMod p)) α m m' n n') h k =
      PrimeGap182.TypeIII.fourier₂ p (PrimeGap182.TypeIII.fourCycle p α m m' n n') h k := by
  simp only [fourier₂_prime]
  congr 1
  funext x y
  exact fourCycle_prime p α m m' n n' x y

end PrimeFieldCompatibility

#print axioms kl3
#print axioms correlation
#print axioms kernel
#print axioms fourCycle
#print axioms fourier₂
#print axioms character_star
#print axioms kl3_star
#print axioms correlation_star
#print axioms kernel_star
#print axioms kl3_coefficient_covariance
#print axioms kl3_star_coefficient_covariance
#print axioms correlation_coefficient_covariance
#print axioms kernel_coefficient_covariance
#print axioms fourCycle_coefficient_covariance
#print axioms kernel_common_parameter_dilation
#print axioms fourCycle_common_parameter_dilation
#print axioms fourier₂_scale
#print axioms fourier₂_fourCycle_coefficient_covariance
#print axioms character_coefficient_covariance
#print axioms prime_scalar_ne_zero
#print axioms exists_uniform_fourier_coefficient_automorphism
#print axioms fourCycle_fourier_zero_iff_prime_dilation
#print axioms traceAddChar
#print axioms traceAddChar_ne_one
#print axioms traceAddChar_isPrimitive
#print axioms traceAddChar_algebraMap
#print axioms trace_eq_sum_prime_powers
#print axioms trace_prime_frobenius
#print axioms traceAddChar_artinSchreier
#print axioms traceAddChar_tower
#print axioms exists_uniform_trace_fourier_coefficient_automorphism
#print axioms traceAddChar_prime
#print axioms kl3_prime
#print axioms correlation_prime
#print axioms kernel_prime
#print axioms fourCycle_prime
#print axioms fourier₂_prime
#print axioms fourier₂_fourCycle_prime

end PrimeGap182.TypeIII.FiniteFieldSums
