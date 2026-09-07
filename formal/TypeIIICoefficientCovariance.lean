import TypeIIIParameterNormalization
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Coefficient covariance of the actual Type III finite sums

A coefficient homomorphism taking the standard additive character at `t`
to its value at `a*t` scales the actual four-cycle Fourier frequencies by
`a³`.  All changes of variables and the zero extensions are retained.

The coefficient action is first isolated as an explicit algebraic premise
about the additive character.  A prime-cyclotomic automorphism, extended to
`ℂ`, then supplies that action for every nonzero `a`.  No Fourier estimate
is a premise or conclusion, and these finite-sum identities do not identify
geometric Fourier supports or assert preservation of complex norms.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Cubic covariance of the actual rank-three Kloosterman sum under a
coefficient map that raises the additive character to its `a`th power. -/
theorem kl3_coefficient_covariance (σ : ℂ →+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (t : ZMod p) : σ (kl3 p t) = kl3 p (a ^ 3 * t) := by
  simp only [kl3, map_mul, map_inv₀, map_natCast, map_sum, hσ]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 a ha)) _ _ ?_
  intro u
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 a ha)) _ _ ?_
  intro v
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0]
  congr 1
  field_simp

/-- On these particular Kloosterman values, conjugation transports through
the coefficient map without assuming that the map preserves all real numbers. -/
theorem kl3_star_coefficient_covariance (σ : ℂ →+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (t : ZMod p) : σ (star (kl3 p t)) = star (kl3 p (a ^ 3 * t)) := by
  rw [kl3_star_eq_neg, kl3_coefficient_covariance p σ a ha hσ, kl3_star_eq_neg,
    mul_neg]

/-- Reindexing the shared unit variable reduces the cubic scaling of each
Kloosterman argument to a quadratic scaling of the correlation parameters. -/
theorem correlation_coefficient_covariance (σ : ℂ →+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (A B c : ZMod p) :
    σ (correlation p A B c) = correlation p (a ^ 2 * A) (a ^ 2 * B) c := by
  simp only [correlation, map_sum, map_mul,
    kl3_coefficient_covariance p σ a ha hσ,
    kl3_star_coefficient_covariance p σ a ha hσ, hσ]
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 a ha)) _ _ ?_
  intro h
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0]
  have hA : a ^ 3 * (A * (h : ZMod p)) = a ^ 2 * A * (a * (h : ZMod p)) := by ring
  have hB : a ^ 3 * (B * (h : ZMod p)) = a ^ 2 * B * (a * (h : ZMod p)) := by ring
  have hc : a * (c * (h : ZMod p)) = c * (a * (h : ZMod p)) := by ring
  rw [hA, hB, hc]

/-- Coefficient covariance of the actual zero-extended kernel. -/
theorem kernel_coefficient_covariance (σ : ℂ →+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (α m n x y : ZMod p) :
    σ (kernel p α m n x y) = kernel p (a ^ 2 * α) m n x y := by
  by_cases hxy : x = 0 ∨ y = 0
  · simp [kernel, hxy]
  · rw [kernel, ite_eq_right hxy, kernel, ite_eq_right hxy,
      correlation_coefficient_covariance p σ a ha hσ]
    congr 1 <;> ring

/-- The original conjugation pattern is preserved because all actual
kernel values are real, as proved by their finite-sum involution. -/
theorem fourCycle_coefficient_covariance (σ : ℂ →+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (α m m' n n' x y : ZMod p) :
    σ (fourCycle p α m m' n n' x y) = fourCycle p (a ^ 2 * α) m m' n n' x y := by
  simp only [fourCycle, kernel_star, map_mul,
    kernel_coefficient_covariance p σ a ha hσ]

/-- A simultaneous nonzero dilation of the common parameter and physical
coordinates leaves every actual kernel value unchanged. -/
theorem kernel_common_parameter_dilation (α m n b x y : ZMod p)
    (hm : m ≠ 0) (hn : n ≠ 0) (hb : b ≠ 0) :
    kernel p (b * α) m n (b * x) (b * y) = kernel p α m n x y := by
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  rw [kernel, ite_eq_right (not_or.mpr ⟨mul_ne_zero hb hx, mul_ne_zero hb hy⟩),
    kernel, ite_eq_right (not_or.mpr ⟨hx, hy⟩)]
  congr 1 <;> field_simp

/-- Physical covariance of the actual four-cycle before the Fourier sum. -/
theorem fourCycle_common_parameter_dilation (α m m' n n' b x y : ZMod p)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) (hb : b ≠ 0) :
    fourCycle p (b * α) m m' n n' (b * x) (b * y) =
      fourCycle p α m m' n n' x y := by
  simp only [fourCycle,
    kernel_common_parameter_dilation p α m n b x y hm hn hb,
    kernel_common_parameter_dilation p α m' n b x y hm' hn hb,
    kernel_common_parameter_dilation p α m' n' b x y hm' hn' hb,
    kernel_common_parameter_dilation p α m n' b x y hm hn' hb]

/-- Coefficient action on the Fourier sum before reindexing the two
physical variables.  The additive frequencies scale linearly here. -/
theorem fourier₂_fourCycle_coefficient_covariance_parameter
    (σ : ℂ →+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (α m m' n n' h k : ZMod p) :
    σ (fourier₂ p (fourCycle p α m m' n n') h k) =
      fourier₂ p (fourCycle p (a ^ 2 * α) m m' n n') (a * h) (a * k) := by
  simp only [fourier₂, map_sum, map_mul,
    fourCycle_coefficient_covariance p σ a ha hσ, hσ]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  ring

/-- The complete covariance identity for the original Type III transform:
the coefficient action scaling the additive character by `a` scales both
Fourier frequencies by `a³`.  There is no analytic or Fourier-bound premise. -/
theorem fourier₂_fourCycle_coefficient_covariance
    (σ : ℂ →+* ℂ) (a : ZMod p) (ha : a ≠ 0)
    (hσ : ∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t))
    (α m m' n n' h k : ZMod p)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    σ (fourier₂ p (fourCycle p α m m' n n') h k) =
      fourier₂ p (fourCycle p α m m' n n') (a ^ 3 * h) (a ^ 3 * k) := by
  rw [fourier₂_fourCycle_coefficient_covariance_parameter p σ a ha hσ]
  have hb : a ^ 2 ≠ 0 := pow_ne_zero _ ha
  have he := exact_fourier₂_scale p (fourCycle p (a ^ 2 * α) m m' n n')
    (a ^ 2) (a ^ 2) (a ^ 3 * h) (a ^ 3 * k) hb hb
  have hh : (a ^ 3 * h) / (a ^ 2) = a * h := by field_simp
  have hk : (a ^ 3 * k) / (a ^ 2) = a * k := by field_simp
  rw [hh, hk] at he
  rw [← he]
  congr 1
  funext x y
  exact fourCycle_common_parameter_dilation p α m m' n n' (a ^ 2) x y hm hm' hn hn' hb

omit [Fact p.Prime] in
/-- Every automorphism of a coefficient field embedded in `ℂ` extends to
a field automorphism of `ℂ`.  A transcendence basis is fixed and the
resulting automorphism extends across the algebraic closure. -/
theorem exists_complex_ringEquiv_extending (K : Type*) [Field K] [Algebra K ℂ]
    (τ : K ≃+* K) :
    ∃ σ : ℂ ≃+* ℂ, ∀ z : K,
      σ (algebraMap K ℂ z) = algebraMap K ℂ (τ z) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  let B := Algebra.adjoin K (Set.range (fun z : s => (z : ℂ)))
  let e : B ≃+* B :=
    hs.1.aevalEquiv.symm.toRingEquiv.trans
      ((MvPolynomial.mapEquiv s τ).trans hs.1.aevalEquiv.toRingEquiv)
  let : IsAlgClosure B ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis (fun z : s => (z : ℂ)) hs
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, ?_⟩
  intro z
  have he : e (algebraMap K B z) = algebraMap K B (τ z) := by
    simp [e, MvPolynomial.algebraMap_eq]
    exact hs.1.aevalEquiv.commutes (τ z)
  have h := IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ e (algebraMap K B z)
  simpa only [he, ← IsScalarTower.algebraMap_apply] using h

/-- The standard additive character at one is the concrete primitive root
of unity used to construct the coefficient action. -/
theorem stdAddChar_one_isPrimitiveRoot :
    IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod p)) p := by
  have he : ZMod.stdAddChar (1 : ZMod p) =
      Complex.exp (2 * Real.pi * Complex.I / p) := by
    simpa only [Int.cast_one, mul_one] using (ZMod.stdAddChar_coe (N := p) 1)
  rw [he]
  exact Complex.isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero

/-- A genuine complex field automorphism transports the standard additive
character by any nonzero residue.  The construction starts in the prime
cyclotomic field and then extends to `ℂ`; no continuity is asserted. -/
theorem exists_stdAddChar_coefficient_automorphism (a : ZMod p) (ha : a ≠ 0) :
    ∃ σ : ℂ ≃+* ℂ, ∀ t : ZMod p,
      σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t) := by
  let ζ : ℂ := ZMod.stdAddChar (1 : ZMod p)
  have hζ : IsPrimitiveRoot ζ p := stdAddChar_one_isPrimitiveRoot p
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ζ}
  have hζmem : ζ ∈ K := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
  let ζK : K := ⟨ζ, hζmem⟩
  have hζK : IsPrimitiveRoot ζK p :=
    hζ.of_map_of_injective (f := K.val) K.val.injective
  have hζint : IsAlgebraic ℚ ζ :=
    ((hζ.isIntegral (Fact.out : p.Prime).pos).tower_top (A := ℚ)).isAlgebraic
  let : IsCyclotomicExtension {p} ℚ K := by
    change IsCyclotomicExtension {p} ℚ K.toSubalgebra
    change IsCyclotomicExtension {p} ℚ
      (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζint]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hζa : IsPrimitiveRoot (ζK ^ a.val) p := by
    exact hζK.pow_of_coprime a.val
      (ZMod.val_coe_unit_coprime (Units.mk0 a ha))
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Fact.out : p.Prime).pos
  have hmin : minpoly ℚ (hζK.powerBasis ℚ).gen =
      minpoly ℚ (hζa.powerBasis ℚ).gen := by
    rw [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.powerBasis_gen]
    exact (hζK.minpoly_eq_cyclotomic_of_irreducible hirr).symm.trans
      (hζa.minpoly_eq_cyclotomic_of_irreducible hirr)
  let τ : K ≃ₐ[ℚ] K := (hζK.powerBasis ℚ).equivOfMinpoly (hζa.powerBasis ℚ) hmin
  have hτ : τ ζK = ζK ^ a.val := by
    simpa only [IsPrimitiveRoot.powerBasis_gen] using
      PowerBasis.equivOfMinpoly_gen (hζK.powerBasis ℚ) (hζa.powerBasis ℚ) hmin
  obtain ⟨σ, hσ⟩ := exists_complex_ringEquiv_extending K τ.toRingEquiv
  have hσζ : σ ζ = ζ ^ a.val := by
    have h := hσ ζK
    simpa only [AlgEquiv.coe_ringEquiv, hτ,
      map_pow, IntermediateField.algebraMap_apply, ζK] using h
  have hchar (t : ZMod p) : ZMod.stdAddChar t = ζ ^ t.val := by
    have h := (ZMod.stdAddChar (N := p)).map_nsmul_eq_pow t.val (1 : ZMod p)
    simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one] using h
  refine ⟨σ, fun t => ?_⟩
  rw [hchar t, map_pow, hσζ, ← hchar a, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

/-- The coefficient automorphism is chosen before all of the row, column,
physical, and Fourier parameters.  Its cubic covariance is an unconditional
identity of the actual arithmetic transforms. -/
theorem exists_fourCycle_fourier_coefficient_automorphism (a : ZMod p) (ha : a ≠ 0) :
    ∃ σ : ℂ ≃+* ℂ,
      (∀ t : ZMod p, σ (ZMod.stdAddChar t) = ZMod.stdAddChar (a * t)) ∧
      ∀ α m m' n n' h k : ZMod p,
        m ≠ 0 → m' ≠ 0 → n ≠ 0 → n' ≠ 0 →
        σ (fourier₂ p (fourCycle p α m m' n n') h k) =
          fourier₂ p (fourCycle p α m m' n n') (a ^ 3 * h) (a ^ 3 * k) := by
  obtain ⟨σ, hσ⟩ := exists_stdAddChar_coefficient_automorphism p a ha
  refine ⟨σ, hσ, ?_⟩
  intro α m m' n n' h k hm hm' hn hn'
  exact fourier₂_fourCycle_coefficient_covariance p σ.toRingHom a ha hσ
    α m m' n n' h k hm hm' hn hn'

/-- Vanishing of the actual Fourier value is invariant under cubic
frequency dilation.  This is a statement about values, not geometric
exceptional supports or their dimensions. -/
theorem fourCycle_fourier_zero_iff_cubic_dilation (a : ZMod p) (ha : a ≠ 0)
    (α m m' n n' h k : ZMod p)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourier₂ p (fourCycle p α m m' n n') h k = 0 ↔
      fourier₂ p (fourCycle p α m m' n n') (a ^ 3 * h) (a ^ 3 * k) = 0 := by
  obtain ⟨σ, _, hσ⟩ := exists_fourCycle_fourier_coefficient_automorphism p a ha
  rw [← hσ α m m' n n' h k hm hm' hn hn']
  constructor
  · intro hzero
    simp only [hzero, map_zero]
  · intro hzero
    exact σ.injective (by simpa only [map_zero] using hzero)

#print axioms kl3_coefficient_covariance
#print axioms kl3_star_coefficient_covariance
#print axioms correlation_coefficient_covariance
#print axioms kernel_coefficient_covariance
#print axioms fourCycle_coefficient_covariance
#print axioms kernel_common_parameter_dilation
#print axioms fourCycle_common_parameter_dilation
#print axioms fourier₂_fourCycle_coefficient_covariance_parameter
#print axioms fourier₂_fourCycle_coefficient_covariance
#print axioms exists_complex_ringEquiv_extending
#print axioms stdAddChar_one_isPrimitiveRoot
#print axioms exists_stdAddChar_coefficient_automorphism
#print axioms exists_fourCycle_fourier_coefficient_automorphism
#print axioms fourCycle_fourier_zero_iff_cubic_dilation

end

end PrimeGap182.TypeIII
