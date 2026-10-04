import TypeIIITwoAdicCoefficientField

/-!
# Continuous root-squaring action on the standard algebraic closure of Q₂

Continuity and rational density show that the local action fixes Q₂.
Transport through the algebraic Q₂-isomorphism then gives an automorphism
of the standard algebraic closure. Norm uniqueness proves that this action
is an isometry in the standard spectral norm; no continuity of the chosen
algebraic-closure equivalence is assumed.
-/

noncomputable section
open scoped Topology PrimeGap182.TypeIII.TwoAdicCoefficientField

namespace PrimeGap182.TypeIII.StandardTwoAdicAction

open NumberField IsDedekindDomain LocalCyclotomicCoefficient TwoAdicCoefficientField

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  [v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})]
  (p : ℕ) [Fact p.Prime] (hp : 3 < p) [IsCyclotomicExtension {p} ℚ K]

theorem localFrobenius_padic (x : ℚ_[2]) :
    localFrobenius K v p hp (padicEmbedding K v x) = padicEmbedding K v x := by
  induction x using isClosed_property (Padic.denseRange_ratCast 2)
  · exact isClosed_eq ((localFrobenius_continuous K v p hp).comp
      (padicEmbedding_continuous K v)) (padicEmbedding_continuous K v)
  · rename_i q
    rw [padicEmbedding_rat, localFrobenius_on_numberField,
      (CyclotomicFrobenius.frobenius p hp K).commutes]

/-- The constructed coefficient action fixes the entire two-adic base. -/
def coefficientFrobenius : ClosedCyclotomicCoefficient.Coeff K v ≃ₐ[ℚ_[2]]
    ClosedCyclotomicCoefficient.Coeff K v where
  __ := ClosedCyclotomicCoefficient.frobenius K v p hp
  commutes' x := by
    change ClosedCyclotomicCoefficient.frobenius K v p hp
      (algebraMap (LocalField K v) (ClosedCyclotomicCoefficient.Coeff K v)
        (padicEmbedding K v x)) = _
    rw [ClosedCyclotomicCoefficient.frobenius_on_local, localFrobenius_padic]
    rfl

/-- The actual Q₂-linear automorphism on Mathlib's standard algebraic closure. -/
def frobenius : PadicAlgCl 2 ≃ₐ[ℚ_[2]] PadicAlgCl 2 :=
  (coefficientEquiv K v).symm.trans
    ((coefficientFrobenius K v p hp).trans (coefficientEquiv K v))

theorem frobenius_isometry : Isometry (frobenius K v p hp) :=
  AlgebraicCoefficientAutomorphism.isometry (RingEquiv.refl ℚ_[2]) (fun _ => rfl)
    (frobenius K v p hp).toRingEquiv (fun x => (frobenius K v p hp).commutes x)

theorem frobenius_continuous : Continuous (frobenius K v p hp) :=
  (frobenius_isometry K v p hp).continuous

theorem frobenius_symm_continuous : Continuous (frobenius K v p hp).symm :=
  (AlgebraicCoefficientAutomorphism.isometry (RingEquiv.refl ℚ_[2]) (fun _ => rfl)
    (frobenius K v p hp).symm.toRingEquiv (fun x => (frobenius K v p hp).symm.commutes x)).continuous

theorem frobenius_root (ζ : PadicAlgCl 2) (hζ : ζ ^ p = 1) :
    frobenius K v p hp ζ = ζ ^ 2 := by
  have h := ClosedCyclotomicCoefficient.frobenius_root K v p hp
    ((coefficientEquiv K v).symm ζ) (by rw [← map_pow, hζ, map_one])
  change coefficientEquiv K v
    (ClosedCyclotomicCoefficient.frobenius K v p hp ((coefficientEquiv K v).symm ζ)) = _
  rw [h, map_pow, AlgEquiv.apply_symm_apply]

/-- For every prime greater than three, the required continuous root
action exists on the standard algebraic closure of Q₂ and fixes Q₂. -/
theorem exists_continuous_action (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ τ : PadicAlgCl 2 ≃ₐ[ℚ_[2]] PadicAlgCl 2,
      Isometry τ ∧ Continuous τ ∧ Continuous τ.symm ∧
        ∀ ζ : PadicAlgCl 2, ζ ^ p = 1 → τ ζ = ζ ^ 2 := by
  let : NeZero p := ⟨by omega⟩
  let : NeZero (p : ℚ) := ⟨by exact_mod_cast (NeZero.ne p)⟩
  let : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨v, hv⟩ := exists_place_above_two (CyclotomicField p ℚ)
  let : v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := hv
  exact ⟨frobenius (CyclotomicField p ℚ) v p hp,
    frobenius_isometry (CyclotomicField p ℚ) v p hp,
    frobenius_continuous (CyclotomicField p ℚ) v p hp,
    frobenius_symm_continuous (CyclotomicField p ℚ) v p hp,
    frobenius_root (CyclotomicField p ℚ) v p hp⟩

end PrimeGap182.TypeIII.StandardTwoAdicAction

#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.localFrobenius_padic
#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.coefficientFrobenius
#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.frobenius
#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.frobenius_isometry
#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.frobenius_continuous
#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.frobenius_symm_continuous
#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.frobenius_root
#print axioms PrimeGap182.TypeIII.StandardTwoAdicAction.exists_continuous_action
