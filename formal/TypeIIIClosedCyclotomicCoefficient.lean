import TypeIIILocalCyclotomicCoefficient
import TypeIIIAlgebraicCoefficientAutomorphism

/-!
# An algebraically closed cyclotomic coefficient model

Extend the actual continuous local cyclotomic action to the algebraic
closure with its spectral norm. Norm uniqueness gives continuity in both
directions, and the action squares every p-th root in the closure.
The compatible geometric sheaf realization remains separate.
-/

noncomputable section
open scoped Topology Valued NNReal WithZero

namespace PrimeGap182.TypeIII.ClosedCyclotomicCoefficient

open NumberField IsDedekindDomain LocalCyclotomicCoefficient

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem embedding_valuation (x : K) :
    (Valued.v (LocalCyclotomicCoefficient.embedding K v x) : WithZero (Multiplicative ℤ)) =
      v.valuation K x :=
  Valued.valuedCompletion_apply ((WithVal.equiv (v.valuation K)).symm x)

instance localRankOne :
    (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ))).RankOne where
  hom' := (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono
    (HeightOneSpectrum.one_lt_absNorm_nnreal v)).comp
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    obtain ⟨x, hx0, hx1⟩ := Valuation.RankOne.nontrivial (v.valuation K)
    exact ⟨LocalCyclotomicCoefficient.embedding K v x,
      by rwa [embedding_valuation], by rwa [embedding_valuation]⟩

instance localNormedField : NontriviallyNormedField (LocalField K v) :=
  Valued.toNontriviallyNormedField (LocalField K v) (WithZero (Multiplicative ℤ))

/-- A fixed algebraic closure of the completed coefficient field. -/
def Coeff := AlgebraicClosure (LocalField K v)

instance coeffField : Field (Coeff K v) :=
  inferInstanceAs (Field (AlgebraicClosure (LocalField K v)))

instance coeffAlgebra : Algebra (LocalField K v) (Coeff K v) :=
  inferInstanceAs (Algebra (LocalField K v) (AlgebraicClosure (LocalField K v)))

instance coeffIsAlgebraic : Algebra.IsAlgebraic (LocalField K v) (Coeff K v) :=
  inferInstanceAs (Algebra.IsAlgebraic (LocalField K v) (AlgebraicClosure (LocalField K v)))

instance coeffIsAlgClosed : IsAlgClosed (Coeff K v) :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure (LocalField K v)))

instance coeffNormedField : NontriviallyNormedField (Coeff K v) :=
  spectralNorm.nontriviallyNormedField (LocalField K v) (Coeff K v)

instance coeffNormedAlgebra : NormedAlgebra (LocalField K v) (Coeff K v) :=
  spectralNorm.normedAlgebra (LocalField K v) (Coeff K v)

instance coeffUltrametric : IsUltrametricDist (Coeff K v) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K := LocalField K v) (L := Coeff K v))

/-- The number-field embedding followed by the actual algebraic-closure embedding. -/
def embedding : K →+* Coeff K v :=
  (algebraMap (LocalField K v) (Coeff K v)).comp (LocalCyclotomicCoefficient.embedding K v)

variable (p : ℕ) [Fact p.Prime] (hp : 3 < p) [IsCyclotomicExtension {p} ℚ K]
  [v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})]

/-- Valuation preservation on the dense number field determines the norm
of the continuous local action everywhere on its completion. -/
theorem localFrobenius_norm (x : LocalField K v) :
    ‖localFrobenius K v p hp x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (localFrobenius_continuous K v p hp)) continuous_norm) ?_
  intro y
  change ‖localFrobenius K v p hp (LocalCyclotomicCoefficient.embedding K v y.ofVal)‖ =
    ‖LocalCyclotomicCoefficient.embedding K v y.ofVal‖
  rw [localFrobenius_on_numberField]
  change ((Valuation.RankOne.hom _) (Valued.v.restrict
    (LocalCyclotomicCoefficient.embedding K v (CyclotomicFrobenius.frobenius p hp K y.ofVal))) : ℝ) =
      ((Valuation.RankOne.hom _) (Valued.v.restrict
        (LocalCyclotomicCoefficient.embedding K v y.ofVal)) : ℝ)
  apply congrArg (fun r => ((Valuation.RankOne.hom
    (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ)))) r : ℝ))
  apply (Valuation.restrict_inj _).mpr
  rw [embedding_valuation, embedding_valuation, valuation_frobenius K v p hp]

/-- Extend the same local action, preserving every local coefficient. -/
def frobenius : Coeff K v ≃+* Coeff K v :=
  CoefficientAutomorphism.extension (LocalField K v) (Coeff K v) (localFrobenius K v p hp)

theorem frobenius_on_local (x : LocalField K v) :
    frobenius K v p hp (algebraMap (LocalField K v) (Coeff K v) x) =
      algebraMap (LocalField K v) (Coeff K v) (localFrobenius K v p hp x) :=
  CoefficientAutomorphism.extension_spec (LocalField K v) (Coeff K v) _ x

theorem frobenius_isometry : Isometry (frobenius K v p hp) :=
  AlgebraicCoefficientAutomorphism.extension_isometry _ (localFrobenius_norm K v p hp)

theorem frobenius_continuous : Continuous (frobenius K v p hp) :=
  (frobenius_isometry K v p hp).continuous

theorem frobenius_symm_continuous : Continuous (frobenius K v p hp).symm :=
  AlgebraicCoefficientAutomorphism.extension_symm_continuous _ (localFrobenius_norm K v p hp)

theorem frobenius_on_numberField (x : K) :
    frobenius K v p hp (embedding K v x) =
      embedding K v (CyclotomicFrobenius.frobenius p hp K x) := by
  exact (frobenius_on_local K v p hp (LocalCyclotomicCoefficient.embedding K v x)).trans
    (congrArg (algebraMap (LocalField K v) (Coeff K v))
      (localFrobenius_on_numberField K v p hp x))

/-- All roots of order dividing p, including roots presented directly in
the algebraic closure, are powers of the embedded cyclotomic root. -/
theorem frobenius_root (ζ : Coeff K v) (hζ : ζ ^ p = 1) :
    frobenius K v p hp ζ = ζ ^ 2 := by
  let z := IsCyclotomicExtension.zeta p ℚ K
  have hz : IsPrimitiveRoot z p := IsCyclotomicExtension.zeta_spec p ℚ K
  have hC := hz.map_of_injective (embedding K v).injective
  obtain ⟨n, _, hn⟩ := hC.eq_pow_of_pow_eq_one hζ
  rw [← hn, map_pow, frobenius_on_numberField,
    CyclotomicFrobenius.frobenius_root p hp K z hz.pow_eq_one, map_pow, pow_right_comm]

variable [Algebra (Coeff K v) ℂ]

theorem exists_compatible_root : ∃ ζ : Coeff K v,
    algebraMap (Coeff K v) ℂ ζ = ZMod.stdAddChar (1 : ZMod p) ∧
      frobenius K v p hp ζ = ζ ^ 2 := by
  let z := IsCyclotomicExtension.zeta p ℚ K
  have hz : IsPrimitiveRoot z p := IsCyclotomicExtension.zeta_spec p ℚ K
  have hC := (hz.map_of_injective (embedding K v).injective).map_of_injective
    (algebraMap (Coeff K v) ℂ).injective
  obtain ⟨n, _, hn⟩ := hC.eq_pow_of_pow_eq_one
    (CoefficientAutomorphism.stdAddChar_one_primitive p).pow_eq_one
  refine ⟨(embedding K v z) ^ n, ?_, frobenius_root K v p hp _ ?_⟩
  · simpa only [map_pow] using hn
  · rw [pow_right_comm, ← map_pow, hz.pow_eq_one, map_one, one_pow]

def complexFrobenius : ℂ ≃+* ℂ :=
  CoefficientAutomorphism.extension (Coeff K v) ℂ (frobenius K v p hp)

theorem complexFrobenius_stdAddChar (t : ZMod p) :
    complexFrobenius K v p hp (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t) := by
  obtain ⟨ζ, hζ, hτ⟩ := exists_compatible_root K v p hp
  exact CoefficientAutomorphism.extension_doubling_spec p (Coeff K v)
    (frobenius K v p hp) ζ hζ hτ t

open PublishedSupportRules PublishedFourierRules PublishedStalkSupport PublishedCovarianceRules

/-- The complex trace-transport record for this actual continuous
coefficient action, from the general coefficient-valued sheaf laws. -/
def complexChebotarev {Obj : Type*}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    {realization : RationalStalkRealization p D} {T : CoefficientTransport D}
    (G : TraceData p realization)
    (R : CoefficientTraceTransport.Rules (T := T) G (frobenius K v p hp)) :
    ChebotarevRules (T := T) G (complexFrobenius K v p hp) :=
  R.toChebotarev

/-- A concrete algebraically closed valued coefficient model and its
continuous root-squaring action exist for every prime greater than three. -/
theorem exists_continuous_action (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ v : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
      v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) ∧
      ∃ τ : Coeff (CyclotomicField p ℚ) v ≃+* Coeff (CyclotomicField p ℚ) v,
        Isometry τ ∧ Continuous τ ∧ Continuous τ.symm ∧
        ∀ ζ : Coeff (CyclotomicField p ℚ) v, ζ ^ p = 1 → τ ζ = ζ ^ 2 := by
  let : NeZero p := ⟨by omega⟩
  let : NeZero (p : ℚ) := ⟨by exact_mod_cast (NeZero.ne p)⟩
  let : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨v, hv⟩ := exists_place_above_two (CyclotomicField p ℚ)
  let : v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := hv
  exact ⟨v, hv, frobenius (CyclotomicField p ℚ) v p hp,
    frobenius_isometry (CyclotomicField p ℚ) v p hp,
    frobenius_continuous (CyclotomicField p ℚ) v p hp,
    frobenius_symm_continuous (CyclotomicField p ℚ) v p hp,
    frobenius_root (CyclotomicField p ℚ) v p hp⟩

end PrimeGap182.TypeIII.ClosedCyclotomicCoefficient

#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.embedding_valuation
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.localRankOne
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.localNormedField
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.coeffNormedField
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.coeffIsAlgClosed
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.coeffUltrametric
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.localFrobenius_norm
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.frobenius
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.frobenius_on_local
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.frobenius_isometry
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.frobenius_continuous
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.frobenius_symm_continuous
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.frobenius_on_numberField
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.frobenius_root
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.exists_compatible_root
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.complexFrobenius
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.complexFrobenius_stdAddChar
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.complexChebotarev
#print axioms PrimeGap182.TypeIII.ClosedCyclotomicCoefficient.exists_continuous_action
