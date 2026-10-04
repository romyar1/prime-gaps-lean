import TypeIIICyclotomicFrobenius
import TypeIIIAdicCoefficientAutomorphism
import TypeIIICoefficientTraceTransport
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The completed cyclotomic coefficient field at two

Construct the continuous root-squaring action on the completion of a
rational cyclotomic field at a prime above two. A complex coefficient
embedding then supplies a compatible standard-character root and the
complex action used by the existing trace-transport constructor.
-/

noncomputable section
open scoped Pointwise Topology

namespace PrimeGap182.TypeIII.LocalCyclotomicCoefficient

open NumberField IsDedekindDomain CyclotomicFrobenius AdicCoefficientAutomorphism

variable (K : Type*) [Field K] [NumberField K]

theorem exists_place_above_two :
    ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : (Ideal.span {(2 : ℤ)}).IsMaximal := by
    simpa using (Int.ideal_span_isMaximal_of_prime 2)
  obtain ⟨P, hP, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (Ideal.span {(2 : ℤ)}) (S := 𝓞 K)
  let : P.IsMaximal := hP
  let : P.LiesOver (Ideal.span {(2 : ℤ)}) := hOver
  exact ⟨⟨P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(2 : ℤ)}) (by simp) P⟩, hOver⟩

variable (v : HeightOneSpectrum (𝓞 K))

/-- The actual valued completion at the selected prime. -/
abbrev LocalField := UniformSpace.Completion (WithVal (v.valuation K))

def embedding : K →+* LocalField K v :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm.toRingHom

variable (p : ℕ) [Fact p.Prime] (hp : 3 < p) [IsCyclotomicExtension {p} ℚ K]
  [v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})]

theorem valuation_frobenius (x : K) :
    v.valuation K (frobenius p hp K x) = v.valuation K x :=
  valuation_smul v (frobenius p hp K) (frobenius_fixes_prime p hp K v.asIdeal)
    (fun _ => rfl) x

/-- The same cyclotomic Galois action, extended in both directions to
the selected 2-adic completion. -/
def localFrobenius : LocalField K v ≃+* LocalField K v :=
  completionEquiv (v.valuation K) (frobenius p hp K).toRingEquiv
    (valuation_frobenius K v p hp)

theorem localFrobenius_continuous : Continuous (localFrobenius K v p hp) :=
  completionEquiv_continuous (v.valuation K) (frobenius p hp K).toRingEquiv
    (valuation_frobenius K v p hp)

theorem localFrobenius_symm_continuous : Continuous (localFrobenius K v p hp).symm :=
  completionEquiv_symm_continuous (v.valuation K) (frobenius p hp K).toRingEquiv
    (valuation_frobenius K v p hp)

theorem localFrobenius_on_numberField (x : K) :
    localFrobenius K v p hp (embedding K v x) = embedding K v (frobenius p hp K x) :=
  completionEquiv_coe (v.valuation K) (frobenius p hp K).toRingEquiv
    (valuation_frobenius K v p hp) ((WithVal.equiv (v.valuation K)).symm x)

theorem localFrobenius_root (ζ : K) (hζ : ζ ^ p = 1) :
    localFrobenius K v p hp (embedding K v ζ) = (embedding K v ζ) ^ 2 := by
  rw [localFrobenius_on_numberField, frobenius_root p hp K ζ hζ, map_pow]

variable [Algebra (LocalField K v) ℂ]

/-- For the supplied complex embedding, choose a power of the cyclotomic
root mapping to the exact standard character, retaining the local action. -/
theorem exists_compatible_root : ∃ ζ : LocalField K v,
    algebraMap (LocalField K v) ℂ ζ = ZMod.stdAddChar (1 : ZMod p) ∧
      localFrobenius K v p hp ζ = ζ ^ 2 := by
  let z := IsCyclotomicExtension.zeta p ℚ K
  have hz : IsPrimitiveRoot z p := IsCyclotomicExtension.zeta_spec p ℚ K
  have hL := hz.map_of_injective (embedding K v).injective
  have hC := hL.map_of_injective (algebraMap (LocalField K v) ℂ).injective
  obtain ⟨n, _, hn⟩ := hC.eq_pow_of_pow_eq_one
    (CoefficientAutomorphism.stdAddChar_one_primitive p).pow_eq_one
  refine ⟨(embedding K v z) ^ n, ?_, ?_⟩
  · simpa only [map_pow] using hn
  · rw [map_pow, localFrobenius_root K v p hp z hz.pow_eq_one, pow_right_comm]

def complexFrobenius : ℂ ≃+* ℂ :=
  CoefficientAutomorphism.extension (LocalField K v) ℂ (localFrobenius K v p hp)

theorem complexFrobenius_stdAddChar (t : ZMod p) :
    complexFrobenius K v p hp (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t) := by
  obtain ⟨ζ, hζ, hτ⟩ := exists_compatible_root K v p hp
  exact CoefficientAutomorphism.extension_doubling_spec p (LocalField K v)
    (localFrobenius K v p hp) ζ hζ hτ t

open PublishedSupportRules PublishedFourierRules PublishedStalkSupport PublishedCovarianceRules

/-- Insert the constructed local action into the existing generic trace
transport. The coefficient-valued sheaf laws remain explicit. -/
def complexChebotarev {Obj : Type*}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    {realization : RationalStalkRealization p D} {T : CoefficientTransport D}
    (G : TraceData p realization)
    (R : CoefficientTraceTransport.Rules (T := T) G (localFrobenius K v p hp)) :
    ChebotarevRules (T := T) G (complexFrobenius K v p hp) :=
  R.toChebotarev

/-- A concrete cyclotomic field and a prime above two exist, and their
completion has a continuous automorphism with continuous inverse that
squares every embedded p-th root. No local-action assumption is used. -/
theorem exists_continuous_action (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ v : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
      v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) ∧
      ∃ τ : LocalField (CyclotomicField p ℚ) v ≃+* LocalField (CyclotomicField p ℚ) v,
        Continuous τ ∧ Continuous τ.symm ∧
        ∀ ζ : CyclotomicField p ℚ, ζ ^ p = 1 →
          τ (embedding (CyclotomicField p ℚ) v ζ) =
            (embedding (CyclotomicField p ℚ) v ζ) ^ 2 := by
  let : NeZero p := ⟨by omega⟩
  let : NeZero (p : ℚ) := ⟨by exact_mod_cast (NeZero.ne p)⟩
  let : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨v, hv⟩ := exists_place_above_two (CyclotomicField p ℚ)
  let : v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := hv
  exact ⟨v, hv, localFrobenius (CyclotomicField p ℚ) v p hp,
    localFrobenius_continuous (CyclotomicField p ℚ) v p hp,
    localFrobenius_symm_continuous (CyclotomicField p ℚ) v p hp,
    localFrobenius_root (CyclotomicField p ℚ) v p hp⟩

end PrimeGap182.TypeIII.LocalCyclotomicCoefficient

#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.exists_place_above_two
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.embedding
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.valuation_frobenius
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.localFrobenius
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.localFrobenius_continuous
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.localFrobenius_symm_continuous
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.localFrobenius_on_numberField
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.localFrobenius_root
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.exists_compatible_root
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.complexFrobenius
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.complexFrobenius_stdAddChar
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.complexChebotarev
#print axioms PrimeGap182.TypeIII.LocalCyclotomicCoefficient.exists_continuous_action
