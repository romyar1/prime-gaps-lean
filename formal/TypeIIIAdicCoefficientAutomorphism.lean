import TypeIIICoefficientAutomorphism
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Topology.Algebra.UniformRing

/-!
# Continuous extension of prime-preserving coefficient automorphisms

Fixing a prime ideal preserves its ideal-power filtration, hence the exact
adic valuation on the Dedekind domain and its fraction field. A
valuation-preserving field automorphism extends continuously to the same
completed valued field. No continuity premise is supplied to that extension.
-/

noncomputable section
open scoped Pointwise Topology

namespace PrimeGap182.TypeIII.AdicCoefficientAutomorphism

open IsDedekindDomain

variable {G R : Type*} [Group G] [CommRing R] [IsDedekindDomain R]
  [MulSemiringAction G R]

theorem intValuation_smul (v : HeightOneSpectrum R) (g : G)
    (hg : g • v.asIdeal = v.asIdeal) (r : R) :
    v.intValuation (g • r) = v.intValuation r := by
  have hpow (n : ℕ) : g • v.asIdeal ^ n = v.asIdeal ^ n := by rw [smul_pow', hg]
  have hle (n : ℕ) : v.intValuation (g • r) ≤ WithZero.exp (-(n : ℤ)) ↔
      v.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
    rw [v.intValuation_le_pow_iff_mem, v.intValuation_le_pow_iff_mem]
    conv_lhs => rw [← hpow n]
    exact Ideal.smul_mem_pointwise_smul_iff
  by_cases hr : r = 0
  · simp [hr]
  have hgr : g • r ≠ 0 := (smul_ne_zero_iff_ne g).mpr hr
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v.intValuation r = WithZero.exp (-(n : ℤ)) :=
    ⟨_, v.intValuation_if_neg hr⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, v.intValuation (g • r) = WithZero.exp (-(m : ℤ)) :=
    ⟨_, v.intValuation_if_neg hgr⟩
  apply le_antisymm
  · rw [hn]
    exact (hle n).mpr hn.le
  · rw [hm]
    exact (hle m).mp hm.le

theorem valuation_smul {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    [MulSemiringAction G K] (v : HeightOneSpectrum R) (g : G)
    (hg : g • v.asIdeal = v.asIdeal)
    (hc : ∀ r : R, algebraMap R K (g • r) = g • algebraMap R K r) (x : K) :
    v.valuation K (g • x) = v.valuation K x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
  rw [smul_div₀', ← hc a, ← hc b, map_div₀, map_div₀,
    v.valuation_of_algebraMap, v.valuation_of_algebraMap,
    v.valuation_of_algebraMap, v.valuation_of_algebraMap,
    intValuation_smul v g hg, intValuation_smul v g hg]

section Completion

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- Equality of valuations supplies continuity, including on the full
value-group neighborhood basis used by the valued-field topology. -/
theorem continuous_of_valuation_eq [Valued K Γ] (e : K ≃+* K)
    (he : ∀ x : K, Valued.v (e x) = Valued.v x) : Continuous e := by
  apply (uniformContinuous_of_continuousAt_zero e.toRingHom ?_).continuous
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  refine ⟨γ, ?_⟩
  intro x hx
  change Valued.v.restrict (e x) < γ.val
  rw [(Valuation.restrict_inj Valued.v).mpr (he x)]
  exact hx

theorem withVal_continuous (v : Valuation K Γ) (e : K ≃+* K)
    (he : ∀ x : K, v (e x) = v x) : Continuous (WithVal.congr v v e) := by
  apply continuous_of_valuation_eq (WithVal.congr v v e)
  intro x
  exact he x.ofVal

/-- Extend both directions of the same valuation-preserving automorphism
to the completion. -/
def completionEquiv (v : Valuation K Γ) (e : K ≃+* K)
    (he : ∀ x : K, v (e x) = v x) :
    UniformSpace.Completion (WithVal v) ≃+* UniformSpace.Completion (WithVal v) :=
  UniformSpace.Completion.mapRingEquiv (WithVal.congr v v e)
    (withVal_continuous v e he)
    (withVal_continuous v e.symm (fun x => by simpa using (he (e.symm x)).symm))

theorem completionEquiv_coe (v : Valuation K Γ) (e : K ≃+* K)
    (he : ∀ x : K, v (e x) = v x) (x : WithVal v) :
    completionEquiv v e he x =
      (WithVal.congr v v e x : UniformSpace.Completion (WithVal v)) := by
  exact UniformSpace.Completion.mapRingHom_coe (withVal_continuous v e he) x

theorem completionEquiv_continuous (v : Valuation K Γ) (e : K ≃+* K)
    (he : ∀ x : K, v (e x) = v x) : Continuous (completionEquiv v e he) :=
  UniformSpace.Completion.continuous_map

theorem completionEquiv_symm_continuous (v : Valuation K Γ) (e : K ≃+* K)
    (he : ∀ x : K, v (e x) = v x) : Continuous (completionEquiv v e he).symm :=
  UniformSpace.Completion.continuous_map

end Completion

end PrimeGap182.TypeIII.AdicCoefficientAutomorphism

#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.intValuation_smul
#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.valuation_smul
#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.continuous_of_valuation_eq
#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.withVal_continuous
#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.completionEquiv
#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.completionEquiv_coe
#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.completionEquiv_continuous
#print axioms PrimeGap182.TypeIII.AdicCoefficientAutomorphism.completionEquiv_symm_continuous
