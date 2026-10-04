import TypeIIITwoAdicComplexEmbedding
import TypeIIICoefficientTraceTransport

/-!
# Constructed coefficients for the Type III source application

Fix one complex embedding of the standard two-adic algebraic closure.
For each prime p > 3, choose the proved continuous root-squaring action.
The exact standard-character root and complex action are then derived.
Only the general coefficient-valued sheaf transport laws remain supplied.
-/

noncomputable section
open scoped Topology PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.CanonicalCoefficients

open TwoAdicComplexEmbedding

variable (p : ℕ) [Fact p.Prime] (hp : 3 < p)

def tau : PadicAlgCl 2 ≃ₐ[ℚ_[2]] PadicAlgCl 2 :=
  (StandardTwoAdicAction.exists_continuous_action p hp).choose

theorem tau_isometry : Isometry (tau p hp) :=
  (StandardTwoAdicAction.exists_continuous_action p hp).choose_spec.1

theorem tau_continuous : Continuous (tau p hp) :=
  (StandardTwoAdicAction.exists_continuous_action p hp).choose_spec.2.1

theorem tau_symm_continuous : Continuous (tau p hp).symm :=
  (StandardTwoAdicAction.exists_continuous_action p hp).choose_spec.2.2.1

theorem tau_root (ζ : PadicAlgCl 2) (hζ : ζ ^ p = 1) : tau p hp ζ = ζ ^ 2 :=
  (StandardTwoAdicAction.exists_continuous_action p hp).choose_spec.2.2.2 ζ hζ

def zeta : PadicAlgCl 2 := complexEquiv.symm (ZMod.stdAddChar (1 : ZMod p))

theorem zeta_complex : algebraMap (PadicAlgCl 2) ℂ (zeta p) =
    ZMod.stdAddChar (1 : ZMod p) :=
  complexEquiv.apply_symm_apply _

theorem tau_zeta : tau p hp (zeta p) = zeta p ^ 2 := by
  apply tau_root p hp
  change (complexEquiv.symm (ZMod.stdAddChar (1 : ZMod p))) ^ p = 1
  rw [← map_pow, (CoefficientAutomorphism.stdAddChar_one_primitive p).pow_eq_one, map_one]

def sigma : ℂ ≃+* ℂ :=
  CoefficientAutomorphism.extension (PadicAlgCl 2) ℂ (tau p hp).toRingEquiv

theorem sigma_on_coefficients (x : PadicAlgCl 2) :
    sigma p hp (algebraMap (PadicAlgCl 2) ℂ x) =
      algebraMap (PadicAlgCl 2) ℂ (tau p hp x) :=
  CoefficientAutomorphism.extension_spec (PadicAlgCl 2) ℂ (tau p hp).toRingEquiv x

theorem sigma_stdAddChar (t : ZMod p) :
    sigma p hp (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t) :=
  CoefficientAutomorphism.extension_doubling_spec p (PadicAlgCl 2)
    (tau p hp).toRingEquiv (zeta p) (zeta_complex p) (tau_zeta p hp) t

open PublishedSupportRules PublishedFourierRules PublishedStalkSupport PublishedCovarianceRules

def chebotarev {Obj : Type*}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    {realization : RationalStalkRealization p D} {T : CoefficientTransport D}
    (G : TraceData p realization)
    (R : CoefficientTraceTransport.Rules (T := T) G (tau p hp).toRingEquiv) :
    ChebotarevRules (T := T) G (sigma p hp) := R.toChebotarev

end PrimeGap182.TypeIII.CanonicalCoefficients

#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.tau
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.tau_isometry
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.tau_continuous
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.tau_symm_continuous
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.tau_root
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.zeta
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.zeta_complex
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.tau_zeta
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.sigma
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.sigma_on_coefficients
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.sigma_stdAddChar
#print axioms PrimeGap182.TypeIII.CanonicalCoefficients.chebotarev
