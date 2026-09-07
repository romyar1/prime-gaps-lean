import TypeIIIPublishedFourierRules
import TypeIIICorrectedTraceCovariance

/-!
# Coefficient dilation from all-extension traces and generic Fourier laws

The Chebotarev premise below concerns geometrically semisimple intermediate
extensions of lisse sheaves on the torus. Its conclusion is GEOMETRIC
isomorphism. Equality of traces does not identify an arbitrary arithmetic
extension. All finite extensions and all torus points occur in the premise.

Traces are attached to chosen Weil lifts of geometric objects, using the
same lifts as the rational stalk spectra. No Frobenius structure is assigned
to geometric constituents that do not descend to the prime field.
The trace of the actual family remains separate construction data. Once
identified with the literal signed corrected sums, its covariance is proved
by finite-sum algebra. Generic coefficient transport, Chebotarev and Fourier
linear-map compatibility then imply the geometric dilation by eight.

The intended coefficient functor comes from the continuous automorphism of
Q_2(zeta_p) sending zeta_p to zeta_p^2, and `sigma` represents its action
through a compatible complex embedding. The trace-transport law explicitly
records this compatibility. No norm-preservation assertion is used.

Primary inputs: Chebotarev and Brauer--Nesbitt for lisse sheaves; Deligne,
Weil II, Theorem 3.4.1(iii), for geometric semisimplicity of pure lisse
sheaves; BBD intermediate-extension uniqueness; Laumon, Theorem 1.2.2.4,
for Fourier compatibility with linear maps. All are hypotheses, not axioms.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.PublishedCovarianceRules

open PublishedSupportRules PublishedFourierRules

universe v w

variable (p : ℕ) [Fact p.Prime]

/-- The actual coefficient inclusion on dilation units. -/
def geometricUnit (a : (ZMod p)ˣ) : (AlgebraicClosure (ZMod p))ˣ :=
  Units.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).toMonoidHom a

@[simp] theorem geometricUnit_val (a : (ZMod p)ˣ) :
    (geometricUnit p a : AlgebraicClosure (ZMod p)) =
      algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) (a : ZMod p) := rfl

/-- Traces of a chosen Weil lift at points of every finite extension.
The prime-field trace is the trace of the same lift's rational spectra.
`TorusIC` is geometric and includes
geometric semisimplicity of the lisse restriction and intermediate extension
from the whole torus. This predicate is not assigned to any family here. -/
structure TraceData {Obj : Type v}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    (realization : RationalStalkRealization p D) where
  trace : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    {P : Obj} → realization.WeilLift P → L → L → ℂ
  prime_trace : ∀ {P} (W : realization.WeilLift P) x y,
    trace (ZMod p) W x y = (realization.stalk W x y).trace
  TorusIC : Obj → Prop

variable {p} {Obj : Type v} {CurveObj : Type w}
  {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : RationalStalkRealization p D}
  {T : CoefficientTransport D} {F : FourierData (AlgebraicClosure (ZMod p)) Obj CurveObj}

/-- General coefficient operations on arithmetic lifts, their trace laws,
and the geometric consequence of Chebotarev on the torus. The isomorphism
relation in `T` is geometric; equality of traces is tested on Weil lifts,
not on arbitrary geometric constituents. -/
structure ChebotarevRules (G : TraceData p realization) (sigma : ℂ ≃+* ℂ) where
  coefficientLift : {P : Obj} → realization.WeilLift P →
    realization.WeilLift (T.coefficient P)
  dilateLift : ∀ a : (ZMod p)ˣ, {P : Obj} → realization.WeilLift P →
    realization.WeilLift (T.dilate (geometricUnit p a) P)
  coefficient_torusIC : ∀ P, G.TorusIC P → G.TorusIC (T.coefficient P)
  dilate_torusIC : ∀ a P, G.TorusIC P → G.TorusIC (T.dilate (geometricUnit p a) P)
  trace_coefficient : ∀ {P} (W : realization.WeilLift P), G.TorusIC P →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y,
      G.trace L (coefficientLift W) x y = sigma (G.trace L W x y)
  trace_dilate : ∀ a {P} (W : realization.WeilLift P), G.TorusIC P →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y,
      G.trace L (dilateLift a W) x y =
        G.trace L W (algebraMap (ZMod p) L (a : ZMod p) * x)
          (algebraMap (ZMod p) L (a : ZMod p) * y)
  chebotarev : ∀ {P Q} (WP : realization.WeilLift P) (WQ : realization.WeilLift Q),
    G.TorusIC P → G.TorusIC Q →
    (∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
      ∀ x y : L, x ≠ 0 → y ≠ 0 → G.trace L WP x y = G.trace L WQ x y) →
    T.Isomorphic P Q

/-- The actual trace identification, intentionally separate from the
general published-theorem record. The signed correction and all four
conjugation positions are defined by the existing finite sums. -/
def ExpectedCoreTrace (G : TraceData p realization) {P : Obj}
    (W : realization.WeilLift P)
    (α m m' n n' : ZMod p) (S : Finset (Fin 4)) : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y : L,
    x ≠ 0 → y ≠ 0 → G.trace L W x y =
      FiniteFieldSums.expectedTrace p L (algebraMap (ZMod p) L α)
        (algebraMap (ZMod p) L m) (algebraMap (ZMod p) L m')
        (algebraMap (ZMod p) L n) (algebraMap (ZMod p) L n') S x y

/-- The all-extension identity already gives the required prime-field
trace of the SAME physical Weil lift. A second unrelated trace hypothesis
is unnecessary. -/
theorem trace_on_units_of_expected_core_trace
    (G : TraceData p realization) {P : Obj} (W : realization.WeilLift P)
    (α m m' n n' : ZMod p) (S : Finset (Fin 4))
    (htrace : ExpectedCoreTrace G W α m m' n n' S)
    (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) :
    (realization.stalk W x y).trace =
      ∏ i ∈ S, PrimeGap182.TypeIII.correctedCycleFactors p α m m' n n' i x y := by
  rw [← G.prime_trace W x y]
  simpa only [Algebra.algebraMap_self, RingHom.id_apply,
    FiniteFieldSums.expectedTrace_prime] using htrace (ZMod p) x y hx hy

/-- The family's physical covariance is deduced from its trace formula
over ALL extensions, using the same coefficient automorphism throughout. -/
theorem physical_covariance_of_expected_trace
    (G : TraceData p realization) (sigma : ℂ ≃+* ℂ)
    (R : ChebotarevRules (T := T) G sigma) (P : Obj)
    (W : realization.WeilLift P) (hP : G.TorusIC P)
    (a : (ZMod p)ˣ)
    (hsigma : ∀ t : ZMod p,
      sigma (ZMod.stdAddChar t) = ZMod.stdAddChar ((a : ZMod p) * t))
    (α m m' n n' : ZMod p) (S : Finset (Fin 4))
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (htrace : ExpectedCoreTrace G W α m m' n n' S) :
    T.Isomorphic (T.coefficient P) (T.dilate (geometricUnit p ((a ^ 2)⁻¹)) P) := by
  apply R.chebotarev (R.coefficientLift W) (R.dilateLift ((a ^ 2)⁻¹) W)
    (R.coefficient_torusIC P hP)
    (R.dilate_torusIC _ P hP)
  intro L _ _ _ x y hx hy
  let j := algebraMap (ZMod p) L
  have hma : j m ≠ 0 := by simpa only [map_zero] using j.injective.ne hm
  have hma' : j m' ≠ 0 := by simpa only [map_zero] using j.injective.ne hm'
  have hna : j n ≠ 0 := by simpa only [map_zero] using j.injective.ne hn
  have hna' : j n' ≠ 0 := by simpa only [map_zero] using j.injective.ne hn'
  have hc : j (((a ^ 2)⁻¹ : (ZMod p)ˣ) : ZMod p) ≠ 0 := by
    simpa only [map_zero] using j.injective.ne ((a ^ 2)⁻¹).ne_zero
  rw [R.trace_coefficient W hP L x y, htrace L x y hx hy]
  rw [FiniteFieldSums.expectedTrace_coefficient_covariance_of_prime p sigma
    (a : ZMod p) a.ne_zero hsigma L _ _ _ _ _ S x y hma hma' hna hna']
  rw [R.trace_dilate _ W hP L x y,
    htrace L _ _ (mul_ne_zero hc hx) (mul_ne_zero hc hy)]
  congr 1 <;> simp [j, div_eq_mul_inv, mul_comm]

/-- Generic positive-kernel Fourier covariance. `scaledFourier a`
uses the additive character psi(a ·). The maps are linear pullbacks,
with no Tate normalization or complex absolute-value assumptions. -/
structure FourierCovarianceRules (a : (ZMod p)ˣ) where
  scaledFourier : (ZMod p)ˣ → Obj → Obj
  isomorphic_trans : ∀ {P Q R}, T.Isomorphic P Q → T.Isomorphic Q R → T.Isomorphic P R
  scaled_congr : ∀ b {P Q}, T.Isomorphic P Q →
    T.Isomorphic (scaledFourier b P) (scaledFourier b Q)
  coefficient_fourier : ∀ P,
    T.Isomorphic (T.coefficient (F.fourier P)) (scaledFourier a (T.coefficient P))
  scaled_dilate : ∀ b c P,
    T.Isomorphic (scaledFourier b (T.dilate (geometricUnit p c) P))
      (T.dilate (geometricUnit p (b / c)) (F.fourier P))

/-- Inverse-square physical dilation and character scaling combine to
give cubic Fourier dilation. This is a formal consequence of the generic
Fourier rules, rather than a new family covariance hypothesis. -/
theorem fourier_covariance_of_physical
    (a : (ZMod p)ˣ) (R : FourierCovarianceRules (T := T) (F := F) a)
    (P : Obj)
    (hphysical : T.Isomorphic (T.coefficient P)
      (T.dilate (geometricUnit p ((a ^ 2)⁻¹)) P)) :
    T.Isomorphic (T.coefficient (F.fourier P))
      (T.dilate (geometricUnit p (a ^ 3)) (F.fourier P)) := by
  have he : a / (a ^ (2 : ℕ))⁻¹ = a ^ (3 : ℕ) := by
    rw [div_eq_mul_inv, inv_inv]
    exact (pow_succ' a 2).symm
  exact R.isomorphic_trans (R.coefficient_fourier P)
    (R.isomorphic_trans (R.scaled_congr a hphysical)
      (by
        have h := R.scaled_dilate a ((a ^ (2 : ℕ))⁻¹) P
        rw [he] at h
        exact h))

theorem geometricUnit_two_cube (h2 : (2 : ZMod p) ≠ 0) :
    (geometricUnit p ((Units.mk0 2 h2) ^ 3) : AlgebraicClosure (ZMod p)) = 8 := by
  simp [geometricUnit]
  rw [map_ofNat]
  norm_num

/-- The exact eight-dilation used in the support proof, conditional on
published generic rules and the separately stated actual trace formula. -/
theorem eight_covariance_of_expected_trace
    (G : TraceData p realization) (sigma : ℂ ≃+* ℂ) (h2 : (2 : ZMod p) ≠ 0)
    (R : ChebotarevRules (T := T) G sigma)
    (RF : FourierCovarianceRules (T := T) (F := F) (Units.mk0 2 h2))
    (P : Obj) (W : realization.WeilLift P) (hP : G.TorusIC P)
    (hsigma : ∀ t : ZMod p, sigma (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t))
    (α m m' n n' : ZMod p) (S : Finset (Fin 4))
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (htrace : ExpectedCoreTrace G W α m m' n n' S) :
    ∃ eight : (AlgebraicClosure (ZMod p))ˣ, (eight : AlgebraicClosure (ZMod p)) = 8 ∧
      T.Isomorphic (T.coefficient (F.fourier P)) (T.dilate eight (F.fourier P)) := by
  refine ⟨geometricUnit p ((Units.mk0 2 h2) ^ 3), geometricUnit_two_cube h2, ?_⟩
  exact fourier_covariance_of_physical _ RF P
    (physical_covariance_of_expected_trace G sigma R P W hP (Units.mk0 2 h2)
      hsigma α m m' n n' S hm hm' hn hn' htrace)

end PrimeGap182.TypeIII.PublishedCovarianceRules

#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.geometricUnit
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.geometricUnit_val
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.TraceData
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.TraceData.mk
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.TraceData.trace
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.TraceData.prime_trace
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.TraceData.TorusIC
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.mk
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.coefficientLift
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.dilateLift
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.coefficient_torusIC
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.dilate_torusIC
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.trace_coefficient
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.trace_dilate
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ChebotarevRules.chebotarev
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.ExpectedCoreTrace
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.trace_on_units_of_expected_core_trace
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.physical_covariance_of_expected_trace
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.FourierCovarianceRules
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.FourierCovarianceRules.mk
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.FourierCovarianceRules.scaledFourier
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.FourierCovarianceRules.isomorphic_trans
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.FourierCovarianceRules.scaled_congr
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.FourierCovarianceRules.coefficient_fourier
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.FourierCovarianceRules.scaled_dilate
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.fourier_covariance_of_physical
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.geometricUnit_two_cube
#print axioms PrimeGap182.TypeIII.PublishedCovarianceRules.eight_covariance_of_expected_trace
