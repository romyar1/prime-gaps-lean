import TypeIIICoefficientAutomorphism
import TypeIIIPublishedCovarianceRules

/-!
# Compatible coefficient transport on complex traces

Keep traces in their actual coefficient field, extend its chosen
automorphism to ℂ, and derive the complex trace-transport law. The
geometric lifts and Chebotarev law are still general explicit inputs.
This constructs the existing ChebotarevRules without assuming an
unrelated automorphism on ℂ or its compatibility with all traces.
-/

noncomputable section

namespace PrimeGap182.TypeIII.CoefficientTraceTransport

open PublishedSupportRules PublishedFourierRules PublishedStalkSupport
open PublishedCovarianceRules

universe u
variable {p : ℕ} [Fact p.Prime] {Obj : Type u}
  {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : RationalStalkRealization p D} {T : CoefficientTransport D}
  {K : Type*} [Field K] [Algebra K ℂ]

/-- General coefficient-valued traces and geometric transport. No
particular physical object, source recipe or Type III family is a field. -/
structure Rules (G : TraceData p realization) (τ : K ≃+* K) where
  coefficientLift : {P : Obj} → realization.WeilLift P →
    realization.WeilLift (T.coefficient P)
  dilateLift : ∀ a : (ZMod p)ˣ, {P : Obj} → realization.WeilLift P →
    realization.WeilLift (T.dilate (geometricUnit p a) P)
  coefficient_torusIC : ∀ P, G.TorusIC P → G.TorusIC (T.coefficient P)
  dilate_torusIC : ∀ a P, G.TorusIC P → G.TorusIC (T.dilate (geometricUnit p a) P)
  trace : ∀ {P} (_W : realization.WeilLift P),
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], E → E → K
  trace_complex : ∀ {P} (W : realization.WeilLift P),
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y,
      G.trace E W x y = algebraMap K ℂ (trace W E x y)
  trace_coefficient : ∀ {P} (W : realization.WeilLift P), G.TorusIC P →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y,
      trace (coefficientLift W) E x y = τ (trace W E x y)
  trace_dilate : ∀ a {P} (W : realization.WeilLift P), G.TorusIC P →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y,
      G.trace E (dilateLift a W) x y =
        G.trace E W (algebraMap (ZMod p) E (a : ZMod p) * x)
          (algebraMap (ZMod p) E (a : ZMod p) * y)
  chebotarev : ∀ {P Q} (WP : realization.WeilLift P) (WQ : realization.WeilLift Q),
    G.TorusIC P → G.TorusIC Q →
    (∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
      ∀ x y : E, x ≠ 0 → y ≠ 0 → G.trace E WP x y = G.trace E WQ x y) →
    T.Isomorphic P Q

/-- The complex coefficient automorphism and its trace compatibility
come from the same supplied coefficient-field automorphism. -/
def Rules.toChebotarev {G : TraceData p realization} {τ : K ≃+* K}
    (R : Rules (T := T) G τ) :
    ChebotarevRules (T := T) G (CoefficientAutomorphism.extension K ℂ τ) where
  coefficientLift := R.coefficientLift
  dilateLift := R.dilateLift
  coefficient_torusIC := R.coefficient_torusIC
  dilate_torusIC := R.dilate_torusIC
  trace_coefficient W hW E _ _ _ x y := by
    rw [R.trace_complex, R.trace_coefficient W hW E x y,
      R.trace_complex, CoefficientAutomorphism.extension_spec]
  trace_dilate := R.trace_dilate
  chebotarev := R.chebotarev

end PrimeGap182.TypeIII.CoefficientTraceTransport

#print axioms PrimeGap182.TypeIII.CoefficientTraceTransport.Rules.toChebotarev
