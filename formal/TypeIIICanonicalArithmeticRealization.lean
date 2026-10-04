import TypeIIIBoundaryCohomologyFromSources
import TypeIIICanonicalInputTrace
import TypeIIITameFrobeniusScaling

/-!
# Arithmetic realization constructed from source traces and monodromy

Populate the original cohomological record on the same arithmetic fibers.
Its three family point traces and its full boundary/Frobenius comparison
are derived, rather than supplied as completed family records. Source
Frobenius operators, naturality and Jordan scaling are also constructed
from general inertia covariance. General
fiber, boundary, sign and pullback laws and individual-source arithmetic
models remain explicit. A concrete common sheaf realization is not
constructed by this module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.CanonicalArithmeticRealization

open PublishedPhysicalConstruction PublishedPhaseApplication
open StartingSourceComplexity CanonicalCurveInput CanonicalInputTrace
open BoundaryFromSourceModels RestrictionFrobenius ArithmeticBoundaryFromSources
open BoundaryCohomologyFromSources FrobeniusBoundaryBasis RegularUnipotentRepresentation TameFrobeniusScaling

attribute [local irreducible] canonicalInput

universe u v w z a b l
variable {p : ℕ} [Fact p.Prime]
  {Input : Type u} {Point : Type v} {C : Type w} [Category.{z} C] [Abelian C]
  {Line : Type l} {D : CurveData Input Point} {H : CohomologyData Input C}
  {PP : ParameterData C}
  (PF : PullbackData (ZMod p) Line Input) (LG : LineGeometry Line)
  (SR : ScalarPullbackRules PF LG D) (kl as : Line)
  (hkl : Kl3Properties LG kl) (has : ASProperties LG as)
  (CR : CurveRules D) (TA : TorusArithmeticData p C)
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (tame : G0 →* Multiplicative ℂ) (htame : ∃ g, (tame g).toAdd ≠ 0)

local notation "K" => canonicalInput PF LG SR kl as hkl has

variable
  (AF : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, (TA.fiber E x y).Additive)
  (FL : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, PreservesFiniteLimits (TA.fiber E x y))
  (FC : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, PreservesFiniteColimits (TA.fiber E x y))
  (CT : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ _x _y : Eˣ, CurveTraceData D E)
  (VR : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, CurveFiberRules D H (TA.fiber E x y) (TA.frobenius E x y) E (CT E x y))
  (lineTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ _x _y : Eˣ, Line → E → ℂ)
  (PT : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, PullbackTraceRules PF (CT E x y) (lineTrace E x y) x y)
  (klTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, ∀ z : Eˣ, lineTrace E x y kl (z : E) = FiniteFieldSums.kl3 (FiniteFieldSums.traceAddChar p E) (z : E))
  (asTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, ∀ z : E, lineTrace E x y as z = FiniteFieldSums.traceAddChar p E z)
  (BS : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, BoundarySequence D H (TA.fiber E x y))
  (AZ : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, RestrictionData (G0 := G0) (Ginf := Ginf) D H (TA.fiber E x y) (BS E x y))
  (AP : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, ArithmeticRestriction (AZ E x y))
  (AB : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, ArithmeticBoundary (AZ E x y) (AP E x y) (TA.frobenius E x y))
  (inertiaConjugation : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ _x _y : Eˣ, G0 →* G0)
  (tameFrobenius : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, ∀ g, (tame (inertiaConjugation E x y g)).toAdd =
    (Fintype.card E : ℂ)⁻¹ * (tame g).toAdd)
  (inertiaCovariance : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, ∀ A g v,
    (AP E x y).zeroFr A (((AZ E x y).zero A).ρ g v) =
      ((AZ E x y).zero A).ρ (inertiaConjugation E x y g) ((AP E x y).zeroFr A v))
  (firstZero : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, Representation.Equiv ((AZ E x y).zero (canonicalInput PF LG SR kl as hkl has).first).ρ (tameRepresentation tame))
  (secondZero : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, Representation.Equiv ((AZ E x y).zero (canonicalInput PF LG SR kl as hkl has).second).ρ (tameRepresentation tame))
  (additiveZero : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, Representation.Equiv ((AZ E x y).zero (canonicalInput PF LG SR kl as hkl has).additive).ρ (Representation.trivial ℂ G0 ℂ))
  (additiveNatural : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, ∀ v, additiveZero E x y ((AP E x y).zeroFr (canonicalInput PF LG SR kl as hkl has).additive v) = additiveZero E x y v)
  (scalar : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ _x _y : Eˣ, ℂ)
  (scalar_ne_zero : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, scalar E x y ≠ 0)
  (firstInvariantLine : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, 
    (AP E x y).zeroFr (canonicalInput PF LG SR kl as hkl has).first ((firstZero E x y).toLinearEquiv.symm (Pi.single 0 1)) =
      scalar E x y • (firstZero E x y).toLinearEquiv.symm (Pi.single 0 1))
  (secondInvariantLine : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, 
    (AP E x y).zeroFr (canonicalInput PF LG SR kl as hkl has).second ((secondZero E x y).toLinearEquiv.symm (Pi.single 0 1)) =
      scalar E x y • (secondZero E x y).toLinearEquiv.symm (Pi.single 0 1))
  (sign : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ, SignStalkComparison PP (TA.fiber E x y) (TA.frobenius E x y) (Module.finrank (ZMod p) E))

/-- The original arithmetic record, with its family trace and boundary
fields constructed from source models on the same fibers. In particular,
there is no CohomologicalRealization, KloostermanTraceData,
KloostermanBoundaryData, OriginBoundaryModel or RegularModel input. -/
def cohomologicalRealization : CohomologicalRealization D H PP K TA where
  additive := AF
  finiteLimits := FL
  finiteColimits := FC
  curveTrace := CT
  fiberRules := VR
  originalTraces E _ _ _ x y :=
    canonicalTraceData PF LG SR kl as hkl has (CT E x y) (lineTrace E x y) x y (PT E x y)
      (FiniteFieldSums.traceAddChar p E) (klTrace E x y) (asTrace E x y)
  boundary E _ _ _ x y := boundaryData (AZ E x y) (AP E x y) (TA.frobenius E x y) (AB E x y)
  boundaryRules E _ _ _ x y := boundaryRules (AZ E x y) (AP E x y) (TA.frobenius E x y) (AB E x y)
  localBoundary E _ _ _ x y := by
    let firstOperator := sourceFrobenius tame ((AZ E x y).zero (K).first)
      (firstZero E x y) ((AP E x y).zeroFr (K).first)
    let secondOperator := sourceFrobenius tame ((AZ E x y).zero (K).second)
      (secondZero E x y) ((AP E x y).zeroFr (K).second)
    refine localBoundaryData (D := D) (H := H) (F := TA.fiber E x y)
      (S := BS E x y) (rho := tameRepresentation tame) (AZ E x y) (AP E x y)
      (TA.frobenius E x y) (AB E x y) K CR (tameRegularModel tame htame)
      (firstZero E x y) (secondZero E x y) (additiveZero E x y)
      firstOperator secondOperator ?_ ?_ (additiveNatural E x y)
      (Fintype.card E : ℂ) (scalar E x y) (PublishedParabolicTrace.complexCard_ne_zero E)
      (scalar_ne_zero E x y) ?_ ?_ ?_ ?_
      (nat_eigenvalue_separation (k := ℂ) (Fintype.card E) Fintype.one_lt_card).1
      (nat_eigenvalue_separation (k := ℂ) (Fintype.card E) Fintype.one_lt_card).2
    · exact sourceFrobenius_natural tame ((AZ E x y).zero (K).first)
        (firstZero E x y) ((AP E x y).zeroFr (K).first)
    · exact sourceFrobenius_natural tame ((AZ E x y).zero (K).second)
        (secondZero E x y) ((AP E x y).zeroFr (K).second)
    · exact sourceFrobenius_scaling tame htame ((AZ E x y).zero (K).first)
        (firstZero E x y) ((AP E x y).zeroFr (K).first)
        (inertiaConjugation E x y) (Fintype.card E : ℂ)⁻¹ (tameFrobenius E x y)
        (inertiaCovariance E x y (K).first)
    · exact sourceFrobenius_scaling tame htame ((AZ E x y).zero (K).second)
        (secondZero E x y) ((AP E x y).zeroFr (K).second)
        (inertiaConjugation E x y) (Fintype.card E : ℂ)⁻¹ (tameFrobenius E x y)
        (inertiaCovariance E x y (K).second)
    · exact sourceFrobenius_leading tame ((AZ E x y).zero (K).first)
        (firstZero E x y) ((AP E x y).zeroFr (K).first)
        (scalar E x y) (firstInvariantLine E x y)
    · exact sourceFrobenius_leading tame ((AZ E x y).zero (K).second)
        (secondZero E x y) ((AP E x y).zeroFr (K).second)
        (scalar E x y) (secondInvariantLine E x y)
  sign := sign

end PrimeGap182.TypeIII.CanonicalArithmeticRealization

#print axioms PrimeGap182.TypeIII.CanonicalArithmeticRealization.cohomologicalRealization
