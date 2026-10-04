import TypeIIIPublishedTypeIII

/-!
ONE plane/curve object family is fixed before p. The general published
surface, support, coefficient, Fourier, stalk and whole-Weil-weight
projections are on exactly those same objects. Theory is constructed;
there is no family Application, TypeIII profile or arithmetic model field.
This is the data/GENERAL law boundary for the coherent endpoint assembly,
not an assertion that arbitrary dictionaries interpret adic theory.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PrimeGap182.TypeIII.PlaneGeneralTheoryFromSharedOperationsBeforePrime03
open PublishedTypeIII PublishedSupportRules PublishedStalkCertificate
open PublishedFourierRules

universe plane curve
variable (PlaneObj : ℕ → Type plane) (CurveObj : ℕ → Type curve)

/-- The actual standard theory operators and genuine ALL-object theorems,
fixed before the prime; none is a selected physical-family conclusion. -/
structure GeneralPlaneOperationsAndPublishedTheorems where
  surface : ∀ (p : ℕ) [Fact p.Prime], SurfaceData (AlgebraicClosure (ZMod p)) (PlaneObj p)
  bbd : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p), BBDRules (surface p)
  qst : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p), QSTRules (surface p)
  classification : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p), SupportClassification (surface p)
  degrees : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p), OrdinarySupportDegreeRules (surface p)
  coefficient : ∀ (p : ℕ) [Fact p.Prime], CoefficientTransport (surface p)
  fourier : ∀ (p : ℕ) [Fact p.Prime],
    PublishedFourierRules.FourierData (AlgebraicClosure (ZMod p)) (PlaneObj p) (CurveObj p)
  localRules : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p), PublishedFourierRules.LocalRules (surface p) (coefficient p) (fourier p)
  realization : ∀ (p : ℕ) [Fact p.Prime], RationalStalkRealization p (surface p)
  traceWeights : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    TraceWeightRules p (surface p) (realization p) (fourier p).fourier

/-- All fields of Theory are the literal shared operators/projections. -/
def theory (general : GeneralPlaneOperationsAndPublishedTheorems PlaneObj CurveObj)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) : Theory p where
  Obj := PlaneObj p
  CurveObj := CurveObj p
  data := general.surface p
  bbd := general.bbd p hp
  qst := general.qst p hp
  classification := general.classification p hp
  degrees := general.degrees p hp
  coefficient := general.coefficient p
  fourier := general.fourier p
  localRules := general.localRules p hp
  realization := general.realization p
  traceWeights := general.traceWeights p hp

@[simp] theorem theory_Obj (general : GeneralPlaneOperationsAndPublishedTheorems PlaneObj CurveObj)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) : (theory PlaneObj CurveObj general p hp).Obj = PlaneObj p := rfl

@[simp] theorem theory_realization
    (general : GeneralPlaneOperationsAndPublishedTheorems PlaneObj CurveObj)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (theory PlaneObj CurveObj general p hp).realization = general.realization p := rfl

end PrimeGap182.TypeIII.PlaneGeneralTheoryFromSharedOperationsBeforePrime03
#print axioms PrimeGap182.TypeIII.PlaneGeneralTheoryFromSharedOperationsBeforePrime03.theory
#print axioms PrimeGap182.TypeIII.PlaneGeneralTheoryFromSharedOperationsBeforePrime03.theory_realization
