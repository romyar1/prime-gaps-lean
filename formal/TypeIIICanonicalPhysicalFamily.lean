import TypeIIICanonicalCurveInput
import TypeIIIPhysicalLocalFamilyData

/-!
# The canonical original physical family and its uniform bounds

Assemble FamilyConstruction from the same signed parabolic core, physical
pullbacks and IC objects. Trace, purity and full support follow from the
existing physical construction. The complexity cap is derived from the
primitive Kl3/AS source classes and general operation bounds. Uniform
QST envelopes then fill the physical and transformed quantitative fields.

The arithmetic CohomologicalRealization remains an explicit input to this
assembly step; its family-specific fields must still be populated from
the separate source trace and arithmetic boundary constructions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CanonicalPhysicalFamily

open PublishedPhysicalConstruction PublishedStalkCertificate PublishedTypeIII
open CanonicalCurveInput StartingSourceComplexity StartingSourceMaps
open PublishedConstructionComplexity PublishedPolynomialComplexity PublishedApplicationBridge
open PhysicalLocalFamilyData PublishedPhaseApplication

universe u v w z a b c d e
variable {p : ℕ} [Fact p.Prime]
  {Input : Type u} {Point : Type v} {Line : Type w}
  {C : Type z} [Category.{a} C] [Abelian C] [MonoidalCategory C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {PP : ParameterData C}
  (F : PullbackData (ZMod p) Line Input) (LG : LineGeometry Line)
  (SR : ScalarPullbackRules F LG D) (kl as : Line)
  (hkl : Kl3Properties LG kl) (has : ASProperties LG as)
  (CR : CurveRules D) (GC : CohomologyRules D H PP)
  (O : TorusOperationData p C) (TA : TorusArithmeticData p C) (TR : TorusRules PP O TA)
  (M : CohomologicalRealization D H PP (canonicalInput F LG SR kl as hkl has) TA)
  (theory : Theory.{b,c} p)
  (traceData : PublishedCovarianceRules.TraceData p theory.realization)
  (IC : IntermediateExtensionData theory.realization C)
  (IR : IntermediateExtensionRules theory.traceWeights traceData PP TA IC)
  (f : ℕ → ℕ) (h unitCap : ℕ) (ci : Input → ℕ) (cp : C → ℕ)
  (cm : TorusMorphismComplexity (ZMod p))
  (Q : OperationBounds (D := D) (H := H) (P := PP) f unitCap ci cp cm O IC)
  (QM : TorusPolynomialRules cm)
  (SC : PrimitiveClasses Line) (cl : Line → ℕ) (cs : MorphismComplexity (ZMod p))
  (QS : StartingSourceComplexity.Bounds F SC f h cl ci cs)
  (QSM : PolynomialRules (ZMod p) cs)
  (hhyper : SC.Hypergeometric kl 3) (hAS : SC.NontrivialArtinSchreier as)
  (bnd : PublishedUniformComplexity.Bounds) (UR : PublishedUniformComplexity.Rules bnd theory)

local notation "cap" => physicalCap f (sourceCap f h) unitCap
local notation "A" => canonicalInput F LG SR kl as hkl has

/-- Construct the actual family, with no supplied finished-family trace, purity,
full-support, initial-input bound or finished physical complexity bound. -/
def canonicalFamily (alpha m m' n n' : (ZMod p)ˣ) :
    FamilyConstruction (bnd.stalkCap cap) (bnd.physicalSupportCap cap) p
      (alpha : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p)
      UR.theory.data UR.theory.qst UR.theory.realization UR.theory.fourier.fourier UR.theory.traceWeights :=
  UR.familyOfComplexity cap alpha m m' n n'
    (physicalObjects IC (entryObjects (H := H) (P := PP) A O alpha m m' n n'))
    (physicalLift IC (entryObjects (H := H) (P := PP) A O alpha m m' n n'))
    (fun S _ x y hx hy => physical_trace_on_units A CR GC O TA TR M
      theory.traceWeights traceData IC IR alpha m m' n n' S x y hx hy)
    (fun S _ => physical_pure_weight A CR GC O TA TR theory.traceWeights traceData IC IR alpha m m' n n' S)
    (fun S _ => physical_full_constituents A CR GC O TA TR theory.traceWeights traceData IC IR alpha m m' n n' S)
    (fun S _ => canonical_physical_complexity LG kl as hkl has F SR CR GC O TA TR IC
      f h unitCap ci cp cm Q QM SC cl cs QS QSM hhyper hAS alpha m m' n n' S)

/-- The family uses the literal original physical IC objects. -/
theorem canonicalFamily_physicalObjects (alpha m m' n n' : (ZMod p)ˣ) :
    (canonicalFamily F LG SR kl as hkl has CR GC O TA TR M theory traceData IC IR
      f h unitCap ci cp cm Q QM SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n').physicalObjects =
    physicalObjects IC (entryObjects (H := H) (P := PP) A O alpha m m' n n') := rfl

/-- All four transformed quantitative bounds use the same physical cap. -/
theorem canonicalFamily_transformedBounds (alpha m m' n n' : (ZMod p)ˣ) :
    TransformedBounds (theory := UR.theory) (bnd.exceptionalCap cap) (bnd.properCap cap)
      (bnd.punctualCap cap)
      (canonicalFamily F LG SR kl as hkl has CR GC O TA TR M theory traceData IC IR
        f h unitCap ci cp cm Q QM SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n') :=
  UR.transformedBoundsOfComplexity cap _ _ alpha m m' n n' _
    (fun S _ => canonical_physical_complexity LG kl as hkl has F SR CR GC O TA TR IC
      f h unitCap ci cp cm Q QM SC cl cs QS QSM hhyper hAS alpha m m' n n' S)

/-- The same Weil lift has the full all-extension trace, retaining its
extension-degree sign, as required by the covariance application. -/
theorem canonicalFamily_expectedTrace (alpha m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4)) :
    PublishedCovarianceRules.ExpectedCoreTrace traceData
      ((canonicalFamily F LG SR kl as hkl has CR GC O TA TR M theory traceData IC IR
        f h unitCap ci cp cm Q QM SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n').physicalLift S)
      (alpha : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p) S :=
  physical_expectedTrace A CR GC O TA TR M theory.traceWeights traceData IC IR alpha m m' n n' S

/-- The same physical objects satisfy the torus IC condition used in
Chebotarev; it follows from the general IC rule and proved input purity. -/
theorem canonicalFamily_torusIC (alpha m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4)) :
    traceData.TorusIC ((canonicalFamily F LG SR kl as hkl has CR GC O TA TR M theory traceData IC IR
      f h unitCap ci cp cm Q QM SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n').physicalObjects S) :=
  physical_torusIC A CR GC O TA TR theory.traceWeights traceData IC IR alpha m m' n n' S


variable {E : Type d} [Field E] {G : Type e} [Group G]
  {PD : PhaseData (AlgebraicClosure (ZMod p)) E G}
  {CF : CubicFourierData (AlgebraicClosure (ZMod p)) E G}
  (radial : RadialRealization UR.theory PD)

/-- Insert local data into the same canonical arithmetic/quantitative
family. Equality with the original physical objects is proved here. -/
def canonicalLocalFamilyData (alpha m m' n n' : (ZMod p)ˣ)
    (localData : PhysicalLocalData (H := H) (P := PP) A O IC radial.inertia CF alpha m m' n n') :
    LocalFamilyData radial
      (canonicalFamily F LG SR kl as hkl has CR GC O TA TR M theory traceData IC IR
        f h unitCap ci cp cm Q QM SC cl cs QS QSM hhyper hAS bnd UR alpha m m' n n') CF :=
  PhysicalLocalData.toLocalFamilyData (theory := UR.theory) A O IC radial localData _ rfl

end PrimeGap182.TypeIII.CanonicalPhysicalFamily

#print axioms PrimeGap182.TypeIII.CanonicalPhysicalFamily.canonicalFamily
#print axioms PrimeGap182.TypeIII.CanonicalPhysicalFamily.canonicalFamily_physicalObjects
#print axioms PrimeGap182.TypeIII.CanonicalPhysicalFamily.canonicalFamily_transformedBounds
#print axioms PrimeGap182.TypeIII.CanonicalPhysicalFamily.canonicalFamily_expectedTrace
#print axioms PrimeGap182.TypeIII.CanonicalPhysicalFamily.canonicalFamily_torusIC

#print axioms PrimeGap182.TypeIII.CanonicalPhysicalFamily.canonicalLocalFamilyData
