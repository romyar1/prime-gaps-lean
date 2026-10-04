import TypeIIIPublishedPhysicalConstruction
import TypeIIIPublishedApplicationBridge

/-!
# Local data on the actual physical IC objects

This intermediate application record separates the local construction
from arithmetic traces and quantitative envelopes. Its fields will be
constructed from sources; they are not declared published hypotheses.
The adapter inserts the record into the existing LocalFamilyData when
the family uses those same physical objects.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.PhysicalLocalFamilyData

open PublishedPhysicalConstruction PublishedPhaseApplication PublishedApplicationBridge
open PublishedTypeIII PublishedStalkCertificate

universe u v w z a b c d
variable {p : ℕ} [Fact p.Prime]
  {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C] [MonoidalCategory C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
  {E : Type a} [Field E] {G : Type b} [Group G]

/-- Application data on the literal original physical objects, before
attaching the matching Weil lifts and global complexity bounds. -/
structure PhysicalLocalData {Obj : Type c}
    {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    {realization : PublishedSupportRules.RationalStalkRealization p SD}
    (A : KloostermanInputData D) (O : TorusOperationData p C)
    (IC : IntermediateExtensionData realization C) (radial : Obj → FDRep E G)
    (CF : CubicFourierData (AlgebraicClosure (ZMod p)) E G)
    (alpha m m' n n' : (ZMod p)ˣ) where
  cores : PhaseRectangle → FDRep E G
  localData : ∀ e : PhaseRectangle,
    CoreLocalData CF (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) (alpha : ZMod p))
      (residuePair p (m : ZMod p) (m' : ZMod p) e.1)
      (residuePair p (n : ZMod p) (n' : ZMod p) e.2) (cores e)
  tensor_comparison : ∀ S : Finset (Fin 4),
    IsSubquotient
      (radial (physicalObjects IC (entryObjects (H := H) (P := P) A O alpha m m' n n') S))
      (selectedTensor (rectangleSubset S)
        (fun e => signedRepresentation (conjugatedCorner e) (cores e)))

variable {theory : Theory.{c,d} p} {B Rphys : ℕ}
  {PD : PhaseData (AlgebraicClosure (ZMod p)) E G}
  {CF : CubicFourierData (AlgebraicClosure (ZMod p)) E G}
  {alpha m m' n n' : (ZMod p)ˣ}
  (A : KloostermanInputData D) (O : TorusOperationData p C)
  (IC : IntermediateExtensionData theory.realization C)
  (radial : RadialRealization theory PD)

/-- A generic adapter. The canonical physical-family constructor proves
the object equality used here, so it need not be a final family premise. -/
def PhysicalLocalData.toLocalFamilyData
    (d : PhysicalLocalData (H := H) (P := P) A O IC radial.inertia CF alpha m m' n n')
    (family : FamilyConstruction B Rphys p (alpha : ZMod p) (m : ZMod p) (m' : ZMod p)
      (n : ZMod p) (n' : ZMod p) theory.data theory.qst theory.realization
      theory.fourier.fourier theory.traceWeights)
    (heq : family.physicalObjects =
      physicalObjects IC (entryObjects (H := H) (P := P) A O alpha m m' n n')) :
    LocalFamilyData radial family CF where
  cores := d.cores
  localData := d.localData
  tensor_comparison S _ := by
    rw [heq]
    exact d.tensor_comparison S

end PrimeGap182.TypeIII.PhysicalLocalFamilyData

#print axioms PrimeGap182.TypeIII.PhysicalLocalFamilyData.PhysicalLocalData.toLocalFamilyData
