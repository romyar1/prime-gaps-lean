import TypeIIIProperAffinization
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The original structure-sheaf map of an affinization

For every quasi-compact, quasi-separated scheme X, the structure morphism
O_(Spec Γ(X, ⊤)) → (X.toSpecΓ)_* O_X is an isomorphism.  The morphism here
is the original map of structure sheaves belonging to X.toSpecΓ.  The
proof uses its existing localization isomorphisms on principal basic
opens and the actual sheaf-basis isomorphism criterion.

The proper-to-affine specialization supplies both topological finiteness
conditions from the original proper morphism.  Empty schemes are allowed.
This identifies the pushforward structure sheaf; it does not assert any
closed-fiber base-change map is surjective or any fiber is connected.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.ProperAffinizationStructureSheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

/-- The original structure map of the canonical morphism to Spec Γ(X, ⊤),
viewed as a morphism of the actual sheaves of rings. -/
def structureMap (X : Scheme.{u}) :
    (ProperAffinization.affineScheme X).sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u}
        (ProperAffinization.toAffinization X).base).obj X.sheaf :=
  ⟨(ProperAffinization.toAffinization X).c⟩

/-- Forgetting the sheaf condition recovers the original structure morphism. -/
theorem structureMap_hom (X : Scheme.{u}) :
    (structureMap X).hom = X.toSpecΓ.c := rfl

/-- On every open, this is the original map on sections, without a chosen replacement. -/
theorem structureMap_app (X : Scheme.{u}) (U : (ProperAffinization.affineScheme X).Opens) :
    (structureMap X).hom.app (op U) = X.toSpecΓ.app U := rfl

/-- The actual structure map is an isomorphism for every qcqs scheme. -/
instance structureMap_isIso (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    IsIso (structureMap X) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
  intro f
  change IsIso (X.toSpecΓ.app (PrimeSpectrum.basicOpen f))
  infer_instance

/-- The resulting sheaf isomorphism has the original structure map as its forward morphism. -/
def structureSheafIso (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (ProperAffinization.affineScheme X).sheaf ≅
      (TopCat.Sheaf.pushforward CommRingCat.{u}
        (ProperAffinization.toAffinization X).base).obj X.sheaf :=
  asIso (structureMap X)

/-- The sheaf isomorphism retains the literal original forward morphism. -/
theorem structureSheafIso_hom (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (structureSheafIso X).hom = structureMap X := rfl

/-- The original presheaf natural transformation is consequently an isomorphism. -/
theorem toSpecΓ_c_isIso (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    IsIso X.toSpecΓ.c := by
  change IsIso ((TopCat.Sheaf.forget CommRingCat.{u}
    (ProperAffinization.affineScheme X).carrier).map (structureMap X))
  infer_instance

/-- The original map on sections is an isomorphism for every open in the affinization. -/
theorem toSpecΓ_app_isIso (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : (ProperAffinization.affineScheme X).Opens) :
    IsIso (X.toSpecΓ.app U) := by
  have := toSpecΓ_c_isIso X
  infer_instance

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- Properness over an affine base supplies the qcqs hypotheses for this exact structure map. -/
theorem structureMap_isIso_of_proper (q : X ⟶ Spec (.of R)) [IsProper q] :
    IsIso (structureMap X) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  infer_instance

/-- The actual affinization of the original proper morphism has pushforward structure sheaf
equal, through its own structure morphism, to that of Spec Γ(X, ⊤). -/
def structureSheafIsoOfProper (q : X ⟶ Spec (.of R)) [IsProper q] :
    (ProperAffinization.affineScheme X).sheaf ≅
      (TopCat.Sheaf.pushforward CommRingCat.{u}
        (ProperAffinization.toAffinization X).base).obj X.sheaf := by
  let := structureMap_isIso_of_proper q
  exact asIso (structureMap X)

/-- The proper specialization has the same original forward map. -/
theorem structureSheafIsoOfProper_hom (q : X ⟶ Spec (.of R)) [IsProper q] :
    (structureSheafIsoOfProper q).hom = structureMap X := rfl

/-- On every open the proper specialization gives an isomorphism of the original section map. -/
theorem toSpecΓ_app_isIso_of_proper (q : X ⟶ Spec (.of R)) [IsProper q]
    (U : (ProperAffinization.affineScheme X).Opens) :
    IsIso (X.toSpecΓ.app U) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  exact toSpecΓ_app_isIso X U

end PrimeGap182.TypeIII.ProperAffinizationStructureSheaf

#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureMap
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureMap_hom
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureMap_app
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureMap_isIso
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureSheafIso
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureSheafIso_hom
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.toSpecΓ_c_isIso
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.toSpecΓ_app_isIso
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureMap_isIso_of_proper
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureSheafIsoOfProper
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureSheafIsoOfProper_hom
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.toSpecΓ_app_isIso_of_proper
