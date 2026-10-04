import TypeIIIGenericCohomologyBaseChange

/-!
# The original physical entry on the generic radial curve

The generic base map used for cohomology base change is the literal
composite of the generic direction, radial map and physical map. General
inverse-image composition therefore identifies restriction of the original
signed entry with pullback of the same signed parabolic core. The sign is
retained; its eventual inertia trivialization is a separate step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.GenericPhysicalEntry

open GenericCurvePullback PhysicalRadialMorphism PhysicalTorusMorphism
open PublishedPhysicalConstruction

universe u v w z a b
variable (K : Type u) [Field K]

def parameterSectionMorphism : parameterScheme K ⟶ torusScheme K :=
  Spec.map (CommRingCat.ofHom (parameterSectionHom K).toRingHom)

def genericRadialMorphism : parameterScheme K ⟶ torusScheme K :=
  parameterSectionMorphism K ≫ radialMorphism K

theorem section_radialPhysical (alpha m n : Kˣ) :
    parameterSectionMorphism K ≫ radialPhysicalMorphism K alpha m n =
      radialParameterMorphism K alpha m n := by
  dsimp only [parameterSectionMorphism, radialPhysicalMorphism,
    radialParameterMorphism, radialParameterHom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem genericRadial_physical (alpha m n : Kˣ) :
    genericRadialMorphism K ≫ physicalMorphism K alpha m n =
      radialParameterMorphism K alpha m n := by
  rw [genericRadialMorphism, Category.assoc, radialMorphism_physicalMorphism,
    section_radialPhysical]

variable {p : ℕ} [Fact p.Prime]
  {C : Type v} [Category.{w} C] {C' : Type z} [Category.{a} C']
  (O : TorusOperationData p C)
  (B : (parameterScheme (ZMod p) ⟶ torusScheme (ZMod p)) → C ⥤ C')

/-- General inverse-image composition, on every map between the fixed
parameter spaces and every sheaf. -/
structure BasePullbackComposition where
  comparison : ∀ (f : parameterScheme (ZMod p) ⟶ torusScheme (ZMod p))
    (g : torusScheme (ZMod p) ⟶ torusScheme (ZMod p)),
    B (f ≫ g) ≅ O.pullback g ⋙ B f

variable [Abelian C] [MonoidalCategory C]
  {Input : Type u} {Point : Type b} {D : CurveData Input Point}
  {H : CohomologyData Input C} {P : ParameterData C}

/-- This is the posted physical entry, with its original sign and core,
restricted along the same generic radial map as the cohomology proof. -/
def genericPhysicalEntryIso (PC : BasePullbackComposition O B)
    (A : KloostermanInputData D) (alpha m n : (ZMod p)ˣ) :
    (B (genericRadialMorphism (ZMod p))).obj (pulledEntry (H := H) (P := P) A O alpha m n) ≅
      (B (radialParameterMorphism (ZMod p) alpha m n)).obj (P.signed (parabolicCore H A.input)) :=
  ((PC.comparison (genericRadialMorphism (ZMod p)) (physicalMorphism (ZMod p) alpha m n)).app
    (P.signed (parabolicCore H A.input))).symm ≪≫
    eqToIso (congrArg (fun f => (B f).obj (P.signed (parabolicCore H A.input)))
      (genericRadial_physical (ZMod p) alpha m n))

end PrimeGap182.TypeIII.GenericPhysicalEntry

#print axioms PrimeGap182.TypeIII.GenericPhysicalEntry.section_radialPhysical
#print axioms PrimeGap182.TypeIII.GenericPhysicalEntry.genericRadial_physical
#print axioms PrimeGap182.TypeIII.GenericPhysicalEntry.genericPhysicalEntryIso
