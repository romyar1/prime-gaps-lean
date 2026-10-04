import TypeIIIPhysicalTensorComparison

/-!
# Intermediate extension and its radial restriction from the actual image

BBD 1.4.22 defines intermediate extension as the image of the canonical
map from perverse extension by zero to perverse direct image. Exact open
restriction and its two counit comparisons identify the restricted image
with the original open object. The proof below keeps both original arrows.

The ordinary torus input is first sent to perverse-H0(A[2]). Geometric
realization and its Weil lift come from the same arithmetic plane object.
No lift of every geometric perverse object is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.IntermediateExtensionFromImage
open PublishedSupportRules PublishedPhysicalConstruction PhysicalTensorComparison
open PublishedPhaseApplication TensorListRepresentation

universe u v w z a b
variable {p : ℕ} [Fact p.Prime] {Obj : Type u}
  {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  (realization : RationalStalkRealization p D)
  (C : Type w) [Category.{z} C]

/-- General arithmetic perverse operations for the fixed torus open in
A2. The actual intermediate-extension object is constructed as an image. -/
structure Data where
  Open : Type u
  Plane : Type u
  [openCategory : Category.{u} Open]
  [openAbelian : Abelian Open]
  [planeCategory : Category.{u} Plane]
  [planeAbelian : Abelian Plane]
  perverseShift : C ⥤ Open
  extensionByZero : Open ⥤ Plane
  directImage : Open ⥤ Plane
  support : extensionByZero ⟶ directImage
  geometric : Plane → Obj
  weil : ∀ P, realization.WeilLift (geometric P)

attribute [instance] Data.openCategory Data.openAbelian Data.planeCategory Data.planeAbelian

variable {realization C} (M : Data realization C)

/-- The image in the arithmetic perverse heart, on every open perverse object. -/
def Data.intermediate (P : M.Open) : M.Plane := Abelian.image (M.support.app P)

/-- Both components of the old IC data use the same constructed object. -/
abbrev Data.IC : IntermediateExtensionData realization C where
  geometric A := M.geometric (M.intermediate (M.perverseShift.obj A))
  weil A := M.weil (M.intermediate (M.perverseShift.obj A))

/-- General restriction laws for the two perverse extensions and their
canonical support map. There is no intermediate-extension comparison field. -/
structure Restriction where
  restrict : M.Plane ⥤ M.Open
  [additive : restrict.Additive]
  [finiteLimits : PreservesFiniteLimits restrict]
  zero : M.extensionByZero ⋙ restrict ≅ 𝟭 M.Open
  direct : M.directImage ⋙ restrict ≅ 𝟭 M.Open
  support : ∀ P, restrict.map (M.support.app P) ≫ (direct.app P).hom = (zero.app P).hom

attribute [instance] Restriction.additive Restriction.finiteLimits

variable {M} (R : Restriction M)

/-- Open restriction sends the original support map to an isomorphism. -/
theorem Restriction.support_isIso (P : M.Open) :
    IsIso (R.restrict.map (M.support.app P)) := by
  have h : R.restrict.map (M.support.app P) = (R.zero.app P).hom ≫ (R.direct.app P).inv := by
    apply (cancel_mono (R.direct.app P).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using R.support P
  rw [h]
  infer_instance

/-- The restricted original image inclusion is mono and epi, hence invertible. -/
theorem Restriction.imageInclusion_isIso (P : M.Open) :
    IsIso (R.restrict.map (Abelian.image.ι (M.support.app P))) := by
  let := R.support_isIso P
  let : Epi (R.restrict.map (Abelian.image.ι (M.support.app P))) :=
    epi_of_epi_fac (by rw [← Functor.map_comp, Abelian.image.fac])
  exact isIso_of_mono_of_epi _

/-- Identify the restricted image using its original inclusion and the
general direct-image restriction comparison. -/
def Restriction.imageIso (P : M.Open) : R.restrict.obj (M.intermediate P) ≅ P := by
  letI := R.imageInclusion_isIso P
  exact asIso (R.restrict.map (Abelian.image.ι (M.support.app P))) ≪≫ R.direct.app P

/-- The comparison also preserves the original projection into the image. -/
theorem Restriction.imageIso_projection (P : M.Open) :
    R.restrict.map (Abelian.factorThruImage (M.support.app P)) ≫ (R.imageIso P).hom =
      (R.zero.app P).hom := by
  change R.restrict.map (Abelian.factorThruImage (M.support.app P)) ≫
    (R.restrict.map (Abelian.image.ι (M.support.app P)) ≫ (R.direct.app P).hom) = _
  rw [← Category.assoc, ← Functor.map_comp, Abelian.image.fac, R.support]

/-- The comparison preserves the original inclusion out of the image. -/
theorem Restriction.imageIso_inclusion (P : M.Open) :
    (R.imageIso P).hom ≫ (R.direct.app P).inv =
      R.restrict.map (Abelian.image.ι (M.support.app P)) := by
  change (R.restrict.map (Abelian.image.ι (M.support.app P)) ≫
    (R.direct.app P).hom) ≫ (R.direct.app P).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {E : Type a} [Field E] {G : Type b} [Group G]
  (I : C ⥤ FDRep E G) (radial : Obj → FDRep E G) (P : ParameterData C)

/-- General degree-minus-two radial stalk laws on the open and plane
categories. The shift comparison retains its original lissity guard. -/
structure RadialData (M : Data realization C) where
  restriction : Restriction M
  stalk : M.Open ⥤ FDRep E G
  plane : ∀ A, Representation.Equiv (radial (M.geometric A)).ρ
    (stalk.obj (restriction.restrict.obj A)).ρ
  shift : ∀ A, P.Lisse A → Representation.Equiv
    (stalk.obj (M.perverseShift.obj A)).ρ (I.obj A).ρ

variable {I radial P} (S : RadialData I radial P M)

/-- Restrict the actual image, then read the same lisse source at degree -2. -/
def RadialData.comparison (A : C) (hA : P.Lisse A) :
    Representation.Equiv (radial (M.IC.geometric A)).ρ (I.obj A).ρ :=
  (S.plane (M.intermediate (M.perverseShift.obj A))).trans <|
    (equivOfIso (S.stalk.mapIso (S.restriction.imageIso (M.perverseShift.obj A)))).trans
      (S.shift A hA)

/-- Supply the existing radial interface; ordinary dual/Tate restriction
remains its separate general lisse law. -/
def RadialData.inertiaCompatibility
    (dualTate : ∀ A, P.Lisse A → Representation.Equiv
      (I.obj (P.dualTateMinusOne A)).ρ (dualRepresentation (I.obj A)).ρ) :
    InertiaCompatibility I M.IC radial P where
  restriction := S.comparison
  dualTate := dualTate

end PrimeGap182.TypeIII.IntermediateExtensionFromImage

#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.Data.IC
#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.Restriction.support_isIso
#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.Restriction.imageInclusion_isIso
#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.Restriction.imageIso
#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.Restriction.imageIso_projection
#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.Restriction.imageIso_inclusion
#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.RadialData.comparison
#print axioms PrimeGap182.TypeIII.IntermediateExtensionFromImage.RadialData.inertiaCompatibility
