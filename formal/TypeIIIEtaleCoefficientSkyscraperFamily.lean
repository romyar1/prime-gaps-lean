import TypeIIIEtaleCoefficientRestriction
import TypeIIIEtaleSkyscraperFamily

/-!
# Coefficient restriction of an actual skyscraper product

Restriction of module scalars commutes with the actual product of
skyscrapers.  The comparison is the canonical preserved-product
isomorphism followed by the original single-skyscraper comparisons.
Its projection formulas retain both the outer family projection and
the inner projection indexed by an element of the actual point fiber.

Both coefficient rings and their homomorphism are arbitrary.  No
flatness, injectivity, or acyclicity hypothesis enters this comparison.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleCoefficientSkyscraperFamily

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

variable (S : Scheme.{u}) {ι : Type u}
  {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')
  (Φ : ι → GrothendieckTopology.Point.{u} S.smallEtaleTopology)

/-- The original module restriction applied to the coefficient diagram. -/
def diagramRestriction : (Discrete ι ⥤ ModuleCat.{u} E') ⥤
    (Discrete ι ⥤ ModuleCat.{u} E) :=
  (Functor.whiskeringRight (Discrete ι) (ModuleCat.{u} E') (ModuleCat.{u} E)).obj
    (ModuleCat.restrictScalars r)

/-- The restricted diagram is literally composition with scalar restriction. -/
theorem diagramRestriction_obj (M : Discrete ι ⥤ ModuleCat.{u} E') :
    (diagramRestriction r).obj M = M ⋙ ModuleCat.restrictScalars r := rfl

/-- Each map is the original component with its scalars restricted. -/
theorem diagramRestriction_map_app {M N : Discrete ι ⥤ ModuleCat.{u} E'}
    (f : M ⟶ N) (i : Discrete ι) :
    ((diagramRestriction r).map f).app i =
      (ModuleCat.restrictScalars r).map (f.app i) := rfl

/-- The actual coefficient-restricted product is canonically the product
of the original skyscrapers of the restricted coefficient modules. -/
def objIso (M : Discrete ι ⥤ ModuleCat.{u} E') :
    (EtaleCoefficientRestriction.functor S r).obj
        ((EtaleSkyscraperFamily.functor S Φ E').obj M) ≅
      (EtaleSkyscraperFamily.functor S Φ E).obj ((diagramRestriction r).obj M) :=
  PreservesProduct.iso (EtaleCoefficientRestriction.functor S r)
      (EtaleSkyscraperFamily.skyscrapers S Φ E' M) ≪≫
    Limits.Pi.mapIso
      (f := fun i => (EtaleCoefficientRestriction.functor S r).obj
        (EtaleSkyscraperFamily.skyscrapers S Φ E' M i))
      (g := EtaleSkyscraperFamily.skyscrapers S Φ E ((diagramRestriction r).obj M))
      (fun i => (EtaleCoefficientRestriction.skyscraperIso S r (Φ i)).app (M.obj ⟨i⟩))

/-- The outer projection is the original product projection with its
coefficients restricted, followed by the original single-skyscraper comparison. -/
@[reassoc (attr := simp)]
theorem objIso_hom_π (M : Discrete ι ⥤ ModuleCat.{u} E') (i : ι) :
    (objIso S r Φ M).hom ≫
        Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E ((diagramRestriction r).obj M)) i =
      (EtaleCoefficientRestriction.functor S r).map
          (Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E' M) i) ≫
        (EtaleCoefficientRestriction.skyscraperIso S r (Φ i)).hom.app (M.obj ⟨i⟩) := by
  simp only [objIso, Iso.trans_hom, assoc, Limits.Pi.mapIso_hom_π,
    PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  rfl

/-- The inverse comparison retains the corresponding original projection. -/
@[reassoc (attr := simp)]
theorem objIso_inv_π (M : Discrete ι ⥤ ModuleCat.{u} E') (i : ι) :
    (objIso S r Φ M).inv ≫
        (EtaleCoefficientRestriction.functor S r).map
          (Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E' M) i) =
      Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E ((diagramRestriction r).obj M)) i ≫
        (EtaleCoefficientRestriction.skyscraperIso S r (Φ i)).inv.app (M.obj ⟨i⟩) := by
  apply (Iso.inv_comp_eq (objIso S r Φ M)).mpr
  rw [← assoc, objIso_hom_π]
  simp only [assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- The comparison commutes with the original maps of coefficient diagrams. -/
theorem objIso_naturality {M N : Discrete ι ⥤ ModuleCat.{u} E'} (f : M ⟶ N) :
    (EtaleCoefficientRestriction.functor S r).map
          ((EtaleSkyscraperFamily.functor S Φ E').map f) ≫
        (objIso S r Φ N).hom =
      (objIso S r Φ M).hom ≫
        (EtaleSkyscraperFamily.functor S Φ E).map ((diagramRestriction r).map f) := by
  apply Pi.hom_ext
  intro i
  simp only [assoc, objIso_hom_π, EtaleSkyscraperFamily.functor_map_π,
    objIso_hom_π_assoc, diagramRestriction_map_app]
  rw [← CategoryTheory.Functor.map_comp_assoc, EtaleSkyscraperFamily.functor_map_π,
    CategoryTheory.Functor.map_comp, assoc]
  exact congrArg
    (fun k => (EtaleCoefficientRestriction.functor S r).map
      (Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E' M) i) ≫ k)
    ((EtaleCoefficientRestriction.skyscraperIso S r (Φ i)).hom.naturality (f.app ⟨i⟩))

/-- The canonical natural isomorphism between the two actual family functors. -/
def familyIso :
    EtaleSkyscraperFamily.functor S Φ E' ⋙ EtaleCoefficientRestriction.functor S r ≅
      diagramRestriction r ⋙ EtaleSkyscraperFamily.functor S Φ E :=
  NatIso.ofComponents (objIso S r Φ) (fun f => objIso_naturality S r Φ f)

/-- The forward component is exactly the proved product comparison. -/
theorem familyIso_hom_app (M : Discrete ι ⥤ ModuleCat.{u} E') :
    (familyIso S r Φ).hom.app M = (objIso S r Φ M).hom := rfl

/-- The inverse component is the inverse of that same product comparison. -/
theorem familyIso_inv_app (M : Discrete ι ⥤ ModuleCat.{u} E') :
    (familyIso S r Φ).inv.app M = (objIso S r Φ M).inv := rfl

/-- On an actual étale object, the outer family projection followed by
the actual point-fiber projection is the scalar restriction of the
original nested projection. -/
theorem objIso_hom_app_π_π (M : Discrete ι ⥤ ModuleCat.{u} E') (i : ι)
    (U : S.Etale) (t : (Φ i).fiber.obj U) :
    (objIso S r Φ M).hom.hom.app (op U) ≫
        (Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E ((diagramRestriction r).obj M)) i).hom.app
          (op U) ≫
        Pi.π (fun _ : (Φ i).fiber.obj U => (ModuleCat.restrictScalars r).obj (M.obj ⟨i⟩)) t =
      (ModuleCat.restrictScalars r).map
        ((Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E' M) i).hom.app (op U) ≫
          Pi.π (fun _ : (Φ i).fiber.obj U => M.obj ⟨i⟩) t) := by
  have h := congrArg (fun f => f.hom.app (op U)) (objIso_hom_π S r Φ M i)
  change (objIso S r Φ M).hom.hom.app (op U) ≫
      (Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E ((diagramRestriction r).obj M)) i).hom.app
        (op U) =
    (ModuleCat.restrictScalars r).map
        ((Pi.π (EtaleSkyscraperFamily.skyscrapers S Φ E' M) i).hom.app (op U)) ≫
      ((EtaleCoefficientRestriction.skyscraperIso S r (Φ i)).hom.app (M.obj ⟨i⟩)).hom.app
        (op U) at h
  rw [← assoc, h, assoc, EtaleCoefficientRestriction.skyscraperIso_hom_app_π,
    ← CategoryTheory.Functor.map_comp]

#print axioms diagramRestriction
#print axioms diagramRestriction_obj
#print axioms diagramRestriction_map_app
#print axioms objIso
#print axioms objIso_hom_π
#print axioms objIso_hom_π_assoc
#print axioms objIso_inv_π
#print axioms objIso_inv_π_assoc
#print axioms objIso_naturality
#print axioms familyIso
#print axioms familyIso_hom_app
#print axioms familyIso_inv_app
#print axioms objIso_hom_app_π_π

end PrimeGap182.TypeIII.EtaleCoefficientSkyscraperFamily
