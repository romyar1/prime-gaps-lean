import TypeIIIEtaleSkyscraperFamily
import TypeIIIEtaleSkyscraperCohomology

/-!
# Global cohomology of a small family of skyscrapers

The sections of the actual product of skyscrapers are the product of
the original coefficient modules.  Each component of the comparison
is the original projection to the unique terminal-fiber element.

Discrete diagrams have enough injectives by the componentwise module
presentations.  The exact, injective-preserving skyscraper-product
functor then identifies its original global cohomology with the right
derived module-product functor.  Products of modules are exact, so all
positive cohomology vanishes for arbitrary coefficient diagrams.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleSkyscraperFamily

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) {ι : Type u}
  (Φ : ι → GrothendieckTopology.Point.{u} S.smallEtaleTopology)
  (E : Type u) [Ring E]

/-- Componentwise injective modules form an injective discrete diagram. -/
instance diagram_injective (M : Discrete ι ⥤ ModuleCat.{u} E)
    [∀ i, Injective (M.obj i)] : Injective M where
  factors {X Y} g f _ := by
    refine ⟨Discrete.natTrans (fun i => Injective.factorThru (g.app i) (f.app i)), ?_⟩
    apply NatTrans.ext
    funext i
    exact Injective.comp_factorThru (g.app i) (f.app i)

/-- The actual module injective presentations give enough injectives
in the same-universe category of discrete coefficient diagrams. -/
instance diagram_enoughInjectives : EnoughInjectives (Discrete ι ⥤ ModuleCat.{u} E) where
  presentation M := by
    let J : Discrete ι ⥤ ModuleCat.{u} E :=
      Discrete.functor (fun i => Injective.under (M.obj ⟨i⟩))
    have : ∀ i, Injective (J.obj i) := fun i =>
      inferInstanceAs (Injective (Injective.under (M.obj i)))
    let f : M ⟶ J := Discrete.natTrans (fun i => Injective.ι (M.obj i))
    have : ∀ i, Mono (f.app i) := fun i =>
      inferInstanceAs (Mono (Injective.ι (M.obj i)))
    have : Mono f := NatTrans.mono_of_mono_app f
    exact ⟨{ J := J, f := f }⟩

/-- The actual product functor on coefficient diagrams is additive. -/
instance coefficientProduct_additive :
    (lim (J := Discrete ι) (C := ModuleCat.{u} E)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Sections commute with the actual sheaf product, and each original
skyscraper contributes its original coefficient module. -/
def sectionsObjIso (M : Discrete ι ⥤ ModuleCat.{u} E) :
    (EtaleCohomology.sections S E).obj ((functor S Φ E).obj M) ≅
      ∏ᶜ (fun i : ι => M.obj ⟨i⟩) := by
  let : PreservesLimit (Discrete.functor (skyscrapers S Φ E M))
      (EtaleCohomology.sections S E) := by
    dsimp only [EtaleCohomology.sections]
    infer_instance
  exact PreservesProduct.iso (EtaleCohomology.sections S E) (skyscrapers S Φ E M) ≪≫
    Limits.Pi.mapIso
      (f := fun i => (EtaleCohomology.sections S E).obj (skyscrapers S Φ E M i))
      (g := fun i => M.obj ⟨i⟩)
      (fun i => EtaleSkyscraper.sectionsObjIso S (Φ i) E (M.obj ⟨i⟩))

/-- Each component of the section comparison is the actual skyscraper
product projection followed by its actual terminal-fiber projection. -/
@[reassoc (attr := simp)]
theorem sectionsObjIso_hom_π (M : Discrete ι ⥤ ModuleCat.{u} E) (i : ι) :
    (sectionsObjIso S Φ E M).hom ≫ Pi.π (fun j : ι => M.obj ⟨j⟩) i =
      (EtaleCohomology.sections S E).map (Pi.π (skyscrapers S Φ E M) i) ≫
        (EtaleSkyscraper.sectionsObjIso S (Φ i) E (M.obj ⟨i⟩)).hom := by
  simp only [sectionsObjIso, Iso.trans_hom, assoc, Limits.Pi.mapIso_hom_π,
    PreservesProduct.iso_hom, piComparison_comp_π_assoc]

/-- The original product and terminal-fiber projections are natural
in the original coefficient diagram. -/
theorem sectionsObjIso_naturality {M N : Discrete ι ⥤ ModuleCat.{u} E} (f : M ⟶ N) :
    (EtaleCohomology.sections S E).map ((functor S Φ E).map f) ≫
        (sectionsObjIso S Φ E N).hom =
      (sectionsObjIso S Φ E M).hom ≫
        Limits.Pi.map (f := fun i : ι => M.obj ⟨i⟩) (g := fun i : ι => N.obj ⟨i⟩)
          (fun i => f.app ⟨i⟩) := by
  apply Pi.hom_ext
  intro i
  simp only [assoc, sectionsObjIso_hom_π, Limits.Pi.map_π, sectionsObjIso_hom_π_assoc]
  rw [← Functor.map_comp_assoc, functor_map_π, Functor.map_comp, assoc]
  exact congrArg
    (fun k => (EtaleCohomology.sections S E).map (Pi.π (skyscrapers S Φ E M) i) ≫ k)
    ((EtaleSkyscraper.sectionsIso S (Φ i) E).hom.naturality (f.app ⟨i⟩))

/-- Global sections of the actual skyscraper product are the original
categorical product functor on coefficient diagrams. -/
def sectionsIso : functor S Φ E ⋙ EtaleCohomology.sections S E ≅
    lim (J := Discrete ι) (C := ModuleCat.{u} E) :=
  NatIso.ofComponents (fun M => sectionsObjIso S Φ E M ≪≫ Pi.isoLimit M)
    (fun {M N} f => by
      apply limit.hom_ext
      rintro ⟨i⟩
      simp only [Functor.comp_map, Iso.trans_hom, assoc, Pi.isoLimit_hom_π,
        lim_map, limMap_π, Pi.isoLimit_hom_π_assoc]
      have h := sectionsObjIso_naturality S Φ E f =≫ Pi.π (fun j : ι => N.obj ⟨j⟩) i
      simpa only [assoc, Limits.Pi.map_π] using h)

/-- The ordinary square is exactly the inverse of the original section comparison. -/
def ordinarySquareIso :
    (lim (J := Discrete ι) (C := ModuleCat.{u} E)) ⋙ (𝟭 (ModuleCat.{u} E)) ≅
      functor S Φ E ⋙ EtaleCohomology.sections S E :=
  Functor.rightUnitor _ ≪≫ (sectionsIso S Φ E).symm

/-- The original derived comparison computes global cohomology of the
actual product by the original right derived module-product functor. -/
def cohomologyIso (n : ℕ) :
    (lim (J := Discrete ι) (C := ModuleCat.{u} E)).rightDerived n ≅
      functor S Φ E ⋙ EtaleCohomology.functor S E n :=
  (Functor.rightUnitor _).symm ≪≫
    derivedBaseChangeIso (lim (J := Discrete ι) (C := ModuleCat.{u} E))
      (EtaleCohomology.sections S E) (functor S Φ E) (𝟭 (ModuleCat.{u} E))
      (ordinarySquareIso S Φ E).hom n

/-- The actual skyscraper product has zero positive global cohomology
for every coefficient diagram, without an injectivity hypothesis. -/
theorem isZero_cohomology_succ (n : ℕ) (M : Discrete ι ⥤ ModuleCat.{u} E) :
    IsZero ((EtaleCohomology.functor S E (n + 1)).obj ((functor S Φ E).obj M)) :=
  (rightDerived_isZero_of_preservesHomology
    (lim (J := Discrete ι) (C := ModuleCat.{u} E)) n M).of_iso
      ((cohomologyIso S Φ E (n + 1)).app M).symm

/-- Degree zero retains the original terminal-fiber projections and
the canonical augmentation maps to the original right derived functors. -/
theorem cohomologyIso_zero :
    (lim (J := Discrete ι) (C := ModuleCat.{u} E)).toRightDerivedZero ≫
        (cohomologyIso S Φ E 0).hom =
      (sectionsIso S Φ E).inv ≫
        Functor.whiskerLeft (functor S Φ E) (EtaleCohomology.sections S E).toRightDerivedZero := by
  have h := derivedBaseChangeMap_zero (lim (J := Discrete ι) (C := ModuleCat.{u} E))
    (EtaleCohomology.sections S E) (functor S Φ E) (𝟭 (ModuleCat.{u} E))
    (ordinarySquareIso S Φ E).hom
  apply NatTrans.ext
  funext M
  simpa [cohomologyIso, ordinarySquareIso, derivedBaseChangeIso] using NatTrans.congr_app h M

#print axioms diagram_injective
#print axioms diagram_enoughInjectives
#print axioms coefficientProduct_additive
#print axioms sectionsObjIso
#print axioms sectionsObjIso_hom_π
#print axioms sectionsObjIso_hom_π_assoc
#print axioms sectionsObjIso_naturality
#print axioms sectionsIso
#print axioms ordinarySquareIso
#print axioms cohomologyIso
#print axioms isZero_cohomology_succ
#print axioms cohomologyIso_zero

end PrimeGap182.TypeIII.EtaleSkyscraperFamily
