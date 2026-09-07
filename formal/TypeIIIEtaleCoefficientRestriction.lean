import TypeIIIEtaleSkyscraperExact
import TypeIIIArtinSchreierCoefficientMaps
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Actual coefficient restriction on the small étale site

For an arbitrary ring map, restriction of coefficients is composition of
the original module sheaf with restriction of module scalars.  The affine
construction already used for Artin--Schreier coefficients is retained
definitionally.  Actual limits and local surjectivity prove exactness.

Global sections commute with this restriction by their literal evaluation
formula.  The original skyscraper commutes with it by the canonical
product-preservation isomorphism, with the original projection maps.
No flatness or preservation of injective objects is assumed or asserted.
-/

noncomputable section

universe u v w

namespace PrimeGap182.TypeIII.EtaleCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

section Scalars

variable {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- Scalar restriction preserves an existing limit of any size.  The
actual underlying limit supplies the required smallness of its sections. -/
instance scalar_preservesLimit {J : Type v} [Category.{w} J]
    (K : J ⥤ ModuleCat.{u} E') : PreservesLimit K (ModuleCat.restrictScalars r) where
  preserves {c} hc := by
    have : HasLimit (K ⋙ forget (ModuleCat.{u} E')) :=
      ⟨_, isLimitOfPreserves (forget (ModuleCat.{u} E')) hc⟩
    have : Small.{u} (K ⋙ forget (ModuleCat.{u} E')).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    let : PreservesLimit K (ModuleCat.restrictScalars r) :=
      ModuleCat.preservesLimit_restrictScalars r K
    exact ⟨isLimitOfPreserves (ModuleCat.restrictScalars r) hc⟩

/-- These are actual preserved limits, without commutativity of the
coefficient rings or a flatness premise. -/
instance scalar_preservesLimits :
    PreservesLimitsOfSize.{w, v} (ModuleCat.restrictScalars.{u} r) where
  preservesLimitsOfShape := { preservesLimit := fun {K} => scalar_preservesLimit r K }

/-- Actual module scalar restriction preserves colimits through its
existing adjunction to coextension of scalars. -/
instance scalar_preservesColimits :
    PreservesColimitsOfSize.{w, v} (ModuleCat.restrictScalars.{u} r) :=
  (ModuleCat.restrictCoextendScalarsAdj r).leftAdjoint_preservesColimits

end Scalars

section Sheaves

variable (S : Scheme.{u}) {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- Actual restriction of coefficient scalars on an arbitrary small
étale site, using the original module restriction functor. -/
def functor :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E') ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  sheafCompose S.smallEtaleTopology (ModuleCat.restrictScalars r)

/-- On each object, the original section module has its scalars restricted. -/
theorem functor_obj_obj (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E'))
    (U : S.Etaleᵒᵖ) :
    ((functor S r).obj F).obj.obj U =
      (ModuleCat.restrictScalars r).obj (F.obj.obj U) := rfl

/-- On each sheaf morphism, the original component is the same linear
map with its scalars restricted. -/
theorem functor_map_hom_app
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')} (f : F ⟶ G)
    (U : S.Etaleᵒᵖ) :
    ((functor S r).map f).hom.app U =
      (ModuleCat.restrictScalars r).map (f.hom.app U) := rfl

/-- All small limits, in particular small products, are preserved by
the original objectwise restriction and the full sheaf inclusion. -/
instance functor_preservesLimits : PreservesLimitsOfSize.{u, u} (functor S r) where
  preservesLimitsOfShape {J} _ := by
    let : PreservesLimitsOfShape J
        ((Functor.whiskeringRight S.Etaleᵒᵖ (ModuleCat.{u} E')
          (ModuleCat.{u} E)).obj (ModuleCat.restrictScalars r)) :=
      whiskeringRight_preservesLimitsOfShape (ModuleCat.restrictScalars r)
    let : PreservesLimitsOfShape J
        (functor S r ⋙ sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      inferInstanceAs (PreservesLimitsOfShape J
        (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E') ⋙
          (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars r)))
    exact preservesLimitsOfShape_of_reflects_of_preserves (functor S r)
      (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E))

/-- Finite limits are the actual objectwise limits of module sheaves. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor S r) where
  preservesFiniteLimits J _ _ := by
    let : PreservesLimitsOfShape J
        ((Functor.whiskeringRight S.Etaleᵒᵖ (ModuleCat.{u} E')
          (ModuleCat.{u} E)).obj (ModuleCat.restrictScalars r)) :=
      whiskeringRight_preservesLimitsOfShape (ModuleCat.restrictScalars r)
    let : PreservesLimitsOfShape J
        (functor S r ⋙ sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      inferInstanceAs (PreservesLimitsOfShape J
        (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E') ⋙
          (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars r)))
    exact preservesLimitsOfShape_of_reflects_of_preserves (functor S r)
      (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E))

/-- The original coefficient restriction is additive. -/
instance functor_additive : (functor S r).Additive where
  map_add := by
    intro F G f g
    ext U x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Local surjectivity is unchanged, since all underlying section maps
are the original functions.  Hence actual sheaf epimorphisms are preserved. -/
instance functor_preservesEpimorphisms : (functor S r).PreservesEpimorphisms where
  preserves {F G} f hf := by
    have hlocal : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} E') f).mpr hf
    have hlocal' : Sheaf.IsLocallySurjective ((functor S r).map f) := by
      constructor
      intro U s
      change Presheaf.imageSieve f.hom s ∈ S.smallEtaleTopology U
      exact hlocal.imageSieve_mem s
    exact (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} E) _).mp hlocal'

/-- The proved preservation of kernels and epimorphisms makes the
original coefficient restriction exact. -/
instance functor_preservesHomology : (functor S r).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- In particular, the original coefficient restriction preserves
finite colimits in the actual sheaf categories. -/
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor S r) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Actual short exact sequences remain short exact after restriction. -/
theorem map_shortExact
    (T : ShortComplex (Sheaf S.smallEtaleTopology (ModuleCat.{u} E')))
    (hT : T.ShortExact) : (T.map (functor S r)).ShortExact :=
  hT.map_of_exact (functor S r)

/-- The actual global-sections comparison is the identity on the
original section module equipped with restricted scalars. -/
def sectionsIso :
    functor S r ⋙ EtaleCohomology.sections S E ≅
      EtaleCohomology.sections S E' ⋙ ModuleCat.restrictScalars r :=
  Iso.refl _

/-- The comparison keeps the original section, without a normalization. -/
theorem sectionsIso_hom_app (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')) :
    (sectionsIso S r).hom.app F =
      𝟙 ((ModuleCat.restrictScalars r).obj ((EtaleCohomology.sections S E').obj F)) := rfl

/-- Its inverse is the same identity on the restricted section module. -/
theorem sectionsIso_inv_app (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')) :
    (sectionsIso S r).inv.app F =
      𝟙 ((ModuleCat.restrictScalars r).obj ((EtaleCohomology.sections S E').obj F)) := rfl

end Sheaves

section Affine

variable (R : Type u) [CommRing R]
  {E E' : Type u} [CommRing E] [CommRing E'] (r : E →+* E')

/-- The existing affine coefficient restriction is retained definitionally. -/
theorem functor_affine :
    functor (Spec (.of R)) r = etaleModuleCoefficientRestriction R r := rfl

end Affine

section Skyscrapers

variable (S : Scheme.{u}) {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')
  (Φ : GrothendieckTopology.Point.{u} S.smallEtaleTopology)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical preserved-product comparison is natural in the
actual étale object, including its action on geometric fiber indices. -/
def skyscraperPresheafIso (M : ModuleCat.{u} E') :
    Φ.skyscraperPresheaf M ⋙ ModuleCat.restrictScalars r ≅
      Φ.skyscraperPresheaf ((ModuleCat.restrictScalars r).obj M) :=
  NatIso.ofComponents
    (fun U => PreservesProduct.iso (ModuleCat.restrictScalars r)
      (fun _ : Φ.fiber.obj U.unop => M)) (by
        intro U V f
        apply Pi.hom_ext
        intro t
        change (ModuleCat.restrictScalars r).map
            (Pi.map' (Φ.fiber.map f.unop) (fun _ => 𝟙 M)) ≫
              piComparison (ModuleCat.restrictScalars r)
                (fun _ : Φ.fiber.obj V.unop => M) ≫ Pi.π _ t =
          piComparison (ModuleCat.restrictScalars r)
              (fun _ : Φ.fiber.obj U.unop => M) ≫
            Pi.map' (Φ.fiber.map f.unop) (fun _ => 𝟙 _) ≫ Pi.π _ t
        simp only [piComparison_comp_π, Pi.map'_comp_π, comp_id,
          ← CategoryTheory.Functor.map_comp])

set_option backward.isDefEq.respectTransparency false in
/-- The original single skyscraper commutes with coefficient restriction
by the actual product-preservation isomorphism on each étale object. -/
def skyscraperIso :
    EtaleSkyscraper.functor S Φ E' ⋙ functor S r ≅
      ModuleCat.restrictScalars r ⋙ EtaleSkyscraper.functor S Φ E :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ (skyscraperPresheafIso S r Φ M)) (by
      intro M N f
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply Pi.hom_ext
      intro t
      change (ModuleCat.restrictScalars r).map
          (CategoryTheory.Limits.Pi.map (fun _ : Φ.fiber.obj U.unop => f)) ≫
            piComparison (ModuleCat.restrictScalars r)
              (fun _ : Φ.fiber.obj U.unop => N) ≫ Pi.π _ t =
        piComparison (ModuleCat.restrictScalars r)
            (fun _ : Φ.fiber.obj U.unop => M) ≫
          CategoryTheory.Limits.Pi.map
            (fun _ : Φ.fiber.obj U.unop => (ModuleCat.restrictScalars r).map f) ≫ Pi.π _ t
      simp only [piComparison_comp_π, Pi.map_π,
        piComparison_comp_π_assoc, ← CategoryTheory.Functor.map_comp])

/-- The skyscraper comparison carries each original product projection
to that same projection with its coefficient scalars restricted. -/
theorem skyscraperIso_hom_app_π (M : ModuleCat.{u} E')
    (U : S.Etale) (t : Φ.fiber.obj U) :
    ((skyscraperIso S r Φ).hom.app M).hom.app (op U) ≫
        Pi.π (fun _ : Φ.fiber.obj U => (ModuleCat.restrictScalars r).obj M) t =
      (ModuleCat.restrictScalars r).map (Pi.π (fun _ : Φ.fiber.obj U => M) t) :=
  piComparison_comp_π (ModuleCat.restrictScalars r) (fun _ : Φ.fiber.obj U => M) t

/-- The inverse skyscraper comparison has the corresponding original
projection formula. -/
theorem skyscraperIso_inv_app_π (M : ModuleCat.{u} E')
    (U : S.Etale) (t : Φ.fiber.obj U) :
    ((skyscraperIso S r Φ).inv.app M).hom.app (op U) ≫
        (ModuleCat.restrictScalars r).map (Pi.π (fun _ : Φ.fiber.obj U => M) t) =
      Pi.π (fun _ : Φ.fiber.obj U => (ModuleCat.restrictScalars r).obj M) t := by
  change (PreservesProduct.iso (ModuleCat.restrictScalars r)
      (fun _ : Φ.fiber.obj U => M)).inv ≫ _ = _
  apply (Iso.inv_comp_eq _).mpr
  exact (piComparison_comp_π (ModuleCat.restrictScalars r)
    (fun _ : Φ.fiber.obj U => M) t).symm

end Skyscrapers

#print axioms scalar_preservesLimit
#print axioms scalar_preservesLimits
#print axioms scalar_preservesColimits
#print axioms functor
#print axioms functor_obj_obj
#print axioms functor_map_hom_app
#print axioms functor_preservesLimits
#print axioms functor_preservesFiniteLimits
#print axioms functor_additive
#print axioms functor_preservesEpimorphisms
#print axioms functor_preservesHomology
#print axioms functor_preservesFiniteColimits
#print axioms map_shortExact
#print axioms sectionsIso
#print axioms sectionsIso_hom_app
#print axioms sectionsIso_inv_app
#print axioms functor_affine
#print axioms skyscraperPresheafIso
#print axioms skyscraperIso
#print axioms skyscraperIso_hom_app_π
#print axioms skyscraperIso_inv_app_π

end PrimeGap182.TypeIII.EtaleCoefficientRestriction
