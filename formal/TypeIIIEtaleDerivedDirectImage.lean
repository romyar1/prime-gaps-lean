import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import TypeIIIEtaleDirectImage
import TypeIIIKloostermanCompactification

/-!
# Injective resolutions and derived direct image on the small étale site

The category of module sheaves on the actual small étale site is
Grothendieck abelian.  Mathlib's enough-injectives theorem therefore
constructs injective resolutions of its objects; no resolution-existence
or exactness premise is supplied here.  Applying the actual small étale
direct-image functor to those resolutions and taking homology defines
its right derived functors.  Their degree-zero comparison is the
canonical isomorphism for the proved left-exact direct image.

For the unchanged Kloosterman phase family, the final functor is
Rⁿ barπ_* composed with the existing actual extension by zero j! into
the actual proper projective-plane model.  This constructs a sheaf on
the original parameter line.  It does not assert a fiberwise
compact-cohomology comparison, proper base change, a trace formula,
or any comparison with adic cohomology.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleDerivedDirectImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Resolutions

variable (S : Scheme.{u}) (E : Type u) [Ring E]

/-- The actual small étale module-sheaf category is Grothendieck abelian. -/
theorem isGrothendieckAbelian :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
  inferInstance

/-- Enough injectives follows from the proved Grothendieck-category construction. -/
theorem enoughInjectives :
    EnoughInjectives (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
  inferInstance

/-- Every actual small étale module sheaf admits an injective resolution. -/
theorem hasInjectiveResolutions :
    HasInjectiveResolutions (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
  inferInstance

/-- An actual injective resolution supplied by the enough-injectives construction. -/
def resolution (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    InjectiveResolution F :=
  CategoryTheory.injectiveResolution F

/-- Each object of the constructed cochain complex is injective. -/
theorem resolution_injective (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (n : ℕ) :
    Injective ((resolution S E F).cocomplex.X n) :=
  inferInstance

/-- The actual augmentation is a quasi-isomorphism. -/
theorem resolution_quasiIso (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    QuasiIso (resolution S E F).ι :=
  inferInstance

/-- Resolutions form the genuine functor to the homotopy category. -/
def resolutionFunctor :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤
      HomotopyCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (ComplexShape.up ℕ) :=
  CategoryTheory.injectiveResolutions _

end Resolutions

section DirectImage

variable {X S : Scheme.{u}} (q : X ⟶ S) (E : Type u) [Ring E]

/-- Actual direct image applied to the genuine injective-resolution functor. -/
def toHomotopyCategory :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} E) ⥤
      HomotopyCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (ComplexShape.up ℕ) :=
  (EtaleDirectImage.functor q E).rightDerivedToHomotopyCategory

/-- The actual nth right derived direct image, constructed with injective resolutions. -/
def functor (n : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  (EtaleDirectImage.functor q E).rightDerived n

/-- The definition literally takes homology after the actual resolution functor. -/
theorem functor_eq_resolution_homology (n : ℕ) :
    functor q E n =
      resolutionFunctor X E ⋙ (EtaleDirectImage.functor q E).mapHomotopyCategory _ ⋙
        HomotopyCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (ComplexShape.up ℕ) n := rfl

/-- Computation by the actual chosen injective resolution of the input sheaf. -/
def objIsoHomology (n : ℕ) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (functor q E n).obj F ≅
      (HomologicalComplex.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (ComplexShape.up ℕ) n).obj
          (((EtaleDirectImage.functor q E).mapHomologicalComplex _).obj
            (resolution X E F).cocomplex) :=
  (resolution X E F).isoRightDerivedObj (EtaleDirectImage.functor q E) n

/-- The canonical degree-zero comparison with the actual underived direct image. -/
def zeroIso : functor q E 0 ≅ EtaleDirectImage.functor q E :=
  (EtaleDirectImage.functor q E).rightDerivedZeroIsoSelf

/-- Its inverse is the canonical map induced by the actual resolution augmentation. -/
theorem zeroIso_inv :
    (zeroIso q E).inv = (EtaleDirectImage.functor q E).toRightDerivedZero := rfl

/-- Actual injective sheaves have zero higher right derived direct image. -/
theorem isZero_obj_injective_succ (n : ℕ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) [Injective F] :
    IsZero ((functor q E (n + 1)).obj F) :=
  (EtaleDirectImage.functor q E).isZero_rightDerived_obj_injective_succ n F

end DirectImage

end PrimeGap182.TypeIII.EtaleDerivedDirectImage

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) (E : Type) [Ring E]

/-- Rⁿ barπ_*(j!F) for the actual compactification of the unchanged phase family. -/
def kloostermanCompactifiedDerivedImage (n : ℕ) :
    Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E) ⥤
      Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology (ModuleCat.{0} E) :=
  kloostermanPhaseExtensionByZero p E ⋙
    EtaleDerivedDirectImage.functor (kloostermanCompactificationProjection p) E n

/-- Its value is literally the derived proper projection applied to the existing j!. -/
theorem kloostermanCompactifiedDerivedImage_obj (n : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    (kloostermanCompactifiedDerivedImage p E n).obj F =
      ((EtaleDirectImage.functor (kloostermanCompactificationProjection p) E).rightDerived n).obj
        ((kloostermanPhaseExtensionByZero p E).obj F) := rfl

/-- The actual canonical degree-zero isomorphism for the fixed compactification. -/
def kloostermanCompactifiedDerivedImage_zeroIso :
    kloostermanCompactifiedDerivedImage p E 0 ≅
      kloostermanPhaseExtensionByZero p E ⋙
        EtaleDirectImage.functor (kloostermanCompactificationProjection p) E :=
  Functor.isoWhiskerLeft (kloostermanPhaseExtensionByZero p E)
    (EtaleDerivedDirectImage.zeroIso (kloostermanCompactificationProjection p) E)

/-- Computation from the actual injective resolution of the extended sheaf on the proper model. -/
def kloostermanCompactifiedDerivedImage_objIsoHomology (n : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    (kloostermanCompactifiedDerivedImage p E n).obj F ≅
      (HomologicalComplex.homologyFunctor
        (Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology (ModuleCat.{0} E))
          (ComplexShape.up ℕ) n).obj
        (((EtaleDirectImage.functor (kloostermanCompactificationProjection p) E).mapHomologicalComplex
          _).obj
            (EtaleDerivedDirectImage.resolution (kloostermanCompactificationScheme p) E
              ((kloostermanPhaseExtensionByZero p E).obj F)).cocomplex) :=
  EtaleDerivedDirectImage.objIsoHomology (kloostermanCompactificationProjection p) E n
    ((kloostermanPhaseExtensionByZero p E).obj F)

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.isGrothendieckAbelian
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.enoughInjectives
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.hasInjectiveResolutions
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.resolution
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.resolution_injective
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.resolution_quasiIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.resolutionFunctor
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.toHomotopyCategory
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.functor
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.functor_eq_resolution_homology
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.objIsoHomology
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.zeroIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.zeroIso_inv
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.isZero_obj_injective_succ
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedImage
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedImage_obj
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedImage_zeroIso
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedImage_objIsoHomology
