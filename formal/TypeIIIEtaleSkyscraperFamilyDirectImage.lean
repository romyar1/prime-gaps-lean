import TypeIIIEtaleSkyscraperDirectImage
import TypeIIIEtaleSkyscraperFamilyCohomology
import TypeIIIEtaleDerivedDirectImage

/-!
# Actual derived direct image of geometric skyscraper products

For a small family of separably closed geometric points of X, the
original direct image under any q : X → S takes the actual skyscraper
product to the product at the composed geometric points.  The
comparison is the preserved-product isomorphism followed by the
original single-skyscraper comparisons, and retains the original
product projections.

The skyscraper-product functors on X and S are already proved exact,
and the one on X preserves injectives.  The existing derived comparison
therefore identifies the actual derived direct image of such products
with the derived functors of the exact product on S.  All positive
degrees vanish for arbitrary coefficient diagrams.  No injectivity or
acyclicity of the coefficient diagram is assumed, and q is arbitrary.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleSkyscraperFamilyDirectImage

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

section GeometricFamily

variable {X S : Scheme.{u}} (q : X ⟶ S)
  {ι : Type u} {K : ι → Type u} [∀ i, Field (K i)] [∀ i, IsSepClosed (K i)]
  (s : ∀ i, Spec (.of (K i)) ⟶ X) (E : Type u) [Ring E]

/-- The original family of actual geometric points of X. -/
def sourcePoints : ι → GrothendieckTopology.Point.{u} X.smallEtaleTopology :=
  fun i => Scheme.pointSmallEtale (s i)

/-- The family of actual geometric points after composition with q. -/
def targetPoints : ι → GrothendieckTopology.Point.{u} S.smallEtaleTopology :=
  fun i => Scheme.pointSmallEtale (s i ≫ q)

/-- Direct image of the original product is the original product at
the composed points, using preservation of actual small products. -/
def objIso (M : Discrete ι ⥤ ModuleCat.{u} E) :
    (EtaleDirectImage.functor q E).obj
        ((EtaleSkyscraperFamily.functor X (sourcePoints s) E).obj M) ≅
      (EtaleSkyscraperFamily.functor S (targetPoints q s) E).obj M :=
  PreservesProduct.iso (EtaleDirectImage.functor q E)
      (EtaleSkyscraperFamily.skyscrapers X (sourcePoints s) E M) ≪≫
    Limits.Pi.mapIso
      (f := fun i => (EtaleDirectImage.functor q E).obj
        (EtaleSkyscraperFamily.skyscrapers X (sourcePoints s) E M i))
      (g := EtaleSkyscraperFamily.skyscrapers S (targetPoints q s) E M)
      (fun i => (EtaleSkyscraperDirectImage.iso q (s i) E).app (M.obj ⟨i⟩))

/-- Each projection is the direct image of the original product
projection followed by the original single-skyscraper comparison. -/
@[reassoc (attr := simp)]
theorem objIso_hom_π (M : Discrete ι ⥤ ModuleCat.{u} E) (i : ι) :
    (objIso q s E M).hom ≫
        Pi.π (EtaleSkyscraperFamily.skyscrapers S (targetPoints q s) E M) i =
      (EtaleDirectImage.functor q E).map
          (Pi.π (EtaleSkyscraperFamily.skyscrapers X (sourcePoints s) E M) i) ≫
        (EtaleSkyscraperDirectImage.iso q (s i) E).hom.app (M.obj ⟨i⟩) := by
  simp only [objIso, Iso.trans_hom, assoc, Limits.Pi.mapIso_hom_π,
    PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  rfl

/-- The inverse comparison retains the corresponding original
product projection and inverse single-skyscraper comparison. -/
@[reassoc (attr := simp)]
theorem objIso_inv_π (M : Discrete ι ⥤ ModuleCat.{u} E) (i : ι) :
    (objIso q s E M).inv ≫
        (EtaleDirectImage.functor q E).map
          (Pi.π (EtaleSkyscraperFamily.skyscrapers X (sourcePoints s) E M) i) =
      Pi.π (EtaleSkyscraperFamily.skyscrapers S (targetPoints q s) E M) i ≫
        (EtaleSkyscraperDirectImage.iso q (s i) E).inv.app (M.obj ⟨i⟩) := by
  apply (Iso.inv_comp_eq (objIso q s E M)).mpr
  rw [← assoc, objIso_hom_π]
  simp only [assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- The comparison commutes with the original coefficient-diagram maps. -/
theorem objIso_naturality {M N : Discrete ι ⥤ ModuleCat.{u} E} (f : M ⟶ N) :
    (EtaleDirectImage.functor q E).map
          ((EtaleSkyscraperFamily.functor X (sourcePoints s) E).map f) ≫
        (objIso q s E N).hom =
      (objIso q s E M).hom ≫
        (EtaleSkyscraperFamily.functor S (targetPoints q s) E).map f := by
  apply Pi.hom_ext
  intro i
  simp only [assoc, objIso_hom_π, EtaleSkyscraperFamily.functor_map_π,
    objIso_hom_π_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, EtaleSkyscraperFamily.functor_map_π,
    CategoryTheory.Functor.map_comp, assoc]
  exact congrArg
    (fun k => (EtaleDirectImage.functor q E).map
      (Pi.π (EtaleSkyscraperFamily.skyscrapers X (sourcePoints s) E M) i) ≫ k)
    ((EtaleSkyscraperDirectImage.iso q (s i) E).hom.naturality (f.app ⟨i⟩))

/-- Direct image of the original family functor is the original family
functor at the composed geometric points. -/
def familyIso :
    EtaleSkyscraperFamily.functor X (sourcePoints s) E ⋙ EtaleDirectImage.functor q E ≅
      EtaleSkyscraperFamily.functor S (targetPoints q s) E :=
  NatIso.ofComponents (objIso q s E) (fun f => objIso_naturality q s E f)

/-- The forward component is the actual preserved-product comparison. -/
theorem familyIso_hom_app (M : Discrete ι ⥤ ModuleCat.{u} E) :
    (familyIso q s E).hom.app M = (objIso q s E M).hom := rfl

/-- The inverse component is the inverse of that same comparison. -/
theorem familyIso_inv_app (M : Discrete ι ⥤ ModuleCat.{u} E) :
    (familyIso q s E).inv.app M = (objIso q s E M).inv := rfl

/-- The ordinary square supplied to the existing derived comparison
is precisely the inverse of the proved original product comparison. -/
def ordinarySquareIso :
    EtaleSkyscraperFamily.functor S (targetPoints q s) E ⋙
        𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) ≅
      EtaleSkyscraperFamily.functor X (sourcePoints s) E ⋙ EtaleDirectImage.functor q E :=
  Functor.rightUnitor _ ≪≫ (familyIso q s E).symm

/-- The actual derived direct image of the original product is
computed by the derived functor of the proved exact product on S. -/
def derivedIso (n : ℕ) :
    (EtaleSkyscraperFamily.functor S (targetPoints q s) E).rightDerived n ≅
      EtaleSkyscraperFamily.functor X (sourcePoints s) E ⋙
        EtaleDerivedDirectImage.functor q E n :=
  (Functor.rightUnitor _).symm ≪≫
    derivedBaseChangeIso (EtaleSkyscraperFamily.functor S (targetPoints q s) E)
      (EtaleDirectImage.functor q E) (EtaleSkyscraperFamily.functor X (sourcePoints s) E)
      (𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))) (ordinarySquareIso q s E).hom n

/-- Every actual skyscraper product has zero positive derived direct
image, without an injectivity or acyclicity premise on its coefficients. -/
theorem isZero_derived_succ (n : ℕ) (M : Discrete ι ⥤ ModuleCat.{u} E) :
    IsZero ((EtaleDerivedDirectImage.functor q E (n + 1)).obj
      ((EtaleSkyscraperFamily.functor X (sourcePoints s) E).obj M)) :=
  (rightDerived_isZero_of_preservesHomology
    (EtaleSkyscraperFamily.functor S (targetPoints q s) E) n M).of_iso
      ((derivedIso q s E (n + 1)).app M).symm

/-- Degree zero retains the actual product comparison and the
original resolution augmentation into the zeroth derived direct image. -/
theorem derivedIso_zero :
    (EtaleSkyscraperFamily.functor S (targetPoints q s) E).toRightDerivedZero ≫
        (derivedIso q s E 0).hom =
      (familyIso q s E).inv ≫
        Functor.whiskerLeft (EtaleSkyscraperFamily.functor X (sourcePoints s) E)
          (EtaleDirectImage.functor q E).toRightDerivedZero := by
  have h := derivedBaseChangeMap_zero
    (EtaleSkyscraperFamily.functor S (targetPoints q s) E)
    (EtaleDirectImage.functor q E) (EtaleSkyscraperFamily.functor X (sourcePoints s) E)
    (𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))) (ordinarySquareIso q s E).hom
  apply NatTrans.ext
  funext M
  simpa [derivedIso, ordinarySquareIso, derivedBaseChangeIso] using NatTrans.congr_app h M

end GeometricFamily

section AlgebraicClosureFamily

variable {X S : Scheme.{u}} (q : X ⟶ S) (E : Type u) [Ring E]

/-- The actual canonical algebraic-closure point family has the same
direct-image comparison, with every point map explicitly composed with q. -/
def algebraicClosureFamilyIso :
    EtaleSkyscraperFamily.functor X (algebraicClosureEtalePoint X) E ⋙
        EtaleDirectImage.functor q E ≅
      EtaleSkyscraperFamily.functor S
        (fun x : X => Scheme.pointSmallEtale (algebraicClosureEtalePointMap X x ≫ q)) E :=
  familyIso q (algebraicClosureEtalePointMap X) E

/-- The product attached to the actual conservative algebraic-closure
point family has zero positive derived direct image for every diagram. -/
theorem algebraicClosure_isZero_derived_succ (n : ℕ)
    (M : Discrete X ⥤ ModuleCat.{u} E) :
    IsZero ((EtaleDerivedDirectImage.functor q E (n + 1)).obj
      ((EtaleSkyscraperFamily.functor X (algebraicClosureEtalePoint X) E).obj M)) :=
  isZero_derived_succ q (algebraicClosureEtalePointMap X) E n M

end AlgebraicClosureFamily

#print axioms sourcePoints
#print axioms targetPoints
#print axioms objIso
#print axioms objIso_hom_π
#print axioms objIso_hom_π_assoc
#print axioms objIso_inv_π
#print axioms objIso_inv_π_assoc
#print axioms objIso_naturality
#print axioms familyIso
#print axioms familyIso_hom_app
#print axioms familyIso_inv_app
#print axioms ordinarySquareIso
#print axioms derivedIso
#print axioms isZero_derived_succ
#print axioms derivedIso_zero
#print axioms algebraicClosureFamilyIso
#print axioms algebraicClosure_isZero_derived_succ

end PrimeGap182.TypeIII.EtaleSkyscraperFamilyDirectImage
