import TypeIIIEtaleSkyscraperExact
import TypeIIIDerivedBaseChangeIso
import TypeIIIDerivedBaseChangeZero
import TypeIIIExactResolutionQuasiIso
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Actual global cohomology of module skyscrapers

The global sections of the existing skyscraper are its original module:
the fiber of the identity étale object has one element, and the comparison
is projection to that element. Exactness and preservation of injectives
by the original skyscraper identify its global cohomology with the right
derived functors of the identity on modules. All positive degrees vanish,
without an injectivity hypothesis on the coefficient module.

The derived comparison is constructed from this actual projection and
retains the original augmentation square in degree zero.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleSkyscraper

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u})
  (Φ : GrothendieckTopology.Point.{u} S.smallEtaleTopology)
  (E : Type u) [Ring E]

/-- The unique actual element of the fiber of the identity étale object. -/
def terminalFiberElement : Φ.fiber.obj (EtaleCohomology.terminalObject S) :=
  (Φ.uniqueFiberObj _ (EtaleCohomology.terminal_isTerminal S)).default

/-- Every element of this actual terminal fiber is the specified one. -/
theorem terminalFiberElement_unique (x : Φ.fiber.obj (EtaleCohomology.terminalObject S)) :
    x = terminalFiberElement S Φ := by
  let : Unique (Φ.fiber.obj (EtaleCohomology.terminalObject S)) :=
    Φ.uniqueFiberObj _ (EtaleCohomology.terminal_isTerminal S)
  exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Literal global sections are the original module, by projection to
the unique actual terminal-fiber element. -/
def sectionsObjIso (M : ModuleCat.{u} E) :
    (EtaleCohomology.sections S E).obj ((functor S Φ E).obj M) ≅ M where
  hom := Pi.π (fun (_ : Φ.fiber.obj (EtaleCohomology.terminalObject S)) => M)
    (terminalFiberElement S Φ)
  inv := Pi.lift (fun (_ : Φ.fiber.obj (EtaleCohomology.terminalObject S)) => 𝟙 M)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    simp only [assoc, Pi.lift_π, comp_id, id_comp]
    rw [terminalFiberElement_unique S Φ i]
    rfl
  inv_hom_id := Pi.lift_π _ _

set_option backward.isDefEq.respectTransparency false in
/-- The original projection comparison is natural in the coefficient module. -/
def sectionsIso : functor S Φ E ⋙ EtaleCohomology.sections S E ≅ 𝟭 (ModuleCat.{u} E) :=
  NatIso.ofComponents (sectionsObjIso S Φ E) (fun {M N} f => by
    change CategoryTheory.Limits.Pi.map
        (fun (_ : Φ.fiber.obj (EtaleCohomology.terminalObject S)) => f) ≫
        Pi.π (fun (_ : Φ.fiber.obj (EtaleCohomology.terminalObject S)) => N)
          (terminalFiberElement S Φ) =
      Pi.π (fun (_ : Φ.fiber.obj (EtaleCohomology.terminalObject S)) => M)
        (terminalFiberElement S Φ) ≫ f
    exact Pi.map_π _ _)

/-- The forward map is literally the original product projection. -/
theorem sectionsIso_hom_app (M : ModuleCat.{u} E) :
    (sectionsIso S Φ E).hom.app M =
      Pi.π (fun (_ : Φ.fiber.obj (EtaleCohomology.terminalObject S)) => M)
        (terminalFiberElement S Φ) := rfl

/-- The ordinary comparison square supplied by that original projection. -/
def ordinarySquareIso :
    (𝟭 (ModuleCat.{u} E)) ⋙ (𝟭 (ModuleCat.{u} E)) ≅
      functor S Φ E ⋙ EtaleCohomology.sections S E :=
  Functor.leftUnitor (𝟭 (ModuleCat.{u} E)) ≪≫ (sectionsIso S Φ E).symm

/-- The existing derived comparison computes actual skyscraper cohomology
by the right derived identity functor on the original module category. -/
def cohomologyIso (n : ℕ) :
    (𝟭 (ModuleCat.{u} E)).rightDerived n ≅
      functor S Φ E ⋙ EtaleCohomology.functor S E n :=
  (Functor.rightUnitor ((𝟭 (ModuleCat.{u} E)).rightDerived n)).symm ≪≫
    derivedBaseChangeIso (𝟭 (ModuleCat.{u} E)) (EtaleCohomology.sections S E)
      (functor S Φ E) (𝟭 (ModuleCat.{u} E)) (ordinarySquareIso S Φ E).hom n

/-- Every original module skyscraper has zero positive global cohomology. -/
theorem isZero_cohomology_succ (n : ℕ) (M : ModuleCat.{u} E) :
    IsZero ((EtaleCohomology.functor S E (n + 1)).obj ((functor S Φ E).obj M)) :=
  (rightDerived_isZero_of_preservesHomology (𝟭 (ModuleCat.{u} E)) n M).of_iso
    ((cohomologyIso S Φ E (n + 1)).app M).symm

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero comparison retains the original projection and
the original maps to zeroth right derived functors. -/
theorem cohomologyIso_zero :
    (𝟭 (ModuleCat.{u} E)).toRightDerivedZero ≫ (cohomologyIso S Φ E 0).hom =
      (sectionsIso S Φ E).inv ≫
        Functor.whiskerLeft (functor S Φ E) (EtaleCohomology.sections S E).toRightDerivedZero := by
  have h := derivedBaseChangeMap_zero (𝟭 (ModuleCat.{u} E))
    (EtaleCohomology.sections S E) (functor S Φ E) (𝟭 (ModuleCat.{u} E))
    (ordinarySquareIso S Φ E).hom
  apply NatTrans.ext
  funext M
  simpa [cohomologyIso, ordinarySquareIso, derivedBaseChangeIso] using NatTrans.congr_app h M

#print axioms terminalFiberElement
#print axioms terminalFiberElement_unique
#print axioms sectionsObjIso
#print axioms sectionsIso
#print axioms sectionsIso_hom_app
#print axioms ordinarySquareIso
#print axioms cohomologyIso
#print axioms isZero_cohomology_succ
#print axioms cohomologyIso_zero

end PrimeGap182.TypeIII.EtaleSkyscraper
