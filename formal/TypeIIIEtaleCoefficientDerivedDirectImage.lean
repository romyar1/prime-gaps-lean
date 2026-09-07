import TypeIIIEtaleCoefficientCohomology
import TypeIIIEtaleSkyscraperFamilyDirectImage

/-!
# Coefficient restriction and the original relative derived direct image

The original direct image and coefficient restriction commute by their
literal section formulas.  Restricting the canonical Godement product
gives an actual product of skyscrapers, whose positive relative derived
direct images have been proved zero.  Mapping the actual injective
retract through these functors therefore proves the required acyclicity
of every restricted injective sheaf.

The existing acyclic-resolution criterion makes the original derived
comparison an isomorphism for every scheme morphism and every ring
homomorphism.  The same identity square and resolution augmentations
are retained in degree zero.  No properness, flatness, or preservation
of injectives by coefficient restriction is assumed.

This is an ordinary coefficient-category comparison.  It does not
assert proper base change or an adic inverse-limit comparison.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable {X S : Scheme.{u}} (q : X ⟶ S)
  {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- Direct image and coefficient restriction commute on the original
section modules over the same literal base-changed étale objects. -/
def directImageIso :
    EtaleDirectImage.functor q E' ⋙ functor S r ≅
      functor X r ⋙ EtaleDirectImage.functor q E :=
  Iso.refl _

/-- The ordinary comparison is the original identity on the restricted
direct-image sheaf. -/
theorem directImageIso_hom_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E')) :
    (directImageIso q r).hom.app F =
      𝟙 ((functor S r).obj ((EtaleDirectImage.functor q E').obj F)) := rfl

/-- The actual restricted Godement product is acyclic for the original
direct-image functor along any scheme morphism. -/
theorem isZero_derived_succ_restrict_godement (n : ℕ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E')) :
    IsZero ((EtaleDerivedDirectImage.functor q E (n + 1)).obj
      ((functor X r).obj (EtaleGodement.obj X E' F))) := by
  let M := (EtaleSkyscraperFamily.stalks X (algebraicClosureEtalePoint X) E').obj F
  exact (EtaleSkyscraperFamilyDirectImage.algebraicClosure_isZero_derived_succ q E n
    ((EtaleCoefficientSkyscraperFamily.diagramRestriction r).obj M)).of_iso
      ((EtaleDerivedDirectImage.functor q E (n + 1)).mapIso
        (EtaleCoefficientSkyscraperFamily.objIso X r (algebraicClosureEtalePoint X) M))

/-- The mapped original injective retract proves relative acyclicity
after arbitrary restriction of coefficient rings. -/
theorem isZero_derived_succ_restrict_injective (n : ℕ)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} E')) [Injective J] :
    IsZero ((EtaleDerivedDirectImage.functor q E (n + 1)).obj ((functor X r).obj J)) := by
  let t := ((EtaleGodement.injectiveRetract X E' J).map (functor X r)).map
    (EtaleDerivedDirectImage.functor q E (n + 1))
  have ht := isZero_derived_succ_restrict_godement q r n J
  apply (IsZero.iff_id_eq_zero _).2
  rw [← t.retract, ht.eq_zero_of_tgt t.i, zero_comp]

/-- The original derived transformation for the literal coefficient
restriction square of the original direct-image functors. -/
def derivedDirectImageMap (n : ℕ) :
    EtaleDerivedDirectImage.functor q E' n ⋙ functor S r ⟶
      functor X r ⋙ EtaleDerivedDirectImage.functor q E n :=
  derivedBaseChangeMap (EtaleDirectImage.functor q E') (EtaleDirectImage.functor q E)
    (functor X r) (functor S r) (directImageIso q r).hom n

/-- The proved relative acyclicity discharges every premise of the
acyclic-resolution criterion for this same derived map. -/
theorem derivedDirectImageMap_isIso (n : ℕ) : IsIso (derivedDirectImageMap q r n) := by
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
  let := HasDerivedCategory.standard (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
  exact derivedBaseChangeMap_isIso_of_acyclic
    (EtaleDirectImage.functor q E') (EtaleDirectImage.functor q E)
    (functor X r) (functor S r) (directImageIso q r).hom
    (fun J hJ m => by
      let : Injective J := hJ
      exact isZero_derived_succ_restrict_injective q r m J) n

/-- The original relative derived direct images commute with arbitrary
restriction of coefficient rings. -/
def derivedDirectImageIso (n : ℕ) :
    EtaleDerivedDirectImage.functor q E' n ⋙ functor S r ≅
      functor X r ⋙ EtaleDerivedDirectImage.functor q E n := by
  have : IsIso (derivedDirectImageMap q r n) := derivedDirectImageMap_isIso q r n
  exact asIso (derivedDirectImageMap q r n)

/-- The packaged isomorphism has precisely the original forward map. -/
theorem derivedDirectImageIso_hom (n : ℕ) :
    (derivedDirectImageIso q r n).hom = derivedDirectImageMap q r n := rfl

/-- Degree zero retains the literal ordinary coefficient square and
the canonical augmentations to the original right derived functors. -/
theorem derivedDirectImageMap_zero :
    Functor.whiskerRight (EtaleDirectImage.functor q E').toRightDerivedZero
        (functor S r) ≫ derivedDirectImageMap q r 0 =
      (directImageIso q r).hom ≫ Functor.whiskerLeft (functor X r)
        (EtaleDirectImage.functor q E).toRightDerivedZero :=
  derivedBaseChangeMap_zero (EtaleDirectImage.functor q E') (EtaleDirectImage.functor q E)
    (functor X r) (functor S r) (directImageIso q r).hom

/-- The same degree-zero square holds for the canonical isomorphism. -/
theorem derivedDirectImageIso_zero :
    Functor.whiskerRight (EtaleDirectImage.functor q E').toRightDerivedZero
        (functor S r) ≫ (derivedDirectImageIso q r 0).hom =
      (directImageIso q r).hom ≫ Functor.whiskerLeft (functor X r)
        (EtaleDirectImage.functor q E).toRightDerivedZero :=
  derivedDirectImageMap_zero q r

#print axioms directImageIso
#print axioms directImageIso_hom_app
#print axioms isZero_derived_succ_restrict_godement
#print axioms isZero_derived_succ_restrict_injective
#print axioms derivedDirectImageMap
#print axioms derivedDirectImageMap_isIso
#print axioms derivedDirectImageIso
#print axioms derivedDirectImageIso_hom
#print axioms derivedDirectImageMap_zero
#print axioms derivedDirectImageIso_zero

end PrimeGap182.TypeIII.EtaleCoefficientRestriction
