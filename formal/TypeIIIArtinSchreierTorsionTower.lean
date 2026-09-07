import TypeIIIArtinSchreierCoefficientMaps
import TypeIIIArtinSchreierTorsionSheaf
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.CategoryTheory.Category.Preorder

/-!
# The actual tower of finite-coefficient Artin--Schreier sheaves

The transition maps are the actual character-image coefficient maps for
the proved cyclotomic reductions. After forgetting to additive sheaves,
they give an inverse system on the original small étale site.

This construction does not assert a tensor base-change isomorphism or
identify the system with an adic sheaf or a cohomology theory.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry

/-- Forgetting coefficients is a right adjoint: restrict to integers
and use the actual equivalence between integer modules and additive groups. -/
instance moduleForgetAb_rightAdjoint (E : Type) [CommRing E] :
    (forget₂ (ModuleCat.{0} E) AddCommGrpCat.{0}).IsRightAdjoint := by
  let e : ModuleCat.restrictScalars (Int.castRingHom E) ⋙
      forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0} ≅
        forget₂ (ModuleCat.{0} E) AddCommGrpCat.{0} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y g; rfl)
  exact Functor.isRightAdjoint_of_iso e

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
  {R : Type} [CommRing R] [CharP R p] (f : R)

/-- The actual finite-level coefficient reduction on character image sheaves. -/
def torsionArtinSchreierReduction {m n : ℕ} (hmn : m ≤ n) :
    torsionArtinSchreierSheaf p ell hne n f ⟶
      (etaleModuleCoefficientRestriction R (torsionCoefficientReduce p ell hmn)).obj
        (torsionArtinSchreierSheaf p ell hne m f) := by
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  let : Invertible (p : TorsionCoefficientRing p ell m) :=
    (torsionCoefficient_p_isUnit p ell m hne).invertible
  exact artinSchreierRingCharacterSheafCoefficientMap p f
    (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell m)
    (torsionCoefficientReduce p ell hmn)

set_option backward.isDefEq.respectTransparency.types false in
/-- Reduction from a coefficient level to itself is the identity on
every section of the actual sheaf. -/
theorem torsionArtinSchreierReduction_refl_apply (n : ℕ)
    (X : (Spec (.of R)).Etaleᵒᵖ)
    (x : (torsionArtinSchreierSheaf p ell hne n f).obj.obj X) :
    (torsionArtinSchreierReduction p ell hne f (le_refl n)).hom.app X x = x := by
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  change (artinSchreierRingCharacterSheafCoefficientMap p f
    (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell n)
    (torsionCoefficientReduce p ell (le_refl n))).hom.app X x = x
  rw [torsionCoefficientReduce_refl]
  exact congrArg (fun g => g.hom.app X x)
    (artinSchreierRingCharacterSheafCoefficientMap_id p f (torsionCoefficientChar p ell n))

set_option backward.isDefEq.respectTransparency.types false in
/-- Two actual coefficient reductions agree with direct reduction
on every section, using the proved character compatibility. -/
theorem torsionArtinSchreierReduction_comp_apply {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) (X : (Spec (.of R)).Etaleᵒᵖ)
    (x : (torsionArtinSchreierSheaf p ell hne n f).obj.obj X) :
    (torsionArtinSchreierReduction p ell hne f hkm).hom.app X
        ((torsionArtinSchreierReduction p ell hne f hmn).hom.app X x) =
      (torsionArtinSchreierReduction p ell hne f (hkm.trans hmn)).hom.app X x := by
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  let : Invertible (p : TorsionCoefficientRing p ell m) :=
    (torsionCoefficient_p_isUnit p ell m hne).invertible
  let : Invertible (p : TorsionCoefficientRing p ell k) :=
    (torsionCoefficient_p_isUnit p ell k hne).invertible
  have h := congrArg (fun g => g.hom.app X x)
    (artinSchreierRingCharacterSheafCoefficientMap_comp p f
      (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell m)
      (torsionCoefficientChar p ell k)
      (torsionCoefficientReduce p ell hmn) (torsionCoefficientReduce p ell hkm)
      (torsionCoefficientReduce_char p ell hmn)
      (torsionCoefficientReduce_char p ell hkm))
  change (artinSchreierRingCharacterSheafCoefficientMap p f
      (torsionCoefficientChar p ell m) (torsionCoefficientChar p ell k)
      (torsionCoefficientReduce p ell hkm)).hom.app X
        ((artinSchreierRingCharacterSheafCoefficientMap p f
          (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell m)
          (torsionCoefficientReduce p ell hmn)).hom.app X x) =
    (artinSchreierRingCharacterSheafCoefficientMap p f
      (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell k)
      ((torsionCoefficientReduce p ell hkm).comp
        (torsionCoefficientReduce p ell hmn))).hom.app X x at h
  rw [torsionCoefficientReduce_comp] at h
  exact h

/-- The underlying additive sheaf at the actual finite coefficient level. -/
abbrev torsionArtinSchreierAbSheaf (n : ℕ) :
    Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{0} :=
  (sheafCompose (Spec (.of R)).smallEtaleTopology
    (forget₂ (ModuleCat.{0} (TorsionCoefficientRing p ell n)) AddCommGrpCat.{0})).obj
      (torsionArtinSchreierSheaf p ell hne n f)

/-- Forgetting the actual coefficient reduction gives a morphism of
additive sheaves on the same site. -/
def torsionArtinSchreierAbReduction {m n : ℕ} (hmn : m ≤ n) :
    torsionArtinSchreierAbSheaf p ell hne f n ⟶
      torsionArtinSchreierAbSheaf p ell hne f m :=
  ⟨{ app X := AddCommGrpCat.ofHom
        ((torsionArtinSchreierReduction p ell hne f hmn).hom.app X).hom.toAddMonoidHom
     naturality {X Y} g := by
       ext x
       exact congrArg (fun h => h x)
         ((torsionArtinSchreierReduction p ell hne f hmn).hom.naturality g) }⟩

/-- The actual identity law in the fixed category of additive sheaves. -/
theorem torsionArtinSchreierAbReduction_refl (n : ℕ) :
    torsionArtinSchreierAbReduction p ell hne f (le_refl n) =
      𝟙 (torsionArtinSchreierAbSheaf p ell hne f n) := by
  apply Sheaf.hom_ext
  ext X x
  exact torsionArtinSchreierReduction_refl_apply p ell hne f n X x

/-- The actual composition law in the fixed category of additive sheaves. -/
theorem torsionArtinSchreierAbReduction_comp {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    torsionArtinSchreierAbReduction p ell hne f hmn ≫
        torsionArtinSchreierAbReduction p ell hne f hkm =
      torsionArtinSchreierAbReduction p ell hne f (hkm.trans hmn) := by
  apply Sheaf.hom_ext
  ext X x
  exact torsionArtinSchreierReduction_comp_apply p ell hne f hkm hmn X x

/-- The genuine inverse system of the finite-coefficient character sheaves,
with their actual additive reduction maps. -/
def torsionArtinSchreierAbTower :
    ℕᵒᵖ ⥤ Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{0} where
  obj n := torsionArtinSchreierAbSheaf p ell hne f n.unop
  map g := torsionArtinSchreierAbReduction p ell hne f (leOfHom g.unop)
  map_id n := torsionArtinSchreierAbReduction_refl p ell hne f n.unop
  map_comp g h := (torsionArtinSchreierAbReduction_comp p ell hne f
    (leOfHom h.unop) (leOfHom g.unop)).symm

#print axioms torsionArtinSchreierReduction
#print axioms moduleForgetAb_rightAdjoint
#print axioms torsionArtinSchreierReduction_refl_apply
#print axioms torsionArtinSchreierReduction_comp_apply
#print axioms torsionArtinSchreierAbSheaf
#print axioms torsionArtinSchreierAbReduction
#print axioms torsionArtinSchreierAbReduction_refl
#print axioms torsionArtinSchreierAbReduction_comp
#print axioms torsionArtinSchreierAbTower

end PrimeGap182.TypeIII
