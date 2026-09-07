import TypeIIIArtinSchreierTorsionBaseChange
import TypeIIITorsionCoefficientLimit

/-!
# The character sheaf over the actual coefficient limit

The existing inverse-limit ring, with its actual primitive character and
inverse of p, supplies an ordinary module-valued character sheaf. Its
canonical tensor extension to each finite coefficient ring is the original
finite-level sheaf. The adjoint maps agree with the existing reductions.

Restricting every finite level along its actual projection from the limit
ring gives an inverse system in one category of module sheaves. The
original limit-coefficient sheaf has a compatible cone to that system.
No identification of this cone as a categorical limit, or comparison of
ordinary sheaf cohomology with adic cohomology, is asserted here.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
  {R : Type} [CommRing R] [CharP R p] (f : R)

/-- The original character-image construction over the actual limit ring. -/
def limitArtinSchreierSheaf :
    Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{0} (TorsionCoefficientLimit p ell)) :=
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  artinSchreierRingCharacterImageSheaf p f (TorsionCoefficientLimit p ell)
    (torsionCoefficientLimitChar p ell)

/-- The same finite étale cover trivializes the limit-coefficient sheaf. -/
def limitArtinSchreierLocalTrivialization :
    (limitArtinSchreierSheaf p ell hne f).over (artinSchreierEtaleObject p f) ≅
      (constantSheaf ((Spec (.of R)).smallEtaleTopology.over
        (artinSchreierEtaleObject p f)) (ModuleCat.{0} (TorsionCoefficientLimit p ell))).obj
          (ModuleCat.of (TorsionCoefficientLimit p ell) (TorsionCoefficientLimit p ell)) := by
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  exact artinSchreierRingCharacterLocalTrivialization p f
    (TorsionCoefficientLimit p ell) (torsionCoefficientLimitChar p ell)

/-- The finite-level sheaf with scalars restricted along the actual projection. -/
abbrev torsionArtinSchreierLimitModuleSheaf (n : ℕ) :
    Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{0} (TorsionCoefficientLimit p ell)) :=
  (etaleModuleCoefficientRestriction R (torsionCoefficientLimitProjection p ell n)).obj
    (torsionArtinSchreierSheaf p ell hne n f)

/-- The actual character coefficient map from the limit to a finite level. -/
def limitArtinSchreierReduction (n : ℕ) :
    limitArtinSchreierSheaf p ell hne f ⟶
      torsionArtinSchreierLimitModuleSheaf p ell hne f n := by
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  exact artinSchreierRingCharacterSheafCoefficientMap p f
    (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell n)
    (torsionCoefficientLimitProjection p ell n)

/-- Tensor extension along the actual limit projection recovers the original finite sheaf. -/
def limitArtinSchreierReductionIso (n : ℕ) :
    (etaleModuleCoefficientExtension R (torsionCoefficientLimitProjection p ell n)).obj
        (limitArtinSchreierSheaf p ell hne f) ≅
      torsionArtinSchreierSheaf p ell hne n f := by
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  exact artinSchreierRingCharacterSheafCoefficientExtensionIso p f
    (torsionCoefficientLimitProjection p ell n)
    (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell n)
    (torsionCoefficientLimitProjection_char p ell n)

/-- The tensor comparison has exactly the original coefficient map as its adjoint. -/
theorem limitArtinSchreierReductionIso_mate (n : ℕ) :
    (etaleModuleCoefficientAdjunction R (torsionCoefficientLimitProjection p ell n)).homEquiv _ _
        (limitArtinSchreierReductionIso p ell hne f n).hom =
      limitArtinSchreierReduction p ell hne f n := by
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  exact artinSchreierRingCharacterSheafCoefficientExtensionIso_mate p f
    (torsionCoefficientLimitProjection p ell n)
    (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell n)
    (torsionCoefficientLimitProjection_char p ell n)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original finite reduction is linear over the actual coefficient limit. -/
def torsionArtinSchreierLimitModuleReduction {m n : ℕ} (hmn : m ≤ n) :
    torsionArtinSchreierLimitModuleSheaf p ell hne f n ⟶
      torsionArtinSchreierLimitModuleSheaf p ell hne f m :=
  ⟨{ app X := ModuleCat.ofHom
        (X := (torsionArtinSchreierLimitModuleSheaf p ell hne f n).obj.obj X)
        (Y := (torsionArtinSchreierLimitModuleSheaf p ell hne f m).obj.obj X)
        { toFun := (torsionArtinSchreierReduction p ell hne f hmn).hom.app X
          map_add' := fun x y => map_add _ x y
          map_smul' := by
            intro a x
            have h := ((torsionArtinSchreierReduction p ell hne f hmn).hom.app X).hom.map_smul
              (torsionCoefficientLimitProjection p ell n a) x
            change (torsionArtinSchreierReduction p ell hne f hmn).hom.app X
                (torsionCoefficientLimitProjection p ell n a •
                  (show (torsionArtinSchreierSheaf p ell hne n f).obj.obj X from x)) =
              torsionCoefficientReduce p ell hmn (torsionCoefficientLimitProjection p ell n a) •
                (show (torsionArtinSchreierSheaf p ell hne m f).obj.obj X from
                  (torsionArtinSchreierReduction p ell hne f hmn).hom.app X x) at h
            change (torsionArtinSchreierReduction p ell hne f hmn).hom.app X
                (torsionCoefficientLimitProjection p ell n a •
                  (show (torsionArtinSchreierSheaf p ell hne n f).obj.obj X from x)) =
              torsionCoefficientLimitProjection p ell m a •
                (show (torsionArtinSchreierSheaf p ell hne m f).obj.obj X from
                  (torsionArtinSchreierReduction p ell hne f hmn).hom.app X x)
            rw [show torsionCoefficientReduce p ell hmn
                (torsionCoefficientLimitProjection p ell n a) =
                torsionCoefficientLimitProjection p ell m a from
              RingHom.congr_fun (torsionCoefficientLimitProjection_compatible p ell hmn) a] at h
            exact h }
     naturality {X Y} g := by
       ext x
       exact congrArg (fun h => h x)
         ((torsionArtinSchreierReduction p ell hne f hmn).hom.naturality g) }⟩

/-- Restricting scalars retains the actual identity reduction. -/
theorem torsionArtinSchreierLimitModuleReduction_refl (n : ℕ) :
    torsionArtinSchreierLimitModuleReduction p ell hne f (le_refl n) =
      𝟙 (torsionArtinSchreierLimitModuleSheaf p ell hne f n) := by
  apply Sheaf.hom_ext
  ext X x
  exact torsionArtinSchreierReduction_refl_apply p ell hne f n X x

/-- The actual finite reductions compose in the fixed limit-module category. -/
theorem torsionArtinSchreierLimitModuleReduction_comp {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    torsionArtinSchreierLimitModuleReduction p ell hne f hmn ≫
        torsionArtinSchreierLimitModuleReduction p ell hne f hkm =
      torsionArtinSchreierLimitModuleReduction p ell hne f (hkm.trans hmn) := by
  apply Sheaf.hom_ext
  ext X x
  exact torsionArtinSchreierReduction_comp_apply p ell hne f hkm hmn X x

/-- The original finite-level system in one category of limit-ring module sheaves. -/
def torsionArtinSchreierLimitModuleTower :
    ℕᵒᵖ ⥤ Sheaf (Spec (.of R)).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) where
  obj n := torsionArtinSchreierLimitModuleSheaf p ell hne f n.unop
  map g := torsionArtinSchreierLimitModuleReduction p ell hne f (leOfHom g.unop)
  map_id n := torsionArtinSchreierLimitModuleReduction_refl p ell hne f n.unop
  map_comp g h := (torsionArtinSchreierLimitModuleReduction_comp p ell hne f
    (leOfHom h.unop) (leOfHom g.unop)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual maps out of the limit-coefficient sheaf respect every finite reduction. -/
theorem limitArtinSchreierReduction_comp {m n : ℕ} (hmn : m ≤ n) :
    limitArtinSchreierReduction p ell hne f n ≫
        torsionArtinSchreierLimitModuleReduction p ell hne f hmn =
      limitArtinSchreierReduction p ell hne f m := by
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  let : Invertible (p : TorsionCoefficientRing p ell m) :=
    (torsionCoefficient_p_isUnit p ell m hne).invertible
  apply Sheaf.hom_ext
  ext X x
  have h := congrArg (fun g => g.hom.app X x)
    (artinSchreierRingCharacterSheafCoefficientMap_comp p f
      (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell n)
      (torsionCoefficientChar p ell m)
      (torsionCoefficientLimitProjection p ell n) (torsionCoefficientReduce p ell hmn)
      (torsionCoefficientLimitProjection_char p ell n)
      (torsionCoefficientReduce_char p ell hmn))
  change (artinSchreierRingCharacterSheafCoefficientMap p f
      (torsionCoefficientChar p ell n) (torsionCoefficientChar p ell m)
      (torsionCoefficientReduce p ell hmn)).hom.app X
        ((artinSchreierRingCharacterSheafCoefficientMap p f
          (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell n)
          (torsionCoefficientLimitProjection p ell n)).hom.app X x) =
    (artinSchreierRingCharacterSheafCoefficientMap p f
      (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell m)
      ((torsionCoefficientReduce p ell hmn).comp
        (torsionCoefficientLimitProjection p ell n))).hom.app X x at h
  rw [torsionCoefficientLimitProjection_compatible] at h
  exact h

/-- A compatible cone from the actual limit-coefficient sheaf to its finite reductions. -/
def limitArtinSchreierCone : Cone (torsionArtinSchreierLimitModuleTower p ell hne f) where
  pt := limitArtinSchreierSheaf p ell hne f
  π :=
    { app n := limitArtinSchreierReduction p ell hne f n.unop
      naturality n m g := by
        change 𝟙 _ ≫ limitArtinSchreierReduction p ell hne f m.unop =
          limitArtinSchreierReduction p ell hne f n.unop ≫
            torsionArtinSchreierLimitModuleReduction p ell hne f (leOfHom g.unop)
        rw [Category.id_comp, limitArtinSchreierReduction_comp] }

#print axioms limitArtinSchreierSheaf
#print axioms limitArtinSchreierLocalTrivialization
#print axioms torsionArtinSchreierLimitModuleSheaf
#print axioms limitArtinSchreierReduction
#print axioms limitArtinSchreierReductionIso
#print axioms limitArtinSchreierReductionIso_mate
#print axioms torsionArtinSchreierLimitModuleReduction
#print axioms torsionArtinSchreierLimitModuleReduction_refl
#print axioms torsionArtinSchreierLimitModuleReduction_comp
#print axioms torsionArtinSchreierLimitModuleTower
#print axioms limitArtinSchreierReduction_comp
#print axioms limitArtinSchreierCone

end PrimeGap182.TypeIII
