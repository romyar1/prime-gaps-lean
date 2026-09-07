import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Coefficient change preserves the stalk support of module-valued sheaves

Restriction of scalars through a ring isomorphism is an equivalence of
module categories.  Composing an actual sheaf with this equivalence
commutes with the fiber functor of a point of its site.  Consequently a
stalk is zero before coefficient change exactly when it is zero afterwards.

The support here is the set of points of the site with nonzero fiber.
No assertion about Fourier transform, perverse cohomology, or dilation
invariance is made.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u uR uS

namespace PrimeGap182.TypeIII.CoefficientSheafSupport

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Coefficient change on actual module-valued sheaves, obtained by
composing with the module equivalence induced by a ring isomorphism. -/
def changeCoefficients (e : R ≃+* S) :
    Sheaf J (ModuleCat.{w} S) ⥤ Sheaf J (ModuleCat.{w} R) :=
  sheafCompose J (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor

/-- Restriction through a ring isomorphism does not change whether a
module is a zero object. -/
theorem isZero_restrictCoefficients_iff (e : R ≃+* S) (M : ModuleCat.{w} S) :
    IsZero ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.obj M) ↔
      IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

/-- The support defined using the actual fibers at points of a site. -/
def stalkSupport (F : Sheaf J (ModuleCat.{w} R)) :
    Set (GrothendieckTopology.Point.{w} J) :=
  {Φ | ¬ IsZero (Φ.sheafFiber.obj F)}

variable [LocallySmall.{w} C]

/-- Taking a stalk commutes with coefficient change.  This is Mathlib's
fiber-composition isomorphism specialized to the module equivalence. -/
def stalkIso (e : R ≃+* S) (Φ : GrothendieckTopology.Point.{w} J)
    (F : Sheaf J (ModuleCat.{w} S)) :
    (Φ.sheafFiber (A := ModuleCat.{w} R)).obj ((changeCoefficients J e).obj F) ≅
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
        ModuleCat.{w} S ≌ ModuleCat.{w} R).functor.obj
        ((Φ.sheafFiber (A := ModuleCat.{w} S)).obj F) :=
  (Φ.sheafFiberCompIso
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
      ModuleCat.{w} S ≌ ModuleCat.{w} R).functor).app F

/-- Zero stalks are preserved and reflected by coefficient change. -/
theorem isZero_stalk_iff (e : R ≃+* S) (Φ : GrothendieckTopology.Point.{w} J)
    (F : Sheaf J (ModuleCat.{w} S)) :
    IsZero (Φ.sheafFiber.obj ((changeCoefficients J e).obj F)) ↔
      IsZero (Φ.sheafFiber.obj F) :=
  (stalkIso J e Φ F).isZero_iff.trans
    (isZero_restrictCoefficients_iff e (Φ.sheafFiber.obj F))

/-- Nonzero stalks are preserved and reflected by coefficient change. -/
theorem nonzero_stalk_iff (e : R ≃+* S) (Φ : GrothendieckTopology.Point.{w} J)
    (F : Sheaf J (ModuleCat.{w} S)) :
    (¬ IsZero (Φ.sheafFiber.obj ((changeCoefficients J e).obj F))) ↔
      ¬ IsZero (Φ.sheafFiber.obj F) :=
  not_congr (isZero_stalk_iff J e Φ F)

/-- Coefficient change preserves the support as a set of points of the
site, with no support-invariance hypothesis. -/
theorem stalkSupport_changeCoefficients (e : R ≃+* S)
    (F : Sheaf J (ModuleCat.{w} S)) :
    stalkSupport J ((changeCoefficients J e).obj F) = stalkSupport J F := by
  ext Φ
  exact nonzero_stalk_iff J e Φ F

end

end PrimeGap182.TypeIII.CoefficientSheafSupport

#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.changeCoefficients
#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.isZero_restrictCoefficients_iff
#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.stalkSupport
#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.stalkIso
#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.isZero_stalk_iff
#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.nonzero_stalk_iff
#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.stalkSupport_changeCoefficients
