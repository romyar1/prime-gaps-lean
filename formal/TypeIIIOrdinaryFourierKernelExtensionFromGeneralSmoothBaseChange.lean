import TypeIIIOrdinaryOpenExtensionsFromAdjunctions
import TypeIIIRelativeAffineFourierKernelRestrictionFromInverseImages
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
Ordinary open pushforward followed by a pullback/tensor kernel is computed
from two general MODEL theorem families: smooth open base change and the
ordinary projection formula with a globally lisse tensor factor. Both
families precede every selected field, square, kernel, and source object.
The actual Fourier coordinate square and its smoothness are separate
geometric obligations; a commuting square alone is insufficient. No exactness
of ordinary open pushforward, complete Inputs, or selected Fourier comparison
is assumed. The supplied ordinary coefficient model remains explicit.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MonoidalCategory
namespace PrimeGap182.TypeIII.OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward
open OrdinaryOpenExtensionsFromAdjunctions

universe mu
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  (F : OrdinaryOpenFamily C U)
  (L : ∀ X : Scheme, ObjectProperty (C X))

/-- Smooth base change on every genuine aligned open square, at degree zero.
Recognition of the supplied rational/adic model is external. -/
abbrev UniversalSmoothOpenBaseChange :=
  ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y X' Y' : Scheme}
    (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
    (PX' : FieldPresentation K X') (PY' : FieldPresentation K Y')
    (j : X ⟶ Y) (j' : X' ⟶ Y') (f : Y' ⟶ Y) (f' : X' ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] [Smooth f]
    (hj : j ≫ PY.structureMorphism = PX.structureMorphism)
    (hj' : j' ≫ PY'.structureMorphism = PX'.structureMorphism)
    (_hf : f ≫ PY.structureMorphism = PY'.structureMorphism)
    (_hf' : f' ≫ PX.structureMorphism = PX'.structureMorphism)
    (_square : IsPullback f' j' j f),
    F.push K h2 PX PY j hj ⋙ U.pull f ≅
      U.pull f' ⋙ F.push K h2 PX' PY' j' hj'

/-- Ordinary projection formula on ALL opens and ALL globally lisse factors.
Lissity only after restriction to the open is not a sufficient premise. -/
abbrev UniversalLisseOpenProjection :=
  ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
    (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (hj : j ≫ PY.structureMorphism = PX.structureMorphism)
    (A : C Y), L Y A →
    (F.push K h2 PX PY j hj ⋙ tensorRight A ≅
      tensorRight ((U.pull j).obj A) ⋙ F.push K h2 PX PY j hj)

variable (baseChange : UniversalSmoothOpenBaseChange C U F)
  (projection : UniversalLisseOpenProjection C U F L)
  (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
  {X Y X' Y' : Scheme}
  (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
  (PX' : FieldPresentation K X') (PY' : FieldPresentation K Y')
  (j : X ⟶ Y) (j' : X' ⟶ Y') (f : Y' ⟶ Y) (f' : X' ⟶ X)
  [IsOpenImmersion j] [QuasiCompact j]
  [IsOpenImmersion j'] [QuasiCompact j'] [Smooth f]
  (hj : j ≫ PY.structureMorphism = PX.structureMorphism)
  (hj' : j' ≫ PY'.structureMorphism = PX'.structureMorphism)
  (hf : f ≫ PY.structureMorphism = PY'.structureMorphism)
  (hf' : f' ≫ PX.structureMorphism = PX'.structureMorphism)
  (square : IsPullback f' j' j f)
  (A : C Y') (hA : L Y' A)

/-- The whole ordinary kernel extension comparison, on every source object. -/
def kernelExtensionIso :
    F.push K h2 PX PY j hj ⋙ U.pull f ⋙ tensorRight A ≅
      U.pull f' ⋙ tensorRight ((U.pull j').obj A) ⋙ F.push K h2 PX' PY' j' hj' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
    (baseChange K h2 PX PY PX' PY' j j' f f' hj hj' hf hf' square) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (U.pull f')
      (projection K h2 PX' PY' j' hj' A hA)

/-- Naturality retains the original ordinary source morphism. -/
theorem kernelExtensionIso_natural {B D : C X} (u : B ⟶ D) :
    (F.push K h2 PX PY j hj ⋙ U.pull f ⋙ tensorRight A).map u ≫
      (kernelExtensionIso C U F L baseChange projection K h2 PX PY PX' PY'
        j j' f f' hj hj' hf hf' square A hA).hom.app D =
    (kernelExtensionIso C U F L baseChange projection K h2 PX PY PX' PY'
        j j' f f' hj hj' hf hf' square A hA).hom.app B ≫
      (U.pull f' ⋙ tensorRight ((U.pull j').obj A) ⋙
        F.push K h2 PX' PY' j' hj').map u :=
  (kernelExtensionIso C U F L baseChange projection K h2 PX PY PX' PY'
    j j' f f' hj hj' hf hf' square A hA).hom.naturality u

end PrimeGap182.TypeIII.OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.UniversalSmoothOpenBaseChange
#print axioms PrimeGap182.TypeIII.OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.UniversalLisseOpenProjection
#print axioms PrimeGap182.TypeIII.OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.kernelExtensionIso
#print axioms PrimeGap182.TypeIII.OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.kernelExtensionIso_natural
