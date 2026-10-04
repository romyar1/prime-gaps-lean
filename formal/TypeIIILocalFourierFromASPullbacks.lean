import TypeIIILocalFourierFromKernel
import TypeIIILocalFourierKernelCoordinates

/-!
# The local AS kernel from the original line object

The local kernel is derived from an actual function pullback of the original
line object. It is not a separate object field. `Open` is the algebraic
source-punctured, finite-target chart, before henselian local restriction.
`extendKernel` first takes its henselian product inverse image and extends
by zero across the source boundary only; the target origin remains included.
The phase pullback includes the constant-field extension from K to PhaseField K.
General local geometry and the inverse-image compositor remain parameters.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory
namespace PrimeGap182.TypeIII.LocalFourierFromASPullbacks
open PublishedPhaseApplication PublishedLocalConstruction FiniteOriginFromRestriction
open LocalFourierKernelCoordinates
universe mu t u v a b
variable (K : Type) [Field K]

structure Inputs (I : Type t) [Group I] (G : Type mu) [Group G]
    (Line : Type a) [Category.{b} Line] where
  Raw : Type mu
  [rawGroup : Group Raw]
  localRestriction : PointedSubstitution (PhaseField K) → G →* Raw
  Admissible : FDRep ℂ I → Prop
  admissibility : LocalFourierFromKernel.Admissibility Admissible
  Trait : Type u
  [traitCategory : Category.{v} Trait]
  [traitPreadditive : Preadditive Trait]
  Product : Type u
  [productCategory : Category.{v} Product]
  [productPreadditive : Preadditive Product]
  [productMonoidal : MonoidalCategory Product]
  [productBilinear : MonoidalPreadditive Product]
  zeroExtend : (show ObjectProperty (FDRep ℂ I) from Admissible).FullSubcategory ⥤ Trait
  [zeroExtendAdditive : zeroExtend.Additive]
  pull : Trait ⥤ Product
  [pullAdditive : pull.Additive]
  firstCycles : Product ⥤ FDRep ℂ Raw
  [firstCyclesAdditive : firstCycles.Additive]
  Open : Type u
  [openCategory : Category.{v} Open]
  phasePullback : (LocalFourierKernelCoordinates.modelScheme (PhaseField K) ⟶
    LocalFourierKernelCoordinates.affineLine (PhaseField K)) → Line ⥤ Open
  coordinateRestriction : Open ⥤ Open
  coordinateComposition : ∀ f, phasePullback f ⋙ coordinateRestriction ≅
    phasePullback (LocalFourierKernelCoordinates.coordinateMorphism (PhaseField K) ≫ f)
  extendKernel : Open ⥤ Product

attribute [instance] Inputs.rawGroup Inputs.traitCategory Inputs.traitPreadditive
  Inputs.productCategory Inputs.productPreadditive Inputs.productMonoidal Inputs.productBilinear
  Inputs.zeroExtendAdditive Inputs.pullAdditive Inputs.firstCyclesAdditive Inputs.openCategory

variable {K} {I : Type t} [Group I] {G : Type mu} [Group G]
  {Line : Type a} [Category.{b} Line] (S : Inputs K I G Line)

/-- Construct the original AS kernel, at the checked finite-target coordinate. -/
def Inputs.kernel (as : Line) : S.Product :=
  S.extendKernel.obj ((S.phasePullback (localKernelMorphism (PhaseField K))).obj as)

/-- All previous local operations are retained, with the kernel now derived. -/
def Inputs.operationData (as : Line) : LocalFourierFromKernel.Inputs K I G where
  Raw := S.Raw
  rawGroup := S.rawGroup
  localRestriction := S.localRestriction
  Admissible := S.Admissible
  admissibility := S.admissibility
  Trait := S.Trait
  traitCategory := S.traitCategory
  traitPreadditive := S.traitPreadditive
  Product := S.Product
  productCategory := S.productCategory
  productPreadditive := S.productPreadditive
  productMonoidal := S.productMonoidal
  productBilinear := S.productBilinear
  zeroExtend := S.zeroExtend
  zeroExtendAdditive := S.zeroExtendAdditive
  pull := S.pull
  pullAdditive := S.pullAdditive
  firstCycles := S.firstCycles
  firstCyclesAdditive := S.firstCyclesAdditive
  kernel := S.kernel as

/-- The original global/local coordinate comparison after source extension. -/
abbrev Inputs.globalKernelFunctorComparison :
    S.phasePullback (globalKernelMorphism (PhaseField K)) ⋙
      S.coordinateRestriction ⋙ S.extendKernel ≅
    S.phasePullback (localKernelMorphism (PhaseField K)) ⋙ S.extendKernel :=
  Functor.isoWhiskerRight (kernelPullbackComparison (PhaseField K) S.phasePullback
    S.coordinateRestriction S.coordinateComposition) S.extendKernel

/-- Restrict the original global AS kernel and extend across the source
boundary. The comparison uses the checked global/local coordinate square. -/
def Inputs.globalKernelComparison (as : Line) :
    S.extendKernel.obj (S.coordinateRestriction.obj
      ((S.phasePullback (globalKernelMorphism (PhaseField K))).obj as)) ≅
      (S.operationData as).kernel :=
  S.globalKernelFunctorComparison.app as

/-- Extension preserves naturality of the original global/local kernel
comparison, on every original line morphism. -/
theorem Inputs.globalKernelComparison_natural {A B : Line} (f : A ⟶ B) :
    (S.phasePullback (globalKernelMorphism (PhaseField K)) ⋙
      S.coordinateRestriction ⋙ S.extendKernel).map f ≫
        S.globalKernelFunctorComparison.hom.app B =
      S.globalKernelFunctorComparison.hom.app A ≫
        (S.phasePullback (localKernelMorphism (PhaseField K)) ⋙ S.extendKernel).map f :=
  S.globalKernelFunctorComparison.hom.naturality f

theorem Inputs.kernel_definition (as : Line) : (S.operationData as).kernel =
    S.extendKernel.obj ((S.phasePullback (localKernelMorphism (PhaseField K))).obj as) := rfl

/-- The transform now computes with this same original AS pullback. -/
theorem Inputs.unscaled_obj (as : Line) (V : FDRep ℂ I) (hV : S.Admissible V) :
    (S.operationData as).data.unscaled.obj V hV =
      S.firstCycles.obj (S.pull.obj (S.zeroExtend.obj ⟨V, hV⟩) ⊗
        S.extendKernel.obj ((S.phasePullback (localKernelMorphism (PhaseField K))).obj as)) := rfl

/-- The action on intertwining maps uses the same original AS pullback. -/
theorem Inputs.unscaled_map (as : Line) {V W : FDRep ℂ I}
    (hV : S.Admissible V) (hW : S.Admissible W)
    (f : Representation.IntertwiningMap V.ρ W.ρ) :
    ((S.operationData as).data.unscaled.map hV hW f).toLinearMap =
      (FourierOriginFromGlobalCycles.intertwiner (S.firstCycles.map
        (S.pull.map (S.zeroExtend.map
          (ObjectProperty.homMk (X := ⟨V, hV⟩) (Y := ⟨W, hW⟩)
            (LocalFourierFromKernel.repHom f))) ▷
          S.extendKernel.obj ((S.phasePullback (localKernelMorphism (PhaseField K))).obj as)))).toLinearMap := rfl

end PrimeGap182.TypeIII.LocalFourierFromASPullbacks

#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.kernel
#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.operationData
#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.globalKernelFunctorComparison
#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.globalKernelComparison
#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.globalKernelComparison_natural
#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.kernel_definition
#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.unscaled_obj
#print axioms PrimeGap182.TypeIII.LocalFourierFromASPullbacks.Inputs.unscaled_map
