import TypeIIILocalFourierFromAdditiveMaps
import TypeIIIFourierOriginFromGlobalCycles
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Local Fourier from the ordinary local kernel and R¹ vanishing cycles

Laumon Definition 2.4.2.3 defines the infinity-to-zero local transform by
R¹ Phi(pr*(V_!) tensor L_psi(pi'/pi)) at the closed/generic local point.
We construct the operation by composing these general functors. Its map
laws and additivity then follow from those same functors on original maps.
No independent local Fourier operation or map-additivity law is supplied.

The local geometric categories, zero extension, inverse image, fixed AS
kernel and degree-one vanishing-cycle stalk remain explicit framework
operations, with the standard additive structures. They are not a
constructed adic sheaf theory. The same operation is passed to stationary
phase, normalization, finite sums and the cubic covering applications.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory

namespace PrimeGap182.TypeIII.LocalFourierFromKernel
open PublishedPhaseApplication PublishedLocalConstruction FiniteOriginFromRestriction
open FourierOriginFromGlobalCycles

universe mu t u v

variable {I : Type t} [Group I] {G : Type mu} [Group G]

/-- The categorical morphism with precisely the original equivariant map. -/
abbrev repHom {R S : FDRep ℂ I} (f : Representation.IntertwiningMap R.ρ S.ρ) : R ⟶ S :=
  FDRep.forget₂HomLinearEquiv R S (Rep.ofHom f)

variable {Admissible : FDRep ℂ I → Prop}

/-- Read an ordinary functor on the actual full admissible subcategory
as the existing representation-functor interface. -/
def representationFunctor
    (F : (show ObjectProperty (FDRep ℂ I) from Admissible).FullSubcategory ⥤ FDRep ℂ G) :
    AdmissibleRepresentationFunctor ℂ I G Admissible where
  obj R hR := F.obj ⟨R, hR⟩
  map hR hS f := intertwiner
    (F.map (ObjectProperty.homMk (X := ⟨_, hR⟩) (Y := ⟨_, hS⟩) (repHom f)))
  map_id R hR := by
    change intertwiner (F.map (𝟙 (⟨R, hR⟩ : (show ObjectProperty _ from Admissible).FullSubcategory))) = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp hR hS hT f g := by
    change intertwiner (F.map
      ((ObjectProperty.homMk (X := ⟨_, hR⟩) (Y := ⟨_, hS⟩) (repHom f)) ≫
        ObjectProperty.homMk (X := ⟨_, hS⟩) (Y := ⟨_, hT⟩) (repHom g))) = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- Map-additivity is inherited on the original intertwining maps. -/
theorem representationFunctor_map_add
    (F : (show ObjectProperty (FDRep ℂ I) from Admissible).FullSubcategory ⥤ FDRep ℂ G)
    [F.Additive] {R S : FDRep ℂ I} (hR : Admissible R) (hS : Admissible S)
    (f g : Representation.IntertwiningMap R.ρ S.ρ) :
    (representationFunctor F).map hR hS (f + g) =
      (representationFunctor F).map hR hS f + (representationFunctor F).map hR hS g := by
  change intertwiner (F.map
    ((ObjectProperty.homMk (X := ⟨R, hR⟩) (Y := ⟨S, hS⟩) (repHom f)) +
      ObjectProperty.homMk (X := ⟨R, hR⟩) (Y := ⟨S, hS⟩) (repHom g))) = _
  rw [CategoryTheory.Functor.map_add]
  rfl

/-- Domain closure for continuous representations defined over a finite
coefficient field. These are the former admissibility clauses verbatim. -/
structure Admissibility (Admissible : FDRep ℂ I → Prop) : Prop where
  admissible_equiv : ∀ {R S : FDRep ℂ I}, Representation.Equiv R.ρ S.ρ →
    Admissible R → Admissible S
  admissible_sum : ∀ {ι : Type} [Fintype ι], ∀ R : ι → FDRep ℂ I,
    (∀ i, Admissible (R i)) → Admissible (finiteSum R)

variable (K : Type) [Field K]

/-- General ordinary local sheaf operations for the kernel pi'/pi.
`Trait` is the source henselian trait; `Product` is the local product.
`firstCycles` is R¹ Phi followed by the closed/generic geometric stalk.
The kernel is the zero-extended AS sheaf of pi'/pi at the fixed character.
These operations are fixed before the Type III family is constructed. -/
structure Inputs (I : Type t) [Group I] (G : Type mu) [Group G] where
  Raw : Type mu
  [rawGroup : Group Raw]
  localRestriction : PointedSubstitution (PhaseField K) → G →* Raw
  Admissible : FDRep ℂ I → Prop
  admissibility : Admissibility Admissible
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
  kernel : Product
  firstCycles : Product ⥤ FDRep ℂ Raw
  [firstCyclesAdditive : firstCycles.Additive]

attribute [instance] Inputs.rawGroup Inputs.traitCategory Inputs.traitPreadditive
  Inputs.productCategory Inputs.productPreadditive Inputs.productMonoidal Inputs.productBilinear
  Inputs.zeroExtendAdditive Inputs.pullAdditive Inputs.firstCyclesAdditive

variable {K} (S : Inputs.{mu,t,u,v} K I G)

/-- The published local Fourier definition, as an actual composite functor. -/
abbrev Inputs.operation :
    (show ObjectProperty (FDRep ℂ I) from S.Admissible).FullSubcategory ⥤ FDRep ℂ S.Raw :=
  S.zeroExtend ⋙ S.pull ⋙ tensorRight S.kernel ⋙ S.firstCycles

instance Inputs.operation_additive : S.operation.Additive := by
  dsimp only [Inputs.operation]
  infer_instance

/-- Construct the former local Fourier data with this exact operation. -/
def Inputs.data : FiniteOriginFromRestriction.Data K ℂ I G where
  Raw := S.Raw
  localRestriction := S.localRestriction
  Admissible := S.Admissible
  unscaled := representationFunctor S.operation

/-- Only domain closure remains a separate rule; map-additivity is derived. -/
theorem Inputs.linearRules : LocalFourierFromAdditiveMaps.Rules S.data.unscaled where
  admissible_equiv := S.admissibility.admissible_equiv
  admissible_sum := S.admissibility.admissible_sum
  map_add := representationFunctor_map_add S.operation

/-- On objects, the unscaled transform is exactly the published local
kernel calculation, including extension by zero and degree R¹ Phi. -/
theorem Inputs.unscaled_obj (V : FDRep ℂ I) (hV : S.Admissible V) :
    S.data.unscaled.obj V hV =
      S.firstCycles.obj (S.pull.obj (S.zeroExtend.obj ⟨V, hV⟩) ⊗ S.kernel) := rfl

/-- The actual action on a morphism uses the same extension, pullback,
tensor and vanishing-cycle maps as the object construction. -/
theorem Inputs.unscaled_map {V W : FDRep ℂ I} (hV : S.Admissible V) (hW : S.Admissible W)
    (f : Representation.IntertwiningMap V.ρ W.ρ) :
    (S.data.unscaled.map hV hW f).toLinearMap =
      (intertwiner (S.firstCycles.map
        ((S.pull.map (S.zeroExtend.map
          (ObjectProperty.homMk (X := ⟨V, hV⟩) (Y := ⟨W, hW⟩) (repHom f)))) ▷ S.kernel))).toLinearMap := rfl

end PrimeGap182.TypeIII.LocalFourierFromKernel

#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.representationFunctor
#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.representationFunctor_map_add
#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.Inputs.operation
#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.Inputs.operation_additive
#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.Inputs.data
#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.Inputs.linearRules
#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.Inputs.unscaled_obj
#print axioms PrimeGap182.TypeIII.LocalFourierFromKernel.Inputs.unscaled_map
