import TypeIIIFiniteRepresentationCoefficientTransport
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
The actual finite-representation coefficient functor is strong monoidal.
Its structure is transferred from extension of scalars to the SAME inverse
restriction functor, then lifted through the actual finite-module and action
categories. No topology or realization comparison is an input.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory

namespace PrimeGap182.TypeIII.FiniteRepresentationCoefficientMonoidal
open FiniteRepresentationCoefficientTransport
universe u v
variable {k l : Type u} [Field k] [Field l] (e : k ≃+* l)

/-- Both functors are left adjoint to the SAME restriction along e. -/
def extensionIso : ModuleCat.extendScalars e.toRingHom ≅ (moduleEquivalence e).functor :=
  (ModuleCat.extendRestrictScalarsAdj e.toRingHom).leftAdjointUniq
    (moduleEquivalence e).toAdjunction

theorem extensionIso_one_tmul (V : ModuleCat.{u} k) (x : V) :
    letI : Algebra k l := e.toRingHom.toAlgebra
    ((extensionIso e).hom.app V) ((1 : l) ⊗ₜ[k] x) = moduleSemilinearEquiv e V x := by
  let : Algebra k l := e.toRingHom.toAlgebra
  change ((ModuleCat.extendRestrictScalarsAdj e.toRingHom).homEquiv _ _
    ((extensionIso e).hom.app V)) x = _
  rw [extensionIso, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

/-- A coherent structure on the literal frozen inverse-restriction functor. -/
instance moduleMonoidal : (moduleEquivalence e).functor.Monoidal :=
  Functor.Monoidal.transport (extensionIso e)

/-- Lift the actual module tensorator and unit to the actual finite subcategory. -/
def finiteModuleCoreMonoidal : (finiteModuleEquivalence e).functor.CoreMonoidal where
  εIso := (ModuleCat.isFG l).isoMk (Functor.Monoidal.εIso (moduleEquivalence e).functor)
  μIso V W := (ModuleCat.isFG l).isoMk
    (Functor.Monoidal.μIso (moduleEquivalence e).functor V.obj W.obj)
  μIso_hom_natural_left f W := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.μ_natural_left (moduleEquivalence e).functor f.hom W.obj
  μIso_hom_natural_right V f := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.μ_natural_right (moduleEquivalence e).functor V.obj f.hom
  associativity V W Z := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.associativity (moduleEquivalence e).functor V.obj W.obj Z.obj
  left_unitality V := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.left_unitality (moduleEquivalence e).functor V.obj
  right_unitality V := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.right_unitality (moduleEquivalence e).functor V.obj

instance finiteModuleMonoidal : (finiteModuleEquivalence e).functor.Monoidal :=
  (finiteModuleCoreMonoidal e).toMonoidal

variable (H : Type v) [Group H]

/-- Action lifting uses the actual frozen coefficient functor. -/
instance coefficientMonoidal : (coefficientEquivalence e H).functor.Monoidal :=
  inferInstanceAs ((finiteModuleEquivalence e).functor.mapAction H).Monoidal

/-- Forward transport of a tensor is the tensor of forward transports. -/
def tensorIso (V W : FDRep k H) :
    (coefficientEquivalence e H).functor.obj (V ⊗ W) ≅
      (coefficientEquivalence e H).functor.obj V ⊗
        (coefficientEquivalence e H).functor.obj W :=
  (Functor.Monoidal.μIso (coefficientEquivalence e H).functor V W).symm

/-- The transported arithmetic-independent coefficient unit is the target unit. -/
def unitIso : (coefficientEquivalence e H).functor.obj (𝟙_ (FDRep k H)) ≅
    𝟙_ (FDRep l H) :=
  (Functor.Monoidal.εIso (coefficientEquivalence e H).functor).symm

theorem tensor_naturality {V V' W W' : FDRep k H} (f : V ⟶ V') (g : W ⟶ W') :
    (coefficientEquivalence e H).functor.map (f ⊗ₘ g) ≫ (tensorIso e H V' W').hom =
      (tensorIso e H V W).hom ≫
        ((coefficientEquivalence e H).functor.map f ⊗ₘ
          (coefficientEquivalence e H).functor.map g) :=
  (Functor.OplaxMonoidal.δ_natural (coefficientEquivalence e H).functor f g).symm

theorem tensor_associativity (V W Z : FDRep k H) :
    (tensorIso e H (V ⊗ W) Z).hom ≫
        (tensorIso e H V W).hom ▷ (coefficientEquivalence e H).functor.obj Z ≫
        (α_ ((coefficientEquivalence e H).functor.obj V)
          ((coefficientEquivalence e H).functor.obj W)
          ((coefficientEquivalence e H).functor.obj Z)).hom =
      (coefficientEquivalence e H).functor.map (α_ V W Z).hom ≫
        (tensorIso e H V (W ⊗ Z)).hom ≫
        (coefficientEquivalence e H).functor.obj V ◁ (tensorIso e H W Z).hom :=
  Functor.OplaxMonoidal.associativity (coefficientEquivalence e H).functor V W Z

theorem unit_left (V : FDRep k H) :
    (tensorIso e H (𝟙_ (FDRep k H)) V).hom ≫
        (unitIso e H).hom ▷ (coefficientEquivalence e H).functor.obj V ≫
        (λ_ ((coefficientEquivalence e H).functor.obj V)).hom =
      (coefficientEquivalence e H).functor.map (λ_ V).hom :=
  Functor.OplaxMonoidal.left_unitality_hom (coefficientEquivalence e H).functor V

theorem unit_right (V : FDRep k H) :
    (tensorIso e H V (𝟙_ (FDRep k H))).hom ≫
        (coefficientEquivalence e H).functor.obj V ◁ (unitIso e H).hom ≫
        (ρ_ ((coefficientEquivalence e H).functor.obj V)).hom =
      (coefficientEquivalence e H).functor.map (ρ_ V).hom :=
  Functor.OplaxMonoidal.right_unitality_hom (coefficientEquivalence e H).functor V

/-- Explicit contragredient: inverse group action and coefficient-valued linear dual. -/
abbrev dualObject (V : FDRep k H) : FDRep k H := FDRep.of (Representation.dual (k := k) V.ρ)

/-- A dual morphism is actual precomposition by the original linear map. -/
def dualMap {V W : FDRep k H} (f : V ⟶ W) : dualObject H W ⟶ dualObject H V :=
  { hom := ObjectProperty.homMk (ModuleCat.ofHom f.hom.hom.hom.dualMap)
    comm := by
      intro g
      apply FGModuleCat.hom_ext
      ext φ x
      exact congrArg φ (LinearMap.congr_fun
        (congrArg (fun h => h.hom.hom) (f.comm g⁻¹)) x).symm }

def dualFunctor : (FDRep k H)ᵒᵖ ⥤ FDRep k H where
  obj V := dualObject H V.unop
  map f := dualMap H f.unop
  map_id V := by ext φ x; rfl
  map_comp f g := by ext φ x; rfl

local instance ringEquivInvPair : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e
local instance ringEquivSymmInvPair : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm e

/-- The dual semilinear map applies e to the value and the inverse carrier map to the input. -/
def dualSemilinearEquiv (V : FDRep k H) :
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) (Module.Dual k V)
      (Module.Dual l ((coefficientEquivalence e H).functor.obj V)) where
  toFun φ :=
    { toFun := fun x => e (φ ((underlyingSemilinearEquiv e H V).symm x))
      map_add' x y := by simp only [map_add]
      map_smul' r x := by
        rw [map_smulₛₗ, map_smul]
        change e (e.symm r * φ ((underlyingSemilinearEquiv e H V).symm x)) =
          r * e (φ ((underlyingSemilinearEquiv e H V).symm x))
        rw [map_mul, e.apply_symm_apply] }
  invFun φ :=
    { toFun := fun x => e.symm (φ (underlyingSemilinearEquiv e H V x))
      map_add' x y := by simp only [map_add]
      map_smul' r x := by
        rw [map_smulₛₗ, map_smul]
        change e.symm (e r * φ (underlyingSemilinearEquiv e H V x)) =
          r * e.symm (φ (underlyingSemilinearEquiv e H V x))
        rw [map_mul, e.symm_apply_apply] }
  left_inv φ := by
    ext x
    change e.symm (e (φ ((underlyingSemilinearEquiv e H V).symm
      (underlyingSemilinearEquiv e H V x)))) = φ x
    rw [LinearEquiv.symm_apply_apply, e.symm_apply_apply]
  right_inv φ := by
    ext x
    change e (e.symm (φ (underlyingSemilinearEquiv e H V
      ((underlyingSemilinearEquiv e H V).symm x)))) = φ x
    rw [LinearEquiv.apply_symm_apply, e.apply_symm_apply]
  map_add' φ ψ := by ext x; exact map_add e _ _
  map_smul' r φ := by
    ext x
    change e ((r • φ) ((underlyingSemilinearEquiv e H V).symm x)) =
      e r * e (φ ((underlyingSemilinearEquiv e H V).symm x))
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul]

/-- Compose two inverse semilinear maps to get the actual l-linear dual comparison. -/
def dualLinearEquiv (V : FDRep k H) :
    (coefficientEquivalence e H).functor.obj (dualObject H V) ≃ₗ[l]
      dualObject H ((coefficientEquivalence e H).functor.obj V) :=
  (underlyingSemilinearEquiv e H (dualObject H V)).symm.trans
    (dualSemilinearEquiv e H V)

def dualIso (V : FDRep k H) :
    (coefficientEquivalence e H).functor.obj (dualObject H V) ≅
      dualObject H ((coefficientEquivalence e H).functor.obj V) :=
  Action.mkIso ((ModuleCat.isFG l).isoMk (dualLinearEquiv e H V).toModuleIso) (by
    intro g
    apply FGModuleCat.hom_ext
    ext φ x
    rfl)

theorem dualIso_apply (V : FDRep k H)
    (φ : (coefficientEquivalence e H).functor.obj (dualObject H V))
    (x : (coefficientEquivalence e H).functor.obj V) :
    (dualIso e H V).hom.hom.hom φ x = e (((underlyingSemilinearEquiv e H (dualObject H V)).symm φ)
      ((underlyingSemilinearEquiv e H V).symm x)) := rfl

theorem dual_naturality {V W : FDRep k H} (f : V ⟶ W) :
    (coefficientEquivalence e H).functor.map (dualMap H f) ≫ (dualIso e H V).hom =
      (dualIso e H W).hom ≫ dualMap H ((coefficientEquivalence e H).functor.map f) := by
  ext φ x
  rfl

def dualNatIso :
    dualFunctor (k := k) H ⋙ (coefficientEquivalence e H).functor ≅
      (coefficientEquivalence e H).functor.op ⋙ dualFunctor (k := l) H :=
  NatIso.ofComponents (fun V => dualIso e H V.unop) (fun f => dual_naturality e H f.unop)

end PrimeGap182.TypeIII.FiniteRepresentationCoefficientMonoidal
