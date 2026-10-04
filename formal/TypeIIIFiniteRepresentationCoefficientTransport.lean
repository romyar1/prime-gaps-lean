import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
Pure finite-representation coefficient transport along a field isomorphism.
The group and every additive action operator remain the same. No topology,
continuous representation, inertia comparison, Frobenius comparison or sheaf
realization is asserted. The two coefficient fields have the same universe;
the group universe is independent.
-/
noncomputable section
open CategoryTheory

namespace PrimeGap182.TypeIII.FiniteRepresentationCoefficientTransport
universe u v w
variable {k l : Type u} [Field k] [Field l] (e : k ≃+* l)

local instance ringEquivInvPair : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e

local instance ringEquivSymmInvPair : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm e

/-- Forward coefficient transport is restriction along the INVERSE field map. -/
def moduleEquivalence : ModuleCat.{u} k ≌ ModuleCat.{u} l :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm

/-- The identity on the additive carrier is semilinear through the forward map. -/
def moduleSemilinearEquiv (V : ModuleCat.{u} k) :
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) V ((moduleEquivalence e).functor.obj V) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = e.symm (e r) • x
    rw [e.symm_apply_apply]

theorem moduleFinite_iff (V : ModuleCat.{u} k) :
    Module.Finite l ((moduleEquivalence e).functor.obj V) ↔ Module.Finite k V := by
  constructor
  · intro h
    let := h
    exact Module.Finite.of_surjective (moduleSemilinearEquiv e V).symm.toLinearMap
      (moduleSemilinearEquiv e V).symm.surjective
  · intro h
    let := h
    exact Module.Finite.of_surjective (moduleSemilinearEquiv e V).toLinearMap
      (moduleSemilinearEquiv e V).surjective

/-- Restrict the actual module equivalence to finite modules. -/
def finiteModuleEquivalence : FGModuleCat.{u} k ≌ FGModuleCat.{u} l := by
  letI : (ModuleCat.isFG.{u} l).IsClosedUnderIsomorphisms :=
    { of_iso := fun {X Y} i h => by
        let : Module.Finite l X := h
        exact Module.Finite.of_surjective i.toLinearEquiv.toLinearMap i.toLinearEquiv.surjective }
  exact (moduleEquivalence e).congrFullSubcategory (by
    funext V
    exact propext (moduleFinite_iff e V))

variable (H : Type v) [Group H]

/-- Actual equivalence of finite representations, for every group. -/
def coefficientEquivalence : FDRep k H ≌ FDRep l H :=
  (finiteModuleEquivalence e).mapAction H

/-- Every underlying action retains its additive carrier. -/
def underlyingSemilinearEquiv (V : FDRep k H) :
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) V ((coefficientEquivalence e H).functor.obj V) :=
  moduleSemilinearEquiv e V.V.obj

theorem intertwines (V : FDRep k H) (g : H) (x : V) :
    underlyingSemilinearEquiv e H V (V.ρ g x) =
      ((coefficientEquivalence e H).functor.obj V).ρ g
        (underlyingSemilinearEquiv e H V x) := rfl

/-- Morphisms retain the same additive linear-map function. -/
theorem map_intertwines {V W : FDRep k H} (f : V ⟶ W) (x : V) :
    underlyingSemilinearEquiv e H W (f.hom.hom x) =
      ((coefficientEquivalence e H).functor.map f).hom.hom
        (underlyingSemilinearEquiv e H V x) := rfl

/-- Coefficient transport commutes naturally with every group restriction. -/
def restrictionIso {J : Type w} [Group J] (f : J →* H) :
    Action.res (FGModuleCat k) f ⋙ (coefficientEquivalence e J).functor ≅
      (coefficientEquivalence e H).functor ⋙ Action.res (FGModuleCat l) f :=
  NatIso.ofComponents (fun _ => Action.mkIso (Iso.refl _) (fun _ => by apply FGModuleCat.hom_ext; ext x; rfl))
    (fun _ => by ext; rfl)

theorem finrank_eq (V : FDRep k H) :
    Module.finrank l ((coefficientEquivalence e H).functor.obj V) = Module.finrank k V := by
  simpa [Module.finrank] using (congrArg Cardinal.toNat (_root_.rank_eq_of_equiv_equiv e (underlyingSemilinearEquiv e H V).toAddEquiv
    e.bijective (underlyingSemilinearEquiv e H V).map_smulₛₗ)).symm

/-- Equality of every actual action operator with identity is preserved. -/
theorem trivialAction_iff (V : FDRep k H) :
    (∀ g, ((coefficientEquivalence e H).functor.obj V).ρ g = 1) ↔
      (∀ g, V.ρ g = 1) := by
  constructor <;> intro h g <;> ext x <;> exact LinearMap.congr_fun (h g) x

/-- Wild-triviality for any fixed subgroup is an unchanged operator assertion. -/
theorem subgroupTrivial_iff (V : FDRep k H) (P : Subgroup H) :
    (∀ g ∈ P, ∀ x, ((coefficientEquivalence e H).functor.obj V).ρ g x = x) ↔
      (∀ g ∈ P, ∀ x, V.ρ g x = x) := Iff.rfl

/-- The same fixed vectors form semilinearly equivalent invariant submodules. -/
def invariantsSemilinearEquiv (V : FDRep k H) :
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      (Representation.invariants V.ρ)
      (Representation.invariants ((coefficientEquivalence e H).functor.obj V).ρ) where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    apply Subtype.ext
    exact (underlyingSemilinearEquiv e H V).map_smulₛₗ r x.val

theorem invariants_finrank_eq (V : FDRep k H) :
    Module.finrank l (Representation.invariants ((coefficientEquivalence e H).functor.obj V).ρ) =
      Module.finrank k (Representation.invariants V.ρ) := by
  simpa [Module.finrank] using (congrArg Cardinal.toNat (_root_.rank_eq_of_equiv_equiv e (invariantsSemilinearEquiv e H V).toAddEquiv
    e.bijective (invariantsSemilinearEquiv e H V).map_smulₛₗ)).symm

end PrimeGap182.TypeIII.FiniteRepresentationCoefficientTransport
