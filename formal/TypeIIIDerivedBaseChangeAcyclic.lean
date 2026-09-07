import TypeIIIAcyclicResolutionComparison
import TypeIIIDerivedBaseChangeZero

/-!
# Acyclic images of injectives and the actual derived base-change map

The original ordinary square is assumed invertible, and the exact
source-side functor sends injective objects to objects with vanishing
positive right derived functors of the target functor.  The proved
acyclic-resolution comparison then makes the existing comparison chain
map a quasi-isomorphism.  Its actual homology factorization proves
invertibility of the same derived base-change map in every degree.

The proof uses homology isomorphisms, without asserting that the source
comparison is invertible in the homotopy category.  The degree-zero
identity retains the original ordinary transformation and augmentations.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₃ w₄

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [EnoughInjectives C']
  [HasDerivedCategory.{w₃} C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D'] [HasDerivedCategory.{w₄} D']
  (F : C ⥤ D) [F.Additive]
  (F' : C' ⥤ D') [F'.Additive] [PreservesFiniteLimits F']
  (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : D ⥤ D') [H.Additive] (β : F ⋙ H ⟶ G ⋙ F') [IsIso β]

omit [HasInjectiveResolutions C] in
set_option backward.isDefEq.respectTransparency false in
/-- The original chain map is a quasi-isomorphism when images of injectives are acyclic. -/
theorem derivedBaseChangeChainMap_quasiIso_of_acyclic
    (hG : ∀ (J : C), Injective J → ∀ m : ℕ,
      IsZero ((F'.rightDerived (m + 1)).obj (G.obj J)))
    {A : C} (I : InjectiveResolution A) :
    QuasiIso (derivedBaseChangeChainMap F F' G H β I) := by
  have : IsIso ((β.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex) :=
    ((NatIso.mapHomologicalComplex (asIso β) (ComplexShape.up ℕ)).app I.cocomplex).isIso_hom
  have : QuasiIso ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (exactFunctorResolutionComparison G I)) :=
    exactFunctorResolutionComparison_map_quasiIso_of_acyclic G F' I
      (fun j m => hG (I.cocomplex.X j) (I.injective j) m)
  change QuasiIso ((β.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
    (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map (exactFunctorResolutionComparison G I))
  infer_instance

variable [H.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical homology factorization makes each component of the same derived map invertible. -/
theorem derivedBaseChangeMap_app_isIso_of_acyclic
    (hG : ∀ (J : C), Injective J → ∀ m : ℕ,
      IsZero ((F'.rightDerived (m + 1)).obj (G.obj J)))
    (n : ℕ) (A : C) : IsIso ((derivedBaseChangeMap F F' G H β n).app A) := by
  have : QuasiIso (derivedBaseChangeChainMap F F' G H β (injectiveResolution A)) :=
    derivedBaseChangeChainMap_quasiIso_of_acyclic F F' G H β hG (injectiveResolution A)
  have : IsIso ((HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
      (derivedBaseChangeChainMap F F' G H β (injectiveResolution A))) := by
    change IsIso (HomologicalComplex.homologyMap
      (derivedBaseChangeChainMap F F' G H β (injectiveResolution A)) n)
    infer_instance
  have : IsIso ((derivedBaseChangeMap F F' G H β n).app A ≫
      (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).hom.app
        ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution (G.obj A)).cocomplex)) := by
    rw [derivedBaseChangeMap_factors]
    infer_instance
  exact IsIso.of_isIso_comp_right ((derivedBaseChangeMap F F' G H β n).app A)
    ((HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).hom.app
      ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (G.obj A)).cocomplex))

/-- Acyclic images of injectives suffice for invertibility of the existing derived transformation. -/
theorem derivedBaseChangeMap_isIso_of_acyclic
    (hG : ∀ (J : C), Injective J → ∀ m : ℕ,
      IsZero ((F'.rightDerived (m + 1)).obj (G.obj J)))
    (n : ℕ) : IsIso (derivedBaseChangeMap F F' G H β n) :=
  (NatTrans.isIso_iff_isIso_app _).2
    (fun A => derivedBaseChangeMap_app_isIso_of_acyclic F F' G H β hG n A)

/-- The actual derived isomorphism obtained from the same base-change transformation. -/
def derivedBaseChangeAcyclicIso
    (hG : ∀ (J : C), Injective J → ∀ m : ℕ,
      IsZero ((F'.rightDerived (m + 1)).obj (G.obj J)))
    (n : ℕ) : F.rightDerived n ⋙ H ≅ G ⋙ F'.rightDerived n := by
  have : IsIso (derivedBaseChangeMap F F' G H β n) :=
    derivedBaseChangeMap_isIso_of_acyclic F F' G H β hG n
  exact asIso (derivedBaseChangeMap F F' G H β n)

/-- Its forward morphism is literally the original derived base-change map. -/
theorem derivedBaseChangeAcyclicIso_hom
    (hG : ∀ (J : C), Injective J → ∀ m : ℕ,
      IsZero ((F'.rightDerived (m + 1)).obj (G.obj J)))
    (n : ℕ) :
    (derivedBaseChangeAcyclicIso F F' G H β hG n).hom =
      derivedBaseChangeMap F F' G H β n := rfl

/-- The same original ordinary square is retained in degree zero. -/
theorem derivedBaseChangeAcyclicIso_zero
    (hG : ∀ (J : C), Injective J → ∀ m : ℕ,
      IsZero ((F'.rightDerived (m + 1)).obj (G.obj J))) :
    CategoryTheory.Functor.whiskerRight F.toRightDerivedZero H ≫
        (derivedBaseChangeAcyclicIso F F' G H β hG 0).hom =
      β ≫ CategoryTheory.Functor.whiskerLeft G F'.toRightDerivedZero :=
  derivedBaseChangeMap_zero F F' G H β

#print axioms derivedBaseChangeChainMap_quasiIso_of_acyclic
#print axioms derivedBaseChangeMap_app_isIso_of_acyclic
#print axioms derivedBaseChangeMap_isIso_of_acyclic
#print axioms derivedBaseChangeAcyclicIso
#print axioms derivedBaseChangeAcyclicIso_hom
#print axioms derivedBaseChangeAcyclicIso_zero

end PrimeGap182.TypeIII
