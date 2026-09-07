import TypeIIIEtaleExtensionByZero
import TypeIIIAlgebraicallyClosedEtalePoints
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exactness of actual étale extension by zero

For a monomorphic étale object U over S, the existing extension functor
preserves finite limits and finite colimits, and hence short exact
sequences of module sheaves.  The finite-limit proof uses the actual
geometric stalk formulas: inside U the composite is a stalk functor,
and outside U it is a zero functor.  The proved conservative family of
algebraic closures of residue-field points reflects the resulting
limit cones.  Finite colimits follow from the existing adjunction.

No exactness, conservativity, or stalk-comparison premise is supplied.
The coefficient ring may in particular be a finite torsion ring.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleExtensionByZero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

variable (S : Scheme.{u}) (U : S.Etale) [Mono U.hom] (E : Type u) [Ring E]

/-- The actual composite of extension by zero with any geometric
stalk functor preserves finite limits. -/
theorem stalkComposite_preservesFiniteLimits (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    PreservesFiniteLimits (functor S U E ⋙ (Scheme.pointSmallEtale s).sheafFiber) := by
  by_cases hs : s default ∈ Set.range U.hom
  · obtain ⟨t⟩ := (geometricFiber_nonempty_iff S U Ω s).mpr hs
    have ht : t.left ≫ U.hom = s := Over.w t
    rw [← ht]
    exact preservesFiniteLimits_of_natIso (stalkIso S U Ω t.left E).symm
  · have hzero : IsZero (functor S U E ⋙ (Scheme.pointSmallEtale s).sheafFiber) :=
      Functor.isZero _ (fun F => stalk_isZero S U E Ω s hs F)
    let : PreservesLimitsOfSize.{0, 0}
        (functor S U E ⋙ (Scheme.pointSmallEtale s).sheafFiber) :=
      Functor.preservesLimitsOfSize_of_isZero _ hzero
    infer_instance

/-- The actual extension functor preserves finite limits, detected by
the proved conservative family of algebraically closed geometric points. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor S U E) where
  preservesFiniteLimits J _ _ := by
    constructor
    intro K
    refine ⟨fun {c} hc => ⟨?_⟩⟩
    apply ((algebraicClosureEtalePoints_isConservative S).jointlyReflectIsomorphisms
      (ModuleCat.{u} E)).jointlyReflectsLimit
    intro Φ
    apply Classical.choice
    rcases Φ with ⟨_, ⟨s⟩⟩
    let : PreservesFiniteLimits
        (functor S U E ⋙ (algebraicClosureEtalePoint S s).sheafFiber) :=
      stalkComposite_preservesFiniteLimits S U E
        (AlgebraicClosure (S.residueField s)) (algebraicClosureEtalePointMap S s)
    exact ⟨isLimitOfPreserves
      (functor S U E ⋙ (algebraicClosureEtalePoint S s).sheafFiber) hc⟩

omit [Mono U.hom] in
/-- Finite colimits are preserved by the actual left adjoint, for
every étale object. -/
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor S U E) := by
  let : PreservesColimitsOfSize.{0, 0} (functor S U E) :=
    (adjunction S U E).leftAdjoint_preservesColimits
  infer_instance

/-- Exact extension by zero is additive on actual morphisms of sheaves. -/
instance functor_additive : (functor S U E).Additive := by
  let : HasFiniteProducts
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) := inferInstance
  let : HasBinaryProducts
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) :=
    hasLimitsOfShape_discrete
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) WalkingPair
  exact Functor.additive_of_preserves_binary_products
    (C := Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E))
    (D := Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (functor S U E)

/-- Kernels and cokernels are preserved by the actual extension functor. -/
instance functor_preservesHomology : (functor S U E).PreservesHomology := inferInstance

/-- Actual short exact sequences of module sheaves remain short exact
after extension by zero. -/
theorem map_shortExact
    (T : ShortComplex (Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)))
    (hT : T.ShortExact) : (T.map (functor S U E)).ShortExact :=
  hT.map_of_exact (functor S U E)

end PrimeGap182.TypeIII.EtaleExtensionByZero

#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.stalkComposite_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.functor_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.functor_preservesFiniteColimits
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.functor_additive
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.functor_preservesHomology
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.map_shortExact
