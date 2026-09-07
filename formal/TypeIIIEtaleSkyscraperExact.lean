import TypeIIIEtaleCohomology
import TypeIIIEtaleInverseImageStalk
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Exactness of the actual module skyscraper functor

The skyscraper attached to an actual point of the small étale site is
the existing right adjoint of that point's stalk functor. Its value on
an étale object is the product of copies of the original coefficient
module indexed by the point's actual fiber. Products of modules are
exact, so this functor is exact. The exact stalk adjunction also proves
that it preserves injective objects.

These assertions hold for every coefficient ring. They concern the
original module-valued skyscraper and do not identify different
coefficient categories or assert proper base change.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleSkyscraper

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u})
  (Φ : GrothendieckTopology.Point.{u} S.smallEtaleTopology)
  (E : Type u) [Ring E]

/-- The existing skyscraper functor of this actual étale-site point. -/
def functor : ModuleCat.{u} E ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  Φ.skyscraperSheafFunctor

/-- Its original adjunction to the actual stalk functor. -/
def adjunction : Φ.sheafFiber (A := ModuleCat.{u} E) ⊣ functor S Φ E :=
  Φ.skyscraperSheafAdjunction

/-- The skyscraper is a right adjoint through the original stalk adjunction. -/
instance functor_isRightAdjoint : (functor S Φ E).IsRightAdjoint :=
  (adjunction S Φ E).isRightAdjoint

/-- Its actual limits are preserved by that right adjunction. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor S Φ E) :=
  inferInstance

/-- The original skyscraper maps are additive. -/
instance functor_additive : (functor S Φ E).Additive :=
  Functor.additive_of_preserves_binary_products _

set_option backward.isDefEq.respectTransparency false in
/-- Products of the original surjective module maps give an epimorphism
on every étale object, hence on the actual sheaves. -/
instance functor_preservesEpimorphisms : (functor S Φ E).PreservesEpimorphisms where
  preserves {M N} f hf := by
    have : ∀ U, Epi (((functor S Φ E).map f).hom.app U) := by
      intro U
      let τ : Discrete.functor (fun (_ : Φ.fiber.obj U.unop) => M) ⟶
          Discrete.functor (fun (_ : Φ.fiber.obj U.unop) => N) :=
        Discrete.natTrans (fun _ => f)
      have : ∀ i, Epi (τ.app i) := fun _ => hf
      have : Epi τ := NatTrans.epi_of_epi_app τ
      change Epi ((lim (J := Discrete (Φ.fiber.obj U.unop)) (C := ModuleCat.{u} E)).map τ)
      exact Functor.map_epi _ τ
    have : Epi ((functor S Φ E).map f).hom := NatTrans.epi_of_epi_app _
    exact Sheaf.Hom.epi_of_presheaf_epi S.smallEtaleTopology (ModuleCat.{u} E) _

/-- Left exactness together with the proved epimorphism preservation
makes the original skyscraper functor exact. -/
instance functor_preservesHomology : (functor S Φ E).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- In particular, the original skyscraper preserves finite colimits. -/
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor S Φ E) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Injectives are preserved because the original left adjoint is the
exact stalk functor. -/
instance functor_preservesInjectiveObjects : (functor S Φ E).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (adjunction S Φ E)

/-- Actual short exact sequences of modules remain short exact as
skyscraper sheaves on the original site. -/
theorem map_shortExact (T : ShortComplex (ModuleCat.{u} E)) (hT : T.ShortExact) :
    (T.map (functor S Φ E)).ShortExact := hT.map_of_exact (functor S Φ E)

#print axioms functor
#print axioms adjunction
#print axioms functor_isRightAdjoint
#print axioms functor_preservesFiniteLimits
#print axioms functor_additive
#print axioms functor_preservesEpimorphisms
#print axioms functor_preservesHomology
#print axioms functor_preservesFiniteColimits
#print axioms functor_preservesInjectiveObjects
#print axioms map_shortExact

end PrimeGap182.TypeIII.EtaleSkyscraper
