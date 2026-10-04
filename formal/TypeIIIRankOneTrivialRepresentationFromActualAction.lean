import TypeIIIRegularTameBasisFromFiniteJordanExponential

/-!
# Rank-one nearby triviality from the actual action and dimension

The universal unramified-nearby and local/generic dimension comparisons for
lisse sheaves may supply the two exact premises below. Their rank-one
application constructs the full trivial representation equivalence without
an independently assumed lisse-rank-one model or selected AS equivalence.
No sheaf or inertia foundations are rebuilt or claimed.
-/
noncomputable section

namespace PrimeGap182.TypeIII.RankOneTrivialRepresentationFromActualAction

universe u v w
variable {k : Type u} [Field k] {H : Type v} [Group H]
  {V : Type w} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- Every actual rank-one representation with trivial group action is fully
isomorphic to the standard coefficient line with its actual trivial action. -/
def rankOneTrivialEquiv (rho : Representation k H V)
    (action : ∀ g, rho g = 1) (dimension : Module.finrank k V = 1) :
    Representation.Equiv rho (Representation.trivial k H k) := by
  let e : V ≃ₗ[k] k := LinearEquiv.ofFinrankEq V k (by simpa only [Module.finrank_self] using dimension)
  refine Representation.Equiv.mk e ?_
  intro g
  change e.toLinearMap ∘ₗ rho g = LinearMap.id ∘ₗ e.toLinearMap
  rw [action g]
  rfl

end PrimeGap182.TypeIII.RankOneTrivialRepresentationFromActualAction
