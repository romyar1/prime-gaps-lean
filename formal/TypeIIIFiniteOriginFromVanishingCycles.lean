import TypeIIIPublishedLocalConstruction

/-!
# The finite-origin maps from the vanishing-cycle sequence

Laumon section 2.3.2 gives the sequence from the generic Fourier stalk
through vanishing cycles to the closed stalk. Proposition 2.3.2.1(iii),
Lemma 2.4.2.1(ii) and Definition 2.4.2.3 identify its middle term with
the infinity-to-zero local Fourier transform. The inputs below retain
that sequence and comparison after the same quadratic pullback and wild
restriction. The original FiniteOriginData maps and their exactness are
constructed by transport through this comparison.

These are explicit geometric inputs, not a constructed sheaf model or
an assumed phase decomposition for the Type III family.
https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf, pp. 159--163.
-/

noncomputable section

namespace PrimeGap182.TypeIII.FiniteOriginFromVanishingCycles

open PublishedLocalConstruction PublishedPhaseApplication

universe u v w t q

variable {E : Type v} [Field E]

/-- Changing the middle vector space by an equivalence preserves the
exactness of the two original maps, with inverse transport on the second. -/
theorem exact_transport {U V W V' : Type*}
    [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [AddCommGroup V'] [Module E V']
    (f : U →ₗ[E] V) (g : V →ₗ[E] W) (e : V ≃ₗ[E] V')
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (e.toLinearMap.comp f) =
      LinearMap.ker (g.comp e.symm.toLinearMap) := by
  ext y
  change (∃ x, e (f x) = y) ↔ g (e.symm y) = 0
  constructor
  · rintro ⟨x, rfl⟩
    rw [e.symm_apply_apply]
    exact LinearMap.mem_ker.mp (h ▸ (show f x ∈ LinearMap.range f from ⟨x, rfl⟩))
  · intro hy
    have hx : e.symm y ∈ LinearMap.ker g := LinearMap.mem_ker.mpr hy
    rw [← h] at hx
    obtain ⟨x, hx⟩ := hx
    exact ⟨x, by rw [hx, e.apply_symm_apply]⟩

variable {K : Type u} [Field K] {I : Type w} [Group I] {G : Type t} [Group G]

/-- General nearby/vanishing-cycle data on perverse objects Q. All terms
and maps already use the same radial pullback and wild restriction.
The local comparison is a representation equivalence, not a rank equality.
No origin-rank premise or family-specific phase statement is included. -/
structure Inputs (Q : Type q) (F : LocalFourierData K E I G) where
  infinity : Q → FDRep E I
  infinity_admissible : ∀ P, F.Admissible (infinity P)
  nearby : (a : PhaseField K) → a ≠ 0 → Q → FDRep E G
  vanishing : (a : PhaseField K) → a ≠ 0 → Q → FDRep E G
  closed : (a : PhaseField K) → a ≠ 0 → Q → FDRep E G
  nearbyToVanishing : ∀ a ha P,
    Representation.IntertwiningMap (nearby a ha P).ρ (vanishing a ha P).ρ
  vanishingToClosed : ∀ a ha P,
    Representation.IntertwiningMap (vanishing a ha P).ρ (closed a ha P).ρ
  localComparison : ∀ a ha P,
    Representation.Equiv (vanishing a ha P).ρ
      ((F.operation a ha).obj (infinity P) (infinity_admissible P)).ρ
  exactness : ∀ a ha P,
    LinearMap.range (nearbyToVanishing a ha P).toLinearMap =
      LinearMap.ker (vanishingToClosed a ha P).toLinearMap
  closedConstant : ∀ a ha P, Representation.IsTrivial (closed a ha P).ρ

variable {Q : Type q} {F : LocalFourierData K E I G} (S : Inputs Q F)

/-- Both original finite-origin arrows are transported through the same
local-Fourier comparison. Their source and closed target are retained. -/
def Inputs.finiteOriginData : FiniteOriginData Q F where
  infinity := S.infinity
  infinity_admissible := S.infinity_admissible
  origin := S.nearby
  boundary := S.closed
  toVanishing a ha P :=
    (S.localComparison a ha P).toIntertwiningMap.comp (S.nearbyToVanishing a ha P)
  toBoundary a ha P :=
    (S.vanishingToClosed a ha P).comp (S.localComparison a ha P).symm.toIntertwiningMap

/-- Laumon's general exact sequence and closed-stalk inertia property
give the exact original rules used by the rank-exhaustion argument. -/
theorem Inputs.finiteOriginRules (p : ℕ) [Fact p.Prime] [CharP K p] :
    FiniteOriginRules p S.finiteOriginData where
  exact _ a ha P := exact_transport
    (S.nearbyToVanishing a ha P).toLinearMap
    (S.vanishingToClosed a ha P).toLinearMap
    (S.localComparison a ha P).toLinearEquiv (S.exactness a ha P)
  constant _ a ha P := S.closedConstant a ha P

end PrimeGap182.TypeIII.FiniteOriginFromVanishingCycles

#print axioms PrimeGap182.TypeIII.FiniteOriginFromVanishingCycles.exact_transport
#print axioms PrimeGap182.TypeIII.FiniteOriginFromVanishingCycles.Inputs.finiteOriginData
#print axioms PrimeGap182.TypeIII.FiniteOriginFromVanishingCycles.Inputs.finiteOriginRules
