import TypeIIITorsionCoefficientQuotient
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Neighborhoods in the actual coefficient limit

The kernels of the original finite-level projections form a decreasing
basis of open neighborhoods of zero for the already constructed topology.
This is a statement about the actual compatible-sequence ring and its
product subspace topology. The proved algebraic kernel computation then
identifies this topology with the topology defined by powers of (ℓ).
Finite freeness over the ℓ-adic integers also proves that the ring is
Noetherian. These are coefficient-ring results, not cohomology comparisons.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open Filter Set
open scoped Topology

attribute [local instance] torsionCoefficientLevelTopology
  torsionCoefficientLevel_discreteTopology

/-- The actual finite-level projection kernel as an ideal of the limit ring. -/
abbrev torsionCoefficientLimitKernel (p ell n : ℕ) : Ideal (TorsionCoefficientLimit p ell) :=
  RingHom.ker (torsionCoefficientLimitProjection p ell n)

/-- Compatibility makes the actual kernels decrease with the coefficient level. -/
theorem torsionCoefficientLimitKernel_antitone (p ell : ℕ) :
    Antitone (torsionCoefficientLimitKernel p ell) := by
  intro m n hmn x hx
  change torsionCoefficientLimitProjection p ell n x = 0 at hx
  change torsionCoefficientLimitProjection p ell m x = 0
  rw [← RingHom.congr_fun (torsionCoefficientLimitProjection_compatible p ell hmn) x]
  change torsionCoefficientReduce p ell hmn (torsionCoefficientLimitProjection p ell n x) = 0
  rw [hx, map_zero]

/-- Each actual projection kernel is open in the previously defined topology. -/
theorem torsionCoefficientLimitKernel_isOpen (p ell n : ℕ) :
    IsOpen (torsionCoefficientLimitKernel p ell n : Set (TorsionCoefficientLimit p ell)) := by
  change IsOpen ((torsionCoefficientLimitProjection p ell n) ⁻¹' {0})
  exact (isOpen_discrete _).preimage (torsionCoefficientLimitProjection_continuous p ell n)

/-- The original projection kernels form a neighborhood basis at zero. -/
theorem torsionCoefficientLimitKernel_hasBasis (p ell : ℕ) :
    (𝓝 (0 : TorsionCoefficientLimit p ell)).HasBasis (fun _ : ℕ => True)
      (fun n => (torsionCoefficientLimitKernel p ell n : Set (TorsionCoefficientLimit p ell))) := by
  have hn : 𝓝 (0 : TorsionCoefficientLimit p ell) =
      ⨅ n : ℕ, 𝓟 (torsionCoefficientLimitKernel p ell n : Set (TorsionCoefficientLimit p ell)) := by
    change @nhds _ (TopologicalSpace.induced (fun x : TorsionCoefficientLimit p ell => x.val) _)
      (0 : TorsionCoefficientLimit p ell) = _
    rw [nhds_induced, nhds_pi, Filter.pi, Filter.comap_iInf]
    simp only [nhds_discrete, Filter.comap_comap]
    simp only [Filter.comap_pure]
    apply iInf_congr
    intro n
    apply congrArg Filter.principal
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  rw [hn]
  apply Filter.hasBasis_iInf_principal
  intro i j
  exact ⟨max i j,
    torsionCoefficientLimitKernel_antitone p ell (le_max_left i j),
    torsionCoefficientLimitKernel_antitone p ell (le_max_right i j)⟩

/-- The existing topology is precisely the topology defined by powers of (ℓ). -/
theorem torsionCoefficientLimit_isAdic (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] :
    IsAdic (Ideal.span {(ell : TorsionCoefficientLimit p ell)}) := by
  rw [isAdic_iff]
  constructor
  · intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [Ideal.span_singleton_pow, ← torsionCoefficientLimitProjection_ker p ell n]
      exact torsionCoefficientLimitKernel_isOpen p ell n
  · intro U hU
    obtain ⟨n, _, hn⟩ := (torsionCoefficientLimitKernel_hasBasis p ell).mem_iff.mp hU
    refine ⟨n + 1, ?_⟩
    rw [Ideal.span_singleton_pow, ← torsionCoefficientLimitProjection_ker p ell n]
    exact hn

/-- The actual finite free ℤ_[ℓ]-algebra is a Noetherian ring. -/
instance torsionCoefficientLimit_isNoetherianRing (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] : IsNoetherianRing (TorsionCoefficientLimit p ell) :=
  isNoetherian_of_tower ℤ_[ell] (S := TorsionCoefficientLimit p ell)
    (M := TorsionCoefficientLimit p ell) inferInstance

#print axioms torsionCoefficientLimitKernel
#print axioms torsionCoefficientLimitKernel_antitone
#print axioms torsionCoefficientLimitKernel_isOpen
#print axioms torsionCoefficientLimitKernel_hasBasis
#print axioms torsionCoefficientLimit_isAdic
#print axioms torsionCoefficientLimit_isNoetherianRing

end PrimeGap182.TypeIII
