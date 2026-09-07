import TypeIIIConstantField
import TypeIIIPhaseObstruction
import TypeIIIArtinSchreierPhase

/-! Algebraic descent obstruction for the actual scalar radial phase list.

The result concerns field automorphisms and actual Laurent-series
Artin--Schreier classes. The geometric assertion that the wild classes of a
descended sheaf form such a finite invariant list is not asserted here.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

variable {k : Type*} [Field k] [IsAlgClosed k]

theorem rescaled_nonzero_constant_of_finite_orbit
    (F u : AlgebraicClosure (RatFunc k)) (hF : F ≠ 0) (hu : u ≠ 0)
    (horbit : (Set.range (fun σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k) => σ (F * u))).Finite) :
    ∃ d : k, d ≠ 0 ∧ F = algebraMap k (AlgebraicClosure (RatFunc k)) d / u := by
  obtain ⟨d, hd⟩ := (rationalAlgebraicClosure_finite_orbit_iff k (F * u)).mp horbit
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    exact (mul_ne_zero hF hu) (by simpa only [map_zero] using hd.symm)
  exact ⟨d, hd0, (eq_div_iff hu).mpr hd.symm⟩

omit [IsAlgClosed k] in
theorem distinctRectanglePhase_ne_zero
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (R : PhaseRectangle → AlgebraicClosure (RatFunc k))
    (hR : ∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C (γ e) - RatFunc.X)) :
    (∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e) ≠ 0 := by
  obtain ⟨A', hA', heq⟩ := rectanglePhase_normalize_root_choices s γ A R
    algebraicPhaseRoot hR algebraicPhaseRoot_sq
  rw [heq]
  exact rectangleRadialPhase_ne_zero h2 α hα m n hm hn hminj hninj s hs γ A'
    hγ (fun e he => (hA' e he).trans (hA e he)) algebraicPhaseRoot algebraicPhaseRoot_sq

/-- The rescaled coefficient of every allowed distinct-index phase has an
infinite actual orbit over the algebraically closed constant field. -/
theorem rescaled_distinctRectanglePhase_infinite_orbit
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (R : PhaseRectangle → AlgebraicClosure (RatFunc k))
    (hR : ∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C (γ e) - RatFunc.X))
    (a b : k) (u : AlgebraicClosure (RatFunc k)) (hu0 : u ≠ 0)
    (hu : u ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C a + RatFunc.C b * RatFunc.X)) :
    (Set.range (fun σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k) =>
        σ ((∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e) * u))).Infinite := by
  intro hfinite
  have hF := distinctRectanglePhase_ne_zero h2 α hα m n hm hn hminj hninj
    s hs γ A hγ hA R hR
  obtain ⟨d, hd, he⟩ := rescaled_nonzero_constant_of_finite_orbit _ u hF hu0 hfinite
  apply algebraicDistinctRectanglePhase_ne_linearReciprocalSqrt h2 α hα m n hm hn
    hminj hninj s hs γ A hγ hA R hR d a b hd u hu
  simpa only [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply] using he

/-- The same descent test holds for the actual pole-one Artin--Schreier
quotient classes, because their coefficient map is injective. -/
theorem poleOneClass_finite_orbit_iff_constant
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : AlgebraicClosure (RatFunc k)) :
    (Set.range (fun σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k) => laurentPoleOneClass p (σ x))).Finite ↔
      ∃ c : k, algebraMap k (AlgebraicClosure (RatFunc k)) c = x := by
  change (Set.range ((laurentPoleOneClass p) ∘
    (fun σ : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k) =>
      σ x))).Finite ↔ _
  rw [Set.range_comp, Set.finite_image_iff (laurentPoleOneClass_injective p).injOn]
  exact rationalAlgebraicClosure_finite_orbit_iff k x

#print axioms rescaled_nonzero_constant_of_finite_orbit
#print axioms distinctRectanglePhase_ne_zero
#print axioms rescaled_distinctRectanglePhase_infinite_orbit
#print axioms poleOneClass_finite_orbit_iff_constant

end PrimeGap182.TypeIII
