import TypeIIIAlgebraicDescent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Exact rank exhaustion and the literal rectangle phase set

The linear-algebra statement retains the direction of the local
vanishing-cycle map `H → V`.  Its exactness and the vanishing of the
outgoing map are explicit premises; it does not construct a local Fourier
transform or assert an inertia realization.

The phase set is defined by the actual cube, amplitude-square, and
independent square-root equations.  Its finiteness and its two exclusions
are unconditional algebraic theorems.  Identifying an actual sheaf's wild
characters with this set is a separate geometric application of the
published local Fourier theorems, not a premise hidden in the definition.
-/

noncomputable section

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

universe u v w x

/-- The actual map in an exact local sequence is bijective once its
outgoing map vanishes and its source and target have the same finite rank. -/
theorem localFourier_exhaustion_of_exact_rank
    {E : Type u} [Field E]
    {H : Type v} [AddCommGroup H] [Module E H] [FiniteDimensional E H]
    {V : Type w} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {T : Type x} [AddCommGroup T] [Module E T]
    (f : H →ₗ[E] V) (g : V →ₗ[E] T)
    (hexact : LinearMap.range f = LinearMap.ker g) (hg : g = 0)
    (hrank : Module.finrank E H = Module.finrank E V) :
    Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    simpa only [hg, LinearMap.ker_zero] using hexact
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj,
    hsurj⟩

/-- The equivalence has precisely the original local-sequence map as its
forward linear map. -/
def localFourierExhaustionEquiv
    {E : Type u} [Field E]
    {H : Type v} [AddCommGroup H] [Module E H] [FiniteDimensional E H]
    {V : Type w} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {T : Type x} [AddCommGroup T] [Module E T]
    (f : H →ₗ[E] V) (g : V →ₗ[E] T)
    (hexact : LinearMap.range f = LinearMap.ker g) (hg : g = 0)
    (hrank : Module.finrank E H = Module.finrank E V) : H ≃ₗ[E] V :=
  LinearEquiv.ofBijective f (localFourier_exhaustion_of_exact_rank f g hexact hg hrank)

theorem localFourierExhaustionEquiv_apply
    {E : Type u} [Field E]
    {H : Type v} [AddCommGroup H] [Module E H] [FiniteDimensional E H]
    {V : Type w} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {T : Type x} [AddCommGroup T] [Module E T]
    (f : H →ₗ[E] V) (g : V →ₗ[E] T)
    (hexact : LinearMap.range f = LinearMap.ker g) (hg : g = 0)
    (hrank : Module.finrank E H = Module.finrank E V) (h : H) :
    localFourierExhaustionEquiv f g hexact hg hrank h = f h := rfl

variable {k : Type u} [Field k]

/-- Positive-power equations have finitely many solutions over any field;
no separability or characteristic assumption is needed. -/
theorem localPhase_power_fiber_finite (n : ℕ) (hn : 0 < n) (a : k) :
    Set.Finite {z : k | z ^ n = a} := by
  simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using
    Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hn a)

/-- Possible scalar coefficients from one cubic local Fourier block,
including every independent choice of amplitude and square root. -/
def cubicAllowedLocalPhases (α m n : k) : Set (AlgebraicClosure (RatFunc k)) :=
  {β | ∃ γ A : k, ∃ R : AlgebraicClosure (RatFunc k),
    γ ^ 3 = m / n ∧ A ^ 2 = 4 * α / m ∧
    R ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C γ - RatFunc.X) ∧
    β = radialPhaseScalar A γ • R}

theorem cubicAllowedLocalPhases_finite (α m n : k) :
    (cubicAllowedLocalPhases α m n).Finite := by
  have hfinite :
      (⋃ γ ∈ {γ : k | γ ^ 3 = m / n},
        ⋃ A ∈ {A : k | A ^ 2 = 4 * α / m},
          (fun R : AlgebraicClosure (RatFunc k) => radialPhaseScalar A γ • R) ''
            {R | R ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
              (RatFunc.C γ - RatFunc.X)}).Finite :=
    (localPhase_power_fiber_finite 3 (by omega) (m / n)).biUnion fun γ _ =>
      (localPhase_power_fiber_finite 2 (by omega) (4 * α / m)).biUnion fun A _ =>
        (localPhase_power_fiber_finite 2 (by omega)
          (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
            (RatFunc.C γ - RatFunc.X))).image _
  apply hfinite.subset
  intro β hβ
  obtain ⟨γ, A, R, hγ, hA, hR, hβ⟩ := hβ
  exact Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion.mpr ⟨hγ,
    Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr ⟨hA, ⟨R, hR, hβ.symm⟩⟩⟩⟩⟩

/-- The literal possible phase sums for a specified subset of the four
rectangle entries. No row/column distinctness is built into this set. -/
def rectangleAllowedPhases (α : k) (m n : Fin 2 → k) (s : Finset PhaseRectangle) :
    Set (AlgebraicClosure (RatFunc k)) :=
  {β | ∃ γ A : PhaseRectangle → k,
    ∃ R : PhaseRectangle → AlgebraicClosure (RatFunc k),
    (∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2) ∧
    (∀ e ∈ s, A e ^ 2 = 4 * α / m e.1) ∧
    (∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C (γ e) - RatFunc.X)) ∧
    β = ∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e}

theorem mem_rectangleAllowedPhases_iff
    (α : k) (m n : Fin 2 → k) (s : Finset PhaseRectangle)
    (β : AlgebraicClosure (RatFunc k)) :
    β ∈ rectangleAllowedPhases α m n s ↔
      ∃ γ A : PhaseRectangle → k,
      ∃ R : PhaseRectangle → AlgebraicClosure (RatFunc k),
        (∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2) ∧
        (∀ e ∈ s, A e ^ 2 = 4 * α / m e.1) ∧
        (∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
          (RatFunc.C (γ e) - RatFunc.X)) ∧
        β = ∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e := Iff.rfl

theorem rectangleAllowedPhases_finite
    (α : k) (m n : Fin 2 → k) (s : Finset PhaseRectangle) :
    (rectangleAllowedPhases α m n s).Finite := by
  let S : PhaseRectangle → Set (AlgebraicClosure (RatFunc k)) := fun e =>
    if e ∈ s then cubicAllowedLocalPhases α (m e.1) (n e.2) else {0}
  have hS : ∀ e, (S e).Finite := by
    intro e
    dsimp only [S]
    split_ifs
    · exact cubicAllowedLocalPhases_finite α _ _
    · exact Set.finite_singleton 0
  have hfinite := (Set.Finite.pi' hS).image
    (fun F : PhaseRectangle → AlgebraicClosure (RatFunc k) => ∑ e ∈ s, F e)
  apply hfinite.subset
  intro β hβ
  obtain ⟨γ, A, R, hγ, hA, hR, hβ⟩ := hβ
  let F : PhaseRectangle → AlgebraicClosure (RatFunc k) := fun e =>
    if e ∈ s then radialPhaseScalar (A e) (γ e) • R e else 0
  refine ⟨F, ?_, ?_⟩
  · intro e
    by_cases he : e ∈ s
    · simp only [S, F, ite_eq_left he]
      exact ⟨γ e, A e, R e, hγ e he, hA e he, hR e he, rfl⟩
    · simp only [S, F, ite_eq_right he, Set.mem_singleton_iff]
  · rw [hβ]
    apply Finset.sum_congr rfl
    intro e he
    exact ite_eq_left he

/-- Every nonempty distinct-row, distinct-column phase sum is nonzero. -/
theorem zero_not_mem_rectangleAllowedPhases
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) :
    (0 : AlgebraicClosure (RatFunc k)) ∉ rectangleAllowedPhases α m n s := by
  intro h
  obtain ⟨γ, A, R, hγ, hA, hR, hphase⟩ := h
  exact distinctRectanglePhase_ne_zero h2 α hα m n hm hn hminj hninj
    s hs γ A hγ hA R hR hphase.symm

/-- The entire allowed list avoids every nonzero constant divided by a
square root of a linear function, not merely a selected branch. -/
theorem linearReciprocalSqrt_not_mem_rectangleAllowedPhases
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty)
    (d a b : k) (hd : d ≠ 0) (u : AlgebraicClosure (RatFunc k))
    (hu : u ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C a + RatFunc.C b * RatFunc.X)) :
    algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) (RatFunc.C d) / u ∉
      rectangleAllowedPhases α m n s := by
  intro h
  obtain ⟨γ, A, R, hγ, hA, hR, hphase⟩ := h
  exact algebraicDistinctRectanglePhase_ne_linearReciprocalSqrt h2 α hα m n hm hn
    hminj hninj s hs γ A hγ hA R hR d a b hd u hu hphase.symm

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.localFourier_exhaustion_of_exact_rank
#print axioms PrimeGap182.TypeIII.localFourierExhaustionEquiv
#print axioms PrimeGap182.TypeIII.localFourierExhaustionEquiv_apply
#print axioms PrimeGap182.TypeIII.localPhase_power_fiber_finite
#print axioms PrimeGap182.TypeIII.cubicAllowedLocalPhases
#print axioms PrimeGap182.TypeIII.cubicAllowedLocalPhases_finite
#print axioms PrimeGap182.TypeIII.rectangleAllowedPhases
#print axioms PrimeGap182.TypeIII.mem_rectangleAllowedPhases_iff
#print axioms PrimeGap182.TypeIII.rectangleAllowedPhases_finite
#print axioms PrimeGap182.TypeIII.zero_not_mem_rectangleAllowedPhases
#print axioms PrimeGap182.TypeIII.linearReciprocalSqrt_not_mem_rectangleAllowedPhases
