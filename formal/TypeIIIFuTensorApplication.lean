import TypeIIIFuPhaseCoordinates
import TypeIIIPublishedLocalPhases

/-!
# Scalar application of Fu's local phase equations to tensor products

This file uses the literal squared-phase equation following the checked
change of variables.  It proves the scalar containment for every sum of
such local coefficients, choosing all root witnesses simultaneously.

No representation, sheaf, or local Fourier theorem is defined here.  An
actual local Fourier realization must supply the individual squared-phase
equations and the tensor-character sum law.  Once it does, containment in
the existing rectangle phase set is a theorem, not an additional premise.
-/

noncomputable section

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

variable {k : Type*} [Field k]

/-- The scalar relation delivered by one cubic local Fourier block after
the generic angular and quadratic radial changes of variables. -/
def FuCubicSquaredPhase (α m n : k) (β : AlgebraicClosure (RatFunc k)) : Prop :=
  ∃ γ : k, γ ^ 3 = m / n ∧
    β ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (fuRadialPhaseSquare α m γ)

/-- The checked squared-phase equation produces all the witnesses in the
original local phase set, without selecting a preferred sign. -/
theorem fuCubicSquaredPhase_mem_cubicAllowedLocalPhases [IsAlgClosed k]
    (h2 : (2 : k) ≠ 0) (α m n : k) (hα : α ≠ 0) (hm : m ≠ 0)
    (β : AlgebraicClosure (RatFunc k)) (hβ : FuCubicSquaredPhase α m n β) :
    β ∈ cubicAllowedLocalPhases α m n := by
  obtain ⟨γ, hγ, hsq⟩ := hβ
  obtain ⟨A, R, hA, hR, heq⟩ :=
    fu_phase_has_radial_coordinates h2 α m γ hα hm β hsq
  exact ⟨γ, A, R, hγ, hA, hR, heq⟩

/-- Conversely, every independent-root phase satisfies the literal Fu
square equation. This direction needs no algebraic-closedness assumption. -/
theorem fuCubicSquaredPhase_of_mem_cubicAllowedLocalPhases
    (α m n : k) (β : AlgebraicClosure (RatFunc k))
    (hβ : β ∈ cubicAllowedLocalPhases α m n) :
    FuCubicSquaredPhase α m n β := by
  obtain ⟨γ, A, R, hγ, hA, hR, rfl⟩ := hβ
  refine ⟨γ, hγ, ?_⟩
  rw [Algebra.smul_def, mul_pow, hR]
  calc
    _ = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
        ((radialPhaseScalar A γ) ^ 2 * (RatFunc.C γ - RatFunc.X)) := by
      rw [map_mul, map_pow]
    _ = _ := congrArg (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)))
      (radialPhaseScalar_sq_mul_linear α m γ A hA)

/-- Simultaneous choices of the per-entry witnesses give membership of
the actual sum in the original rectangle phase set. This also allows an
empty subset or repeated rows and columns. -/
theorem sum_mem_rectangleAllowedPhases_of_localPhases
    (α : k) (m n : Fin 2 → k) (s : Finset PhaseRectangle)
    (β : PhaseRectangle → AlgebraicClosure (RatFunc k))
    (hβ : ∀ e ∈ s, β e ∈ cubicAllowedLocalPhases α (m e.1) (n e.2)) :
    (∑ e ∈ s, β e) ∈ rectangleAllowedPhases α m n s := by
  have hw : ∀ e : PhaseRectangle, ∃ γ A : k,
      ∃ R : AlgebraicClosure (RatFunc k), e ∈ s →
        γ ^ 3 = m e.1 / n e.2 ∧ A ^ 2 = 4 * α / m e.1 ∧
        R ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
          (RatFunc.C γ - RatFunc.X) ∧ β e = radialPhaseScalar A γ • R := by
    intro e
    by_cases he : e ∈ s
    · obtain ⟨γ, A, R, hγ, hA, hR, heq⟩ := hβ e he
      exact ⟨γ, A, R, fun _ => ⟨hγ, hA, hR, heq⟩⟩
    · exact ⟨0, 0, 0, fun h => False.elim (he h)⟩
  choose γ A R hw using hw
  refine ⟨γ, A, R, (fun e he => (hw e he).1),
    (fun e he => (hw e he).2.1), (fun e he => (hw e he).2.2.1), ?_⟩
  apply Finset.sum_congr rfl
  intro e he
  exact (hw e he).2.2.2

/-- The tensor scalar containment follows from the individual squared
phases. Noncancellation and descent exclusions are separate theorems and
do not occur among this statement's hypotheses. -/
theorem sum_mem_rectangleAllowedPhases_of_fuSquaredPhases [IsAlgClosed k]
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (s : Finset PhaseRectangle)
    (β : PhaseRectangle → AlgebraicClosure (RatFunc k))
    (hβ : ∀ e ∈ s, FuCubicSquaredPhase α (m e.1) (n e.2) (β e)) :
    (∑ e ∈ s, β e) ∈ rectangleAllowedPhases α m n s := by
  apply sum_mem_rectangleAllowedPhases_of_localPhases α m n s β
  intro e he
  exact fuCubicSquaredPhase_mem_cubicAllowedLocalPhases h2 α (m e.1) (n e.2)
    hα (hm e.1) (β e) (hβ e he)

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.FuCubicSquaredPhase
#print axioms PrimeGap182.TypeIII.fuCubicSquaredPhase_mem_cubicAllowedLocalPhases
#print axioms PrimeGap182.TypeIII.fuCubicSquaredPhase_of_mem_cubicAllowedLocalPhases
#print axioms PrimeGap182.TypeIII.sum_mem_rectangleAllowedPhases_of_localPhases
#print axioms PrimeGap182.TypeIII.sum_mem_rectangleAllowedPhases_of_fuSquaredPhases
