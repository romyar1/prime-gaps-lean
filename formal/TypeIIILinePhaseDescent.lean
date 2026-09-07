import TypeIIIPublishedLocalPhases

/-!
# The finite-set descent obstruction for rectangle phases

The automorphisms and rational-function algebraic closure in this file are
the actual field-theoretic objects.  Finiteness comes from the proved
rectangle phase set.  Invariance under constant-field automorphisms remains
an explicit hypothesis; no sheaf, local Fourier realization, or origin-line
exclusion is postulated by these definitions.
-/

noncomputable section

open scoped Classical

namespace PrimeGap182.TypeIII

variable {k : Type*} [Field k]

/-- A nonzero direction defines a nonzero linear rational function, also
when one of its coordinates vanishes. -/
theorem ratFunc_direction_ne_zero (a b : k) (hab : (a, b) ≠ (0, 0)) :
    (RatFunc.C a + RatFunc.C b * RatFunc.X : RatFunc k) ≠ 0 := by
  have hpoly : (Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial k) ≠ 0 := by
    intro h
    apply hab
    apply Prod.ext
    · simpa using congrArg (fun P : Polynomial k => P.coeff 0) h
    · simpa using congrArg (fun P : Polynomial k => P.coeff 1) h
  simpa only [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X] using
    RatFunc.algebraMap_ne_zero hpoly

/-- Every square root of a nonzero direction remains nonzero in the
actual extension field. -/
theorem linearDirectionRoot_ne_zero
    {L : Type*} [Field L] [Algebra (RatFunc k) L]
    (a b : k) (hab : (a, b) ≠ (0, 0)) (u : L)
    (hu : u ^ 2 = algebraMap (RatFunc k) L
      (RatFunc.C a + RatFunc.C b * RatFunc.X)) : u ≠ 0 := by
  have hlinear : algebraMap (RatFunc k) L
      (RatFunc.C a + RatFunc.C b * RatFunc.X) ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap (RatFunc k) L).injective.ne (ratFunc_direction_ne_zero a b hab)
  intro hzero
  apply hlinear
  simpa only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hu.symm

section ConstantField

variable [IsAlgClosed k]

/-- A nonzero member of a finite set whose rescaling is invariant under
all constant-field automorphisms is a nonzero constant divided by that
rescaling factor.  The conclusion uses the original element. -/
theorem constant_div_of_mem_rescaled_finite_invariant_set
    (S : Set (AlgebraicClosure (RatFunc k))) (hS : S.Finite)
    (u : AlgebraicClosure (RatFunc k)) (hu : u ≠ 0)
    (hstable : ∀ σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
        AlgebraicClosure (RatFunc k),
      ∀ x ∈ (fun β => u * β) '' S, σ x ∈ (fun β => u * β) '' S)
    (β : AlgebraicClosure (RatFunc k)) (hβ : β ∈ S) (hβ0 : β ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ β = algebraMap k (AlgebraicClosure (RatFunc k)) c / u := by
  obtain ⟨c, hc⟩ := constant_of_mem_finite_invariant_set
    (rationalAlgebraicClosure_trdeg k).le ((fun β => u * β) '' S)
    (hS.image _) hstable (Set.mem_image_of_mem _ hβ)
  have hc0 : c ≠ 0 := by
    intro hz
    subst c
    exact (mul_ne_zero hu hβ0) (by simpa only [map_zero] using hc.symm)
  refine ⟨c, hc0, ?_⟩
  rw [hc, mul_div_cancel_left₀ β hu]

/-- A nonempty subset of the actual allowed rectangle phases cannot have
an invariant finite rescaling by a square root of a linear direction.
No finiteness assumption is needed: it follows from the phase equations. -/
theorem rectangleAllowedPhases_no_nonempty_rescaled_invariant_subset
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty)
    (a b : k) (u : AlgebraicClosure (RatFunc k)) (hu0 : u ≠ 0)
    (hu : u ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C a + RatFunc.C b * RatFunc.X))
    (S : Set (AlgebraicClosure (RatFunc k))) (hSne : S.Nonempty)
    (hSsub : S ⊆ rectangleAllowedPhases α m n s)
    (hstable : ∀ σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
        AlgebraicClosure (RatFunc k),
      ∀ x ∈ (fun β => u * β) '' S, σ x ∈ (fun β => u * β) '' S) : False := by
  obtain ⟨β, hβ⟩ := hSne
  have hβallowed := hSsub hβ
  have hβ0 : β ≠ 0 := by
    intro hz
    subst β
    exact zero_not_mem_rectangleAllowedPhases h2 α hα m n hm hn hminj hninj
      s hs hβallowed
  have hSfinite := (rectangleAllowedPhases_finite α m n s).subset hSsub
  obtain ⟨c, hc0, hc⟩ := constant_div_of_mem_rescaled_finite_invariant_set
    S hSfinite u hu0 hstable β hβ hβ0
  apply linearReciprocalSqrt_not_mem_rectangleAllowedPhases h2 α hα m n hm hn
    hminj hninj s hs c a b hc0 u hu
  have heq : β = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C c) / u := by
    simpa only [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply] using hc
  exact heq ▸ hβallowed

end ConstantField

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.ratFunc_direction_ne_zero
#print axioms PrimeGap182.TypeIII.linearDirectionRoot_ne_zero
#print axioms PrimeGap182.TypeIII.constant_div_of_mem_rescaled_finite_invariant_set
#print axioms PrimeGap182.TypeIII.rectangleAllowedPhases_no_nonempty_rescaled_invariant_subset
