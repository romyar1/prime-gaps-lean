import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Descent of an idempotent relation to a finite subalgebra

Suppose A is a commutative integral R-algebra and a(a - 1) belongs
to the extension of an ideal I of R.  An actual finite linear-combination
witness for this membership has only finitely many coefficients in A.
Adjoining a and these coefficients gives a subalgebra finite as an
R-module, in which the same relation belongs to the extended ideal.

The construction does not assume that contracting I A to R[a] gives
I R[a].  It retains the coefficients of the original ideal-membership
witness.  No localness, henselianity, freeness, or nontriviality is
required, and the base and algebra may have independent universes.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.IntegralAlgebraFiniteDescent

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]

/-- Membership in the actual extended ideal has a finitely supported
coefficient witness indexed by elements of the original ideal. -/
theorem exists_finsupp_witness (I : Ideal R) (x : A)
    (h : x ∈ I.map (algebraMap R A)) :
    ∃ c : I →₀ A, c.sum (fun i u => u * algebraMap R A i.1) = x := by
  change x ∈ Submodule.span A ((algebraMap R A) '' (I : Set R)) at h
  rw [Set.image_eq_range] at h
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h
  exact ⟨c, by simpa only [smul_eq_mul] using! hc⟩

variable [Algebra.IsIntegral R A]

/-- Adjoining a and the finitely many membership coefficients gives an
actual finite subalgebra containing the same idempotent relation. -/
theorem exists_finite_subalgebra (I : Ideal R) (a : A)
    (h : a * (a - 1) ∈ I.map (algebraMap R A)) :
    ∃ B : Subalgebra R A, Module.Finite R B ∧
      ∃ b : B, (b : A) = a ∧ b * (b - 1) ∈ I.map (algebraMap R B) := by
  classical
  obtain ⟨c, hc⟩ := exists_finsupp_witness I (a * (a - 1)) h
  let s : Finset A := insert a (c.support.image c)
  let B : Subalgebra R A := Algebra.adjoin R (s : Set A)
  have hfinite : Module.Finite R B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  have ha : a ∈ B := Algebra.subset_adjoin (Finset.mem_insert_self _ _)
  let b : B := ⟨a, ha⟩
  have hcoeff : ∀ i ∈ c.support, c i ∈ B := by
    intro i hi
    apply Algebra.subset_adjoin
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  let cB : c.support → B := fun i => ⟨c i.1, hcoeff i.1 i.2⟩
  have hsum :
      (∑ i : c.support, cB i * algebraMap R B i.1.1) = b * (b - 1) := by
    apply Subtype.ext
    change B.val (∑ i : c.support, cB i * algebraMap R B i.1.1) = a * (a - 1)
    simp only [map_sum, map_mul, AlgHom.commutes]
    change (∑ i : c.support, c i.1 * algebraMap R A i.1.1) = a * (a - 1)
    rw [Finset.sum_coe_sort c.support (fun i : I => c i * algebraMap R A i.1)]
    exact hc
  refine ⟨B, hfinite, b, rfl, ?_⟩
  rw [← hsum]
  refine (I.map (algebraMap R B)).sum_mem ?_
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R B) i.1.2)

end PrimeGap182.TypeIII.IntegralAlgebraFiniteDescent

#print axioms PrimeGap182.TypeIII.IntegralAlgebraFiniteDescent.exists_finsupp_witness
#print axioms PrimeGap182.TypeIII.IntegralAlgebraFiniteDescent.exists_finite_subalgebra
