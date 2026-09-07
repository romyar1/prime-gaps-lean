import TypeIIIScalingLines
import TypeIIICurveTangents
import Mathlib.Algebra.BigOperators.Associated

/-!
# Irreducible components of an invariant bounded proper support

The coefficient-transport identity for a Fourier complex makes the union
of its proper simple supports invariant. It need not fix each constituent.
This file works with that union as a literal subset of the plane. Given a
bounded-degree containing polynomial, the existing dilation argument and
the Nullstellensatz put each irreducible curve component into one origin
line. The containing polynomial itself need not be invariant.

These are algebraic deductions. A sheaf application must supply the actual
support union, its degree bound, and its coefficient-transport invariance.
-/

noncomputable section
open scoped BigOperators Classical
open MvPolynomial

namespace PrimeGap182.TypeIII.InvariantSupportComponents

variable {K : Type*} [Field K]

def linePolynomial (l : K × K) : MvPolynomial (Fin 2) K :=
  C l.1 * X 0 + C l.2 * X 1

@[simp] theorem eval_linePolynomial (l : K × K) (x : Fin 2 → K) :
    eval x (linePolynomial l) = l.1 * x 0 + l.2 * x 1 := by
  simp [linePolynomial]

/-- An irreducible curve contained in a finite union of lines is contained
in one of the lines. The proof uses actual polynomial divisibility. -/
theorem irreducible_curve_in_one_line [IsAlgClosed K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (L : Finset (K × K))
    (hcover : ∀ x : Fin 2 → K, eval x f = 0 →
      ∃ l ∈ L, l.1 * x 0 + l.2 * x 1 = 0) :
    ∃ l ∈ L, ∀ x : Fin 2 → K, eval x f = 0 →
      l.1 * x 0 + l.2 * x 1 = 0 := by
  have hdiv : f ∣ ∏ l ∈ L, linePolynomial l := by
    apply CurvePolynomial.irreducible_dvd_of_zeroLocus_vanishing hf
    intro x hx
    obtain ⟨l, hl, hzero⟩ := hcover x hx
    rw [map_prod]
    apply Finset.prod_eq_zero hl
    simpa only [eval_linePolynomial] using hzero
  obtain ⟨l, hl, hfl⟩ := (hf.prime.dvd_finsetProd_iff linePolynomial).mp hdiv
  refine ⟨l, hl, ?_⟩
  intro x hx
  obtain ⟨g, hg⟩ := hfl
  have he : eval x (linePolynomial l) = 0 := by
    rw [hg, map_mul, hx, zero_mul]
  simpa only [eval_linePolynomial] using he

/-- Only the union is required to be invariant. An individual curve
component can be permuted with other components by coefficient change. -/
theorem curve_component_in_origin_line [IsAlgClosed K]
    {p : ℕ} [CharP K p] (D : ℕ) (hp : 8 ^ D < p)
    (F : MvPolynomial (Fin 2) K) (hF : F ≠ 0) (hD : F.totalDegree ≤ D)
    (Y : Set (K × K))
    (hY : ∀ z ∈ Y, ((8 : K) * z.1, (8 : K) * z.2) ∈ Y)
    (hvan : ∀ z ∈ Y, eval ![z.1, z.2] F = 0)
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (hsub : ∀ x : Fin 2 → K, eval x f = 0 → (x 0, x 1) ∈ Y) :
    ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ x : Fin 2 → K, eval x f = 0 → a * x 0 + b * x 1 = 0 := by
  obtain ⟨L, _, hproper, hcover⟩ :=
    ScalingLines.eight_invariant_subset_line_cover D hp F hF hD Y hY hvan
  obtain ⟨l, hl, hline⟩ := irreducible_curve_in_one_line f hf L
    (fun x hx => hcover (x 0, x 1) (hsub x hx))
  exact ⟨l.1, l.2, hproper l hl, hline⟩

/-- The separate union of punctual supports is finite and invariant.
It therefore consists only of the origin after the same explicit cutoff. -/
theorem punctual_component_eq_origin
    {p : ℕ} [CharP K p] (D : ℕ) (hp : 8 ^ D < p)
    (Z : Finset (K × K)) (hcard : Z.card ≤ D)
    (hZ : ∀ z ∈ Z, ((8 : K) * z.1, (8 : K) * z.2) ∈ Z)
    (z : K × K) (hz : z ∈ Z) : z = (0, 0) :=
  ScalingSupport.eight_invariant_finite_support D hp Z hcard hZ z hz

#print axioms linePolynomial
#print axioms eval_linePolynomial
#print axioms irreducible_curve_in_one_line
#print axioms curve_component_in_origin_line
#print axioms punctual_component_eq_origin

end PrimeGap182.TypeIII.InvariantSupportComponents
