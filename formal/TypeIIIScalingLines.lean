import TypeIIICurveProjection
import TypeIIIScalingSupport

/-!
# Finite line covers of homogeneous plane zero loci

A nonzero homogeneous binary polynomial of degree n has a zero locus
contained in at most n+1 proper lines through the origin. The construction
uses its actual dehomogenization f(T,1), its finite set of roots, and the
line y=0. Containment works over any field; algebraic closedness is not
required.

Applying the construction to the top homogeneous component and the
dilation theorem in TypeIIIScalingSupport gives a line cover for a
bounded-degree zero locus invariant under one integer dilation. More
generally, the subset to be covered may be invariant inside an arbitrary
bounded-degree zero locus; invariance of the containing zero locus is not
required.
-/

noncomputable section

open scoped Classical
open MvPolynomial

namespace PrimeGap182.TypeIII.ScalingLines

variable {K : Type*} [Field K]

/-- The line defined by a homogeneous linear equation. Nonzero
coefficients are required in the theorems asserting properness. -/
def originLine (a b : K) : Set (K × K) :=
  {z | a * z.1 + b * z.2 = 0}

@[simp] theorem zero_mem_originLine (a b : K) :
    (0, 0) ∈ originLine a b := by
  simp [originLine]

/-- A nonzero coefficient pair defines a proper subset of the plane. -/
theorem originLine_ne_univ (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    originLine a b ≠ Set.univ := by
  intro h
  rcases hab with ha | hb
  · have hz : (1, 0) ∈ originLine a b := by rw [h]; trivial
    exact ha (by simpa [originLine] using hz)
  · have hz : (0, 1) ∈ originLine a b := by rw [h]; trivial
    exact hb (by simpa [originLine] using hz)

/-- The extra chart-boundary line is the ordinary horizontal axis. -/
theorem originLine_axis :
    originLine (0 : K) 1 = Set.range (fun t : K => (t, 0)) := by
  ext z
  constructor
  · intro hz
    have hy : z.2 = 0 := by simpa [originLine] using hz
    exact ⟨z.1, Prod.ext rfl hy.symm⟩
  · rintro ⟨t, rfl⟩
    simp [originLine]

/-- Every other line in the cover is parametrized by a nonzero direction
vector (a,1). -/
theorem originLine_graph (a : K) :
    originLine 1 (-a) = Set.range (fun t : K => (a * t, t)) := by
  ext z
  constructor
  · intro hz
    have hxy : z.1 = a * z.2 := by
      apply sub_eq_zero.mp
      simpa [originLine, sub_eq_add_neg] using hz
    exact ⟨z.2, Prod.ext hxy.symm rfl⟩
  · rintro ⟨t, rfl⟩
    simp [originLine]

/-- The literal polynomial f(T,1). -/
def dehomogenize (f : MvPolynomial (Fin 2) K) : Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, 1] f

theorem dehomogenize_natDegree_le (f : MvPolynomial (Fin 2) K) :
    (dehomogenize f).natDegree ≤ f.totalDegree :=
  CurvePolynomial.dehomogenize_natDegree_le f

/-- Homogeneity prevents loss of a nonzero polynomial on this chart. -/
theorem dehomogenize_ne_zero {f : MvPolynomial (Fin 2) K} {n : ℕ}
    (hf : f ≠ 0) (hh : f.IsHomogeneous n) : dehomogenize f ≠ 0 := by
  have hrec : (dehomogenize f).homogenize n = f :=
    Polynomial.homogenize_eq_of_isHomogeneous hh rfl
  intro hzero
  apply hf
  rw [← hrec, hzero, Polynomial.homogenize_zero]

/-- On the chart y≠0, the root direction is x/y. The factor y^n is
retained explicitly, including degree zero. -/
theorem eval_homogeneous_of_second_ne_zero
    {f : MvPolynomial (Fin 2) K} {n : ℕ}
    (hh : f.IsHomogeneous n) (x y : K) (hy : y ≠ 0) :
    MvPolynomial.eval ![x, y] f =
      (dehomogenize f).eval (x / y) * y ^ n := by
  have hrec : (dehomogenize f).homogenize n = f :=
    Polynomial.homogenize_eq_of_isHomogeneous hh rfl
  simpa only [hrec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
    Polynomial.eval_homogenize
      ((dehomogenize_natDegree_le f).trans hh.totalDegree_le) ![x, y] hy

/-- Explicit coefficient pairs for the axis and the finitely many root
directions of a univariate polynomial. -/
def lineNormals (q : Polynomial K) : Finset (K × K) :=
  insert (0, 1) (q.roots.toFinset.image (fun a => (1, -a)))

theorem lineNormals_card_le (q : Polynomial K) :
    (lineNormals q).card ≤ q.natDegree + 1 := by
  apply (Finset.card_insert_le _ _).trans
  apply Nat.add_le_add_right
  exact Finset.card_image_le.trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' q))

theorem lineNormals_nonzero (q : Polynomial K) (l : K × K)
    (hl : l ∈ lineNormals q) : l.1 ≠ 0 ∨ l.2 ≠ 0 := by
  rcases Finset.mem_insert.mp hl with rfl | hl
  · exact Or.inr one_ne_zero
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
    exact Or.inl one_ne_zero

/-- A zero away from the chart boundary supplies an actual root of
f(T,1), hence one of the explicit lines in the finite cover. -/
theorem homogeneous_zero_mem_line
    {f : MvPolynomial (Fin 2) K} {n : ℕ}
    (hf : f ≠ 0) (hh : f.IsHomogeneous n)
    (x y : K) (hxy : MvPolynomial.eval ![x, y] f = 0) :
    ∃ l ∈ lineNormals (dehomogenize f), (x, y) ∈ originLine l.1 l.2 := by
  by_cases hy : y = 0
  · refine ⟨(0, 1), Finset.mem_insert_self _ _, ?_⟩
    simp [originLine, hy]
  · have hroot : (dehomogenize f).IsRoot (x / y) := by
      have he := (eval_homogeneous_of_second_ne_zero hh x y hy).symm.trans hxy
      exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero n hy)
    refine ⟨(1, -(x / y)), Finset.mem_insert_of_mem ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨x / y, Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (dehomogenize_ne_zero hf hh)).mpr hroot), rfl⟩
    · simp [originLine, div_mul_cancel₀ x hy]

/-- Nonzero homogeneous binary forms have uniformly bounded covers by
proper origin lines, without a factorization or irreducibility premise. -/
theorem homogeneous_zero_locus_line_cover
    {f : MvPolynomial (Fin 2) K} {n : ℕ}
    (hf : f ≠ 0) (hh : f.IsHomogeneous n) :
    ∃ L : Finset (K × K), L.card ≤ n + 1 ∧
      (∀ l ∈ L, l.1 ≠ 0 ∨ l.2 ≠ 0) ∧
      ∀ x y, MvPolynomial.eval ![x, y] f = 0 →
        ∃ l ∈ L, (x, y) ∈ originLine l.1 l.2 := by
  refine ⟨lineNormals (dehomogenize f), ?_, lineNormals_nonzero _, ?_⟩
  · exact (lineNormals_card_le _).trans
      (Nat.add_le_add_right
        ((dehomogenize_natDegree_le f).trans hh.totalDegree_le) 1)
  · exact homogeneous_zero_mem_line hf hh

/-- The same cover as a finite family of actual proper subsets of the
plane. Each member is a line defined by a nonzero homogeneous linear
equation and contains the origin. -/
theorem homogeneous_zero_locus_finite_line_sets
    {f : MvPolynomial (Fin 2) K} {n : ℕ}
    (hf : f ≠ 0) (hh : f.IsHomogeneous n) :
    ∃ L : Finset (Set (K × K)), L.card ≤ n + 1 ∧
      (∀ l ∈ L, (0, 0) ∈ l ∧ l ≠ Set.univ ∧
        ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧ l = originLine a b) ∧
      ∀ x y, MvPolynomial.eval ![x, y] f = 0 → ∃ l ∈ L, (x, y) ∈ l := by
  obtain ⟨N, hcard, hproper, hcover⟩ := homogeneous_zero_locus_line_cover hf hh
  refine ⟨N.image (fun l => originLine l.1 l.2),
    Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro l hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨zero_mem_originLine _ _, originLine_ne_univ _ _ (hproper a ha),
      a.1, a.2, hproper a ha, rfl⟩
  · intro x y hxy
    obtain ⟨a, ha, hxa⟩ := hcover x y hxy
    exact ⟨originLine a.1 a.2, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hxa⟩

/-- The top nonzero homogeneous component of any plane polynomial has a
cover controlled by the original total degree. -/
theorem top_component_line_cover
    {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    ∃ L : Finset (K × K), L.card ≤ f.totalDegree + 1 ∧
      (∀ l ∈ L, l.1 ≠ 0 ∨ l.2 ≠ 0) ∧
      ∀ x y, MvPolynomial.eval ![x, y] (homogeneousComponent f.totalDegree f) = 0 →
        ∃ l ∈ L, (x, y) ∈ originLine l.1 l.2 :=
  homogeneous_zero_locus_line_cover
    (CurveProjection.topHomogeneousComponent_ne_zero hf)
    (homogeneousComponent_isHomogeneous f.totalDegree f)

/-- A bounded-degree plane zero locus invariant under integer dilation
lies in at most D+1 proper origin lines once p>b^D. Only the polynomial
invariance premise is used; there is no sheaf or Fourier-bound premise. -/
theorem zero_locus_line_cover_of_cutoff
    {p : ℕ} [CharP K p] (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hf : f ≠ 0) (hD : f.totalDegree ≤ D)
    (hscale : ∀ x y, MvPolynomial.eval ![x, y] f = 0 →
      MvPolynomial.eval ![(b : K) * x, (b : K) * y] f = 0) :
    ∃ L : Finset (K × K), L.card ≤ D + 1 ∧
      (∀ l ∈ L, l.1 ≠ 0 ∨ l.2 ≠ 0) ∧
      ∀ x y, MvPolynomial.eval ![x, y] f = 0 →
        ∃ l ∈ L, (x, y) ∈ originLine l.1 l.2 := by
  obtain ⟨L, hcard, hproper, hcover⟩ := top_component_line_cover hf
  refine ⟨L, hcard.trans (Nat.add_le_add_right hD 1), hproper, ?_⟩
  intro x y hxy
  apply hcover
  exact ScalingSupport.homogeneousComponent_vanishes_of_cutoff
    b D hb hp f hD hscale x y hxy f.totalDegree

/-- It suffices that the subset being covered is invariant and lies in
a bounded-degree zero locus. The containing zero locus need not itself
be invariant under dilation. -/
theorem invariant_subset_line_cover_of_cutoff
    {p : ℕ} [CharP K p] (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hf : f ≠ 0) (hD : f.totalDegree ≤ D) (Y : Set (K × K))
    (hY : ∀ z ∈ Y, ((b : K) * z.1, (b : K) * z.2) ∈ Y)
    (hvanish : ∀ z ∈ Y, MvPolynomial.eval ![z.1, z.2] f = 0) :
    ∃ L : Finset (K × K), L.card ≤ D + 1 ∧
      (∀ l ∈ L, l.1 ≠ 0 ∨ l.2 ≠ 0) ∧
      ∀ z ∈ Y, ∃ l ∈ L, z ∈ originLine l.1 l.2 := by
  obtain ⟨L, hcard, hproper, hcover⟩ := top_component_line_cover hf
  refine ⟨L, hcard.trans (Nat.add_le_add_right hD 1), hproper, ?_⟩
  intro z hz
  exact hcover z.1 z.2
    (ScalingSupport.homogeneousComponent_vanishes_on_invariant_subset
      b D hb hp f hD Y hY hvanish z hz f.totalDegree)

/-- Dilation by eight gives the explicit characteristic cutoff used by
the Type III coefficient-conjugation support argument. -/
theorem eight_invariant_subset_line_cover
    {p : ℕ} [CharP K p] (D : ℕ) (hp : 8 ^ D < p)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hD : f.totalDegree ≤ D)
    (Y : Set (K × K))
    (hY : ∀ z ∈ Y, ((8 : K) * z.1, (8 : K) * z.2) ∈ Y)
    (hvanish : ∀ z ∈ Y, MvPolynomial.eval ![z.1, z.2] f = 0) :
    ∃ L : Finset (K × K), L.card ≤ D + 1 ∧
      (∀ l ∈ L, l.1 ≠ 0 ∨ l.2 ≠ 0) ∧
      ∀ z ∈ Y, ∃ l ∈ L, z ∈ originLine l.1 l.2 :=
  invariant_subset_line_cover_of_cutoff 8 D (by norm_num)
    hp f hf hD Y hY hvanish

#print axioms zero_mem_originLine
#print axioms originLine_ne_univ
#print axioms originLine_axis
#print axioms originLine_graph
#print axioms dehomogenize_natDegree_le
#print axioms dehomogenize_ne_zero
#print axioms eval_homogeneous_of_second_ne_zero
#print axioms lineNormals_card_le
#print axioms lineNormals_nonzero
#print axioms homogeneous_zero_mem_line
#print axioms homogeneous_zero_locus_line_cover
#print axioms homogeneous_zero_locus_finite_line_sets
#print axioms top_component_line_cover
#print axioms zero_locus_line_cover_of_cutoff
#print axioms invariant_subset_line_cover_of_cutoff
#print axioms eight_invariant_subset_line_cover

end PrimeGap182.TypeIII.ScalingLines
