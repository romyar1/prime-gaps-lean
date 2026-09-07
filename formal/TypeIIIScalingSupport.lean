import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Bounded supports invariant under a fixed dilation

If a prime exceeds `b^D`, the first `D+1` powers of an integer `b>1`
remain distinct in characteristic `p`. Consequently, a dilation-invariant
finite set of at most `D` points in the plane is supported at the origin.

The application with `b=8` is motivated by coefficient conjugation of the
actual Type III family. This file proves the algebraic support facts; it does
not posit or construct a sheaf realization of that family.
-/

noncomputable section

namespace PrimeGap182.TypeIII.ScalingSupport

open scoped BigOperators Classical

variable {K : Type*} [Field K] {p : ℕ} [CharP K p]

/-- Before the explicit characteristic cutoff, ordinary integer powers
remain pairwise distinct after reduction. -/
theorem powers_injective_of_cutoff (b D : ℕ) (hb : 1 < b) (hp : b ^ D < p) :
    Function.Injective (fun i : Fin (D + 1) => (b : K) ^ (i : ℕ)) := by
  intro i j hij
  apply Fin.ext
  have hi : b ^ (i : ℕ) < p :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega : 0 < b) (by omega)) hp
  have hj : b ^ (j : ℕ) < p :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega : 0 < b) (by omega)) hp
  have he : b ^ (i : ℕ) = b ^ (j : ℕ) :=
    CharP.natCast_injOn_Iio K p hi hj (by simpa only [Nat.cast_pow] using hij)
  exact Nat.pow_right_injective hb he

/-- Iterating a forward-invariant plane dilation stays in the same set. -/
theorem pow_scale_mem (Z : Finset (K × K)) (a : K)
    (hZ : ∀ z ∈ Z, (a * z.1, a * z.2) ∈ Z)
    (z : K × K) (hz : z ∈ Z) (i : ℕ) :
    (a ^ i * z.1, a ^ i * z.2) ∈ Z := by
  induction i with
  | zero => simpa only [pow_zero, one_mul] using hz
  | succ i ih =>
      simpa only [pow_succ', mul_assoc] using
        hZ (a ^ i * z.1, a ^ i * z.2) ih

/-- A bounded finite support invariant under multiplication by `b` contains
no nonzero point once `p>b^D`. No classification of plane curves is used. -/
theorem finite_support_eq_origin_of_cutoff (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (Z : Finset (K × K))
    (hcard : Z.card ≤ D)
    (hZ : ∀ z ∈ Z, ((b : K) * z.1, (b : K) * z.2) ∈ Z)
    (z : K × K) (hz : z ∈ Z) : z = (0, 0) := by
  by_contra hzero
  have hcoord : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hzero (Prod.ext h.1 h.2)
  let orbit : Fin (D + 1) → Z := fun i =>
    ⟨((b : K) ^ (i : ℕ) * z.1, (b : K) ^ (i : ℕ) * z.2),
      pow_scale_mem Z (b : K) hZ z hz (i : ℕ)⟩
  have hinj : Function.Injective orbit := by
    intro i j hij
    apply powers_injective_of_cutoff (K := K) (p := p) b D hb hp
    have he := congrArg Subtype.val hij
    rcases hcoord with hx | hy
    · exact mul_right_cancel₀ hx (congrArg Prod.fst he)
    · exact mul_right_cancel₀ hy (congrArg Prod.snd he)
  have hsize : D + 1 ≤ Z.card := by
    simpa using Fintype.card_le_of_injective orbit hinj
  omega

/-- The dilation relevant to the coefficient Frobenius at the auxiliary
prime two has the concrete, uniform cutoff `8^D`. -/
theorem eight_invariant_finite_support (D : ℕ) (hp : 8 ^ D < p)
    (Z : Finset (K × K)) (hcard : Z.card ≤ D)
    (hZ : ∀ z ∈ Z, ((8 : K) * z.1, (8 : K) * z.2) ∈ Z) :
    ∀ z ∈ Z, z = (0, 0) :=
  finite_support_eq_origin_of_cutoff 8 D (by norm_num) hp Z hcard hZ

open MvPolynomial

/-- Restriction of a plane polynomial to the complete line `t ↦ (tx,ty)`. -/
def radialPolynomial (f : MvPolynomial (Fin 2) K) (x y : K) : Polynomial K :=
  MvPolynomial.aeval ![Polynomial.C x * Polynomial.X,
    Polynomial.C y * Polynomial.X] f

/-- This polynomial is the literal restriction, with the scalar variable
in the same position in both coordinates. -/
theorem eval_radialPolynomial (f : MvPolynomial (Fin 2) K) (x y t : K) :
    Polynomial.eval t (radialPolynomial f x y) =
      MvPolynomial.eval ![t * x, t * y] f := by
  change (Polynomial.aeval t : Polynomial K →ₐ[K] K)
    (MvPolynomial.aeval _ f) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v : Fin 2 → K => MvPolynomial.aeval v f)
  funext i
  fin_cases i
  · change (Polynomial.aeval t) (Polynomial.C x * Polynomial.X) = t * x
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    exact mul_comm x t
  · change (Polynomial.aeval t) (Polynomial.C y * Polynomial.X) = t * y
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    exact mul_comm y t

theorem radialPolynomial_monomial (d : Fin 2 →₀ ℕ) (c x y : K) :
    radialPolynomial (MvPolynomial.monomial d c) x y =
      Polynomial.monomial d.degree (c * x ^ d 0 * y ^ d 1) := by
  rw [radialPolynomial, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Polynomial.algebraMap_apply, mul_assoc]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  have hd : d.degree = d 0 + d 1 := by
    simp only [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [hd, pow_add]
  simp only [map_mul, map_pow, mul_pow, Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- Restriction to a line does not increase the total degree. -/
theorem natDegree_radialPolynomial_le (f : MvPolynomial (Fin 2) K) (x y : K) :
    (radialPolynomial f x y).natDegree ≤ f.totalDegree := by
  classical
  unfold radialPolynomial
  conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  change (radialPolynomial (MvPolynomial.monomial d (coeff d f)) x y).natDegree ≤ _
  rw [radialPolynomial_monomial]
  exact (Polynomial.natDegree_monomial_le _).trans (le_totalDegree hd)

/-- Every homogeneous component appears as one coefficient of the actual
line restriction. -/
theorem coeff_radialPolynomial (f : MvPolynomial (Fin 2) K) (x y : K) (n : ℕ) :
    (radialPolynomial f x y).coeff n =
      MvPolynomial.eval ![x, y] (homogeneousComponent n f) := by
  classical
  unfold radialPolynomial
  conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum, Polynomial.finsetSum_coeff]
  rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  change (radialPolynomial (MvPolynomial.monomial d (coeff d f)) x y).coeff n = _
  rw [radialPolynomial_monomial, Polynomial.coeff_monomial]
  split_ifs with hd
  · rw [MvPolynomial.eval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [mul_assoc]
  · rfl

/-- Invariance under one integer dilation supplies every successive point
on its multiplicative orbit. -/
theorem eval_pow_scale_eq_zero (f : MvPolynomial (Fin 2) K) (a : K)
    (hscale : ∀ x y, MvPolynomial.eval ![x, y] f = 0 →
      MvPolynomial.eval ![a * x, a * y] f = 0)
    (x y : K) (hxy : MvPolynomial.eval ![x, y] f = 0) (i : ℕ) :
    MvPolynomial.eval ![a ^ i * x, a ^ i * y] f = 0 := by
  induction i with
  | zero => simpa only [pow_zero, one_mul] using hxy
  | succ i ih =>
      simpa only [pow_succ', mul_assoc] using hscale (a ^ i * x) (a ^ i * y) ih

/-- If a degree-`D` zero locus is dilation-invariant and `p>b^D`, the
restriction to the line through any of its points is identically zero. -/
theorem radialPolynomial_eq_zero_of_cutoff (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hD : f.totalDegree ≤ D)
    (hscale : ∀ x y, MvPolynomial.eval ![x, y] f = 0 →
      MvPolynomial.eval ![(b : K) * x, (b : K) * y] f = 0)
    (x y : K) (hxy : MvPolynomial.eval ![x, y] f = 0) :
    radialPolynomial f x y = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (radialPolynomial f x y) (powers_injective_of_cutoff (K := K) b D hb hp)
  · intro i
    rw [eval_radialPolynomial]
    exact eval_pow_scale_eq_zero f (b : K) hscale x y hxy (i : ℕ)
  · simpa only [Fintype.card_fin] using
      lt_of_le_of_lt ((natDegree_radialPolynomial_le f x y).trans hD) (Nat.lt_succ_self D)

/-- The complete zero locus is a cone: with each point it contains its
whole line through the origin. This conclusion needs no squarefreeness or
irreducibility assumption on its defining polynomial. -/
theorem zero_locus_conical_of_cutoff (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hD : f.totalDegree ≤ D)
    (hscale : ∀ x y, MvPolynomial.eval ![x, y] f = 0 →
      MvPolynomial.eval ![(b : K) * x, (b : K) * y] f = 0)
    (x y : K) (hxy : MvPolynomial.eval ![x, y] f = 0) (t : K) :
    MvPolynomial.eval ![t * x, t * y] f = 0 := by
  rw [← eval_radialPolynomial,
    radialPolynomial_eq_zero_of_cutoff b D hb hp f hD hscale x y hxy]
  simp

/-- In particular, every homogeneous component vanishes on the original
invariant zero locus. The top nonzero component gives a homogeneous
polynomial containing all of its curve supports. -/
theorem homogeneousComponent_vanishes_of_cutoff (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hD : f.totalDegree ≤ D)
    (hscale : ∀ x y, MvPolynomial.eval ![x, y] f = 0 →
      MvPolynomial.eval ![(b : K) * x, (b : K) * y] f = 0)
    (x y : K) (hxy : MvPolynomial.eval ![x, y] f = 0) (n : ℕ) :
    MvPolynomial.eval ![x, y] (homogeneousComponent n f) = 0 := by
  rw [← coeff_radialPolynomial,
    radialPolynomial_eq_zero_of_cutoff b D hb hp f hD hscale x y hxy]
  simp

/-- The orbit argument works for an arbitrary subset of the plane; no
finiteness or algebraicity of the subset is needed. -/
theorem set_pow_scale_mem (Y : Set (K × K)) (a : K)
    (hY : ∀ z ∈ Y, (a * z.1, a * z.2) ∈ Y)
    (z : K × K) (hz : z ∈ Y) (i : ℕ) :
    (a ^ i * z.1, a ^ i * z.2) ∈ Y := by
  induction i with
  | zero => simpa only [pow_zero, one_mul] using hz
  | succ i ih =>
      simpa only [pow_succ', mul_assoc] using
        hY (a ^ i * z.1, a ^ i * z.2) ih

/-- A bounded-degree polynomial vanishing on an invariant subset vanishes
on the complete line through each of its points. The whole zero locus of
the polynomial need not be invariant. -/
theorem radialPolynomial_eq_zero_of_invariant_subset (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hD : f.totalDegree ≤ D) (Y : Set (K × K))
    (hY : ∀ z ∈ Y, ((b : K) * z.1, (b : K) * z.2) ∈ Y)
    (hvanish : ∀ z ∈ Y, MvPolynomial.eval ![z.1, z.2] f = 0)
    (z : K × K) (hz : z ∈ Y) :
    radialPolynomial f z.1 z.2 = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (radialPolynomial f z.1 z.2)
    (powers_injective_of_cutoff (K := K) (p := p) b D hb hp)
  · intro i
    rw [eval_radialPolynomial]
    exact hvanish (((b : K) ^ (i : ℕ) * z.1), ((b : K) ^ (i : ℕ) * z.2))
      (set_pow_scale_mem Y (b : K) hY z hz (i : ℕ))
  · simpa only [Fintype.card_fin] using
      lt_of_le_of_lt ((natDegree_radialPolynomial_le f z.1 z.2).trans hD)
        (Nat.lt_succ_self D)

/-- Every homogeneous component vanishes on the invariant subset. This
does not assert that the subset itself contains all scalar multiples. -/
theorem homogeneousComponent_vanishes_on_invariant_subset (b D : ℕ)
    (hb : 1 < b) (hp : b ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hD : f.totalDegree ≤ D) (Y : Set (K × K))
    (hY : ∀ z ∈ Y, ((b : K) * z.1, (b : K) * z.2) ∈ Y)
    (hvanish : ∀ z ∈ Y, MvPolynomial.eval ![z.1, z.2] f = 0)
    (z : K × K) (hz : z ∈ Y) (n : ℕ) :
    MvPolynomial.eval ![z.1, z.2] (homogeneousComponent n f) = 0 := by
  rw [← coeff_radialPolynomial,
    radialPolynomial_eq_zero_of_invariant_subset b D hb hp f hD Y hY hvanish z hz]
  simp

/-- The explicit dilation-eight specialization used after the geometric
coefficient-conjugation step, once a bounded-degree containing polynomial
has been supplied. -/
theorem eight_invariant_subset_homogeneous_components (D : ℕ)
    (hp : 8 ^ D < p) (f : MvPolynomial (Fin 2) K)
    (hD : f.totalDegree ≤ D) (Y : Set (K × K))
    (hY : ∀ z ∈ Y, ((8 : K) * z.1, (8 : K) * z.2) ∈ Y)
    (hvanish : ∀ z ∈ Y, MvPolynomial.eval ![z.1, z.2] f = 0)
    (z : K × K) (hz : z ∈ Y) (n : ℕ) :
    MvPolynomial.eval ![z.1, z.2] (homogeneousComponent n f) = 0 :=
  homogeneousComponent_vanishes_on_invariant_subset 8 D (by norm_num)
    hp f hD Y hY hvanish z hz n

#print axioms powers_injective_of_cutoff
#print axioms pow_scale_mem
#print axioms finite_support_eq_origin_of_cutoff
#print axioms eight_invariant_finite_support
#print axioms eval_radialPolynomial
#print axioms radialPolynomial_monomial
#print axioms natDegree_radialPolynomial_le
#print axioms coeff_radialPolynomial
#print axioms eval_pow_scale_eq_zero
#print axioms radialPolynomial_eq_zero_of_cutoff
#print axioms zero_locus_conical_of_cutoff
#print axioms homogeneousComponent_vanishes_of_cutoff
#print axioms set_pow_scale_mem
#print axioms radialPolynomial_eq_zero_of_invariant_subset
#print axioms homogeneousComponent_vanishes_on_invariant_subset
#print axioms eight_invariant_subset_homogeneous_components

end PrimeGap182.TypeIII.ScalingSupport
