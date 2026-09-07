import TypeIIIFourierCRT
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Finite-product CRT Fourier factorization

The local characters are the restrictions of the actual standard character through CRT.
Their frequency multipliers are proved to be units.  Thus all local frequencies are actual
reductions followed by invertible scalings; neither a factorization nor its nondegeneracy is
an assumption.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

private theorem addChar_sum {A : Type*} [AddCommMonoid A]
    {ι : Type*} (s : Finset ι) (ψ : AddChar A ℂ) (x : ι → A) :
    ψ (∑ i ∈ s, x i) = ∏ i ∈ s, ψ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- Every character of the actual cyclic residue ring is a standard-character shift. -/
theorem addChar_eq_std_mul (n : ℕ) [NeZero n] (ψ : AddChar (ZMod n) ℂ) :
    ∃ a : ZMod n, ∀ x, ψ x = ZMod.stdAddChar (a * x) := by
  have hi : Function.Injective (ZMod.stdAddChar (N := n)).mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (ZMod.isPrimitive_stdAddChar n)
  have hb : Function.Bijective (ZMod.stdAddChar (N := n)).mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hi, (AddChar.card_eq (α := ZMod n)).symm⟩
  obtain ⟨a, ha⟩ := hb.surjective ψ
  refine ⟨a, fun x => ?_⟩
  simpa only [AddChar.mulShift_apply] using (DFunLike.congr_fun ha x).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard character restricted to one actual CRT coordinate. -/
def crtLocalAddChar (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : ι) :
    AddChar (ZMod (q i)) ℂ where
  toFun x := ZMod.stdAddChar ((ZMod.prodEquivPi q hc).symm (Pi.single i x))
  map_zero_eq_one' := by simp only [Pi.single_zero, map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by
    rw [Pi.single_add, map_add, AddChar.map_add_eq_mul]

/-- Restriction along a CRT coordinate preserves injectivity of the standard character. -/
theorem crtLocalAddChar_injective (q : ι → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : ι) :
    Function.Injective (crtLocalAddChar q hc i) :=
  ZMod.injective_stdAddChar.comp
    ((ZMod.prodEquivPi q hc).symm.injective.comp (Pi.single_injective i))

/-- The actual local CRT character has an invertible frequency multiplier. -/
theorem exists_crtFrequencyUnit (q : ι → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : ι) :
    ∃ u : (ZMod (q i))ˣ, ∀ x,
      crtLocalAddChar q hc i x = ZMod.stdAddChar ((u : ZMod (q i)) * x) := by
  obtain ⟨a, ha⟩ := addChar_eq_std_mul (q i) (crtLocalAddChar q hc i)
  have hi : Function.Injective (a * ·) := by
    intro x y hxy
    dsimp only at hxy
    apply crtLocalAddChar_injective q hc i
    rw [ha, ha, hxy]
  have hu : IsUnit a := IsUnit.isUnit_iff_mulLeft_bijective.mpr
    (Finite.injective_iff_bijective.mp hi)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, ha⟩

/-- A choice of the uniquely determined local character multiplier. -/
def crtFrequencyUnit (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : ι) : (ZMod (q i))ˣ :=
  Classical.choose (exists_crtFrequencyUnit q hc i)

theorem crtLocalAddChar_eq_std (q : ι → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : ι) (x : ZMod (q i)) :
    crtLocalAddChar q hc i x =
      ZMod.stdAddChar ((crtFrequencyUnit q hc i : ZMod (q i)) * x) :=
  Classical.choose_spec (exists_crtFrequencyUnit q hc i) x

/-- Exact decomposition of the standard character into its actual CRT restrictions. -/
theorem stdAddChar_finite_crt (q : ι → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (z : ZMod (∏ i, q i)) :
    ZMod.stdAddChar z = ∏ i,
      ZMod.stdAddChar ((crtFrequencyUnit q hc i : ZMod (q i)) * (z.val : ZMod (q i))) := by
  let e := ZMod.prodEquivPi q hc
  have hz : z = ∑ i, e.symm (Pi.single i (e z i)) := by
    rw [← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
  calc
    _ = ZMod.stdAddChar (∑ i, e.symm (Pi.single i (e z i))) := congrArg _ hz
    _ = ∏ i, crtLocalAddChar q hc i (e z i) := addChar_sum _ _ _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [crtLocalAddChar_eq_std]
      congr 2
      exact crt_coordinates q hc z i

/-- A product of local functions evaluated at the actual prime-power or prime reductions. -/
def crtProduct (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (F : ∀ i, ZMod (q i) → ZMod (q i) → ℂ)
    (x y : ZMod (∏ i, q i)) : ℂ :=
  ∏ i, F i (x.val : ZMod (q i)) (y.val : ZMod (q i))

/-- Exact finite-product Fourier factorization, valid also for the empty factor family. -/
theorem fourier₂_crtProduct (q : ι → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (F : ∀ i, ZMod (q i) → ZMod (q i) → ℂ) (H K : ZMod (∏ i, q i)) :
    fourier₂ (∏ i, q i) (crtProduct q F) H K =
      ∏ i, fourier₂ (q i) (F i)
        ((crtFrequencyUnit q hc i : ZMod (q i)) * (H.val : ZMod (q i)))
        ((crtFrequencyUnit q hc i : ZMod (q i)) * (K.val : ZMod (q i))) := by
  let e := ZMod.prodEquivPi q hc
  let G (i : ι) (x y : ZMod (q i)) := F i x y * ZMod.stdAddChar
    (((crtFrequencyUnit q hc i : ZMod (q i)) * e H i) * x +
      ((crtFrequencyUnit q hc i : ZMod (q i)) * e K i) * y)
  have hterm (x y : ZMod (∏ i, q i)) :
      crtProduct q F x y * ZMod.stdAddChar (H * x + K * y) =
        ∏ i, G i (e x i) (e y i) := by
    rw [stdAddChar_finite_crt q hc]
    simp only [crtProduct, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hcoord := crt_coordinates q hc (H * x + K * y) i
    simp only [map_add, map_mul, Pi.add_apply, Pi.mul_apply] at hcoord
    rw [← hcoord]
    simp only [G, e, crt_coordinates]
    congr 2
    ring
  calc
    _ = ∑ x : ZMod (∏ i, q i), ∑ y : ZMod (∏ i, q i),
        ∏ i, G i (e x i) (e y i) := by simp only [fourier₂, hterm]
    _ = ∑ x : ∀ i, ZMod (q i), ∑ y : ∀ i, ZMod (q i), ∏ i, G i (x i) (y i) := by
      refine Fintype.sum_equiv e.toEquiv _ _ ?_
      intro x
      refine Fintype.sum_equiv e.toEquiv _ _ ?_
      intro y
      rfl
    _ = ∏ i, ∑ x : ZMod (q i), ∑ y : ZMod (q i), G i x y := by
      simp_rw [← Fintype.prod_sum]
      exact (Fintype.prod_sum (fun i x => ∑ y, G i x y)).symm
    _ = _ := by
      simp only [G, e, crt_coordinates, fourier₂]

theorem norm_fourier₂_crtProduct (q : ι → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (F : ∀ i, ZMod (q i) → ZMod (q i) → ℂ) (H K : ZMod (∏ i, q i)) :
    ‖fourier₂ (∏ i, q i) (crtProduct q F) H K‖ =
      ∏ i, ‖fourier₂ (q i) (F i)
        ((crtFrequencyUnit q hc i : ZMod (q i)) * (H.val : ZMod (q i)))
        ((crtFrequencyUnit q hc i : ZMod (q i)) * (K.val : ZMod (q i)))‖ := by
  rw [fourier₂_crtProduct q hc, norm_prod]

#print axioms addChar_eq_std_mul
#print axioms exists_crtFrequencyUnit
#print axioms stdAddChar_finite_crt
#print axioms fourier₂_crtProduct
#print axioms norm_fourier₂_crtProduct

end

end PrimeGap182.TypeIII
