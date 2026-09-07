import TypeIIISubpower
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# All-width decay summation for the nonzero Type III frequencies

The slope is arbitrary positive. In particular the eventual frequency scale may be below
one. The proof uses the actual integral of a decreasing power envelope.
-/

open Set Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The positive-half-line envelope with arbitrary positive slope. -/
def positiveFrequencyDecay (a A x : ℝ) : ℝ := (1 + a * x) ^ (-A)

theorem positiveFrequencyDecay_nonneg {a : ℝ} (ha : 0 ≤ a) (A : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ positiveFrequencyDecay a A x := Real.rpow_nonneg (by nlinarith) _

/-- Actual integrability and exact integral for the decay envelope. -/
theorem positiveFrequencyDecay_integral {a A : ℝ} (ha : 0 < a) (hA : 1 < A) :
    IntegrableOn (positiveFrequencyDecay a A) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), positiveFrequencyDecay a A x) = 1 / (a * (A - 1)) := by
  let F (x : ℝ) := (1 + a * x) ^ (1 - A) / (a * (1 - A))
  have ha' : a ≠ 0 := ha.ne'
  have hA' : 1 - A ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F (positiveFrequencyDecay a A x) x := by
    intro x hx
    have hbase : 0 < 1 + a * x := by nlinarith [mem_Ici.mp hx]
    have hd := (((hasDerivAt_id x).const_mul a).const_add 1).rpow_const (p := 1 - A)
      (Or.inl hbase.ne')
    have hd' := hd.div_const (a * (1 - A))
    convert! hd' using 1
    dsimp only [positiveFrequencyDecay, id_eq]
    rw [show 1 - A - 1 = -A by ring]
    field_simp
  have htbase : Tendsto (fun x : ℝ => 1 + a * x) atTop atTop :=
    tendsto_const_nhds.add_atTop (Filter.Tendsto.const_mul_atTop ha tendsto_id)
  have ht : Tendsto F atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (show 0 < A - 1 by linarith)).comp htbase
    have hp' : Tendsto (fun x : ℝ => (1 + a * x) ^ (1 - A)) atTop (𝓝 0) := by
      simpa only [neg_sub, Function.comp_def] using hp
    simpa only [F, zero_div] using hp'.div_const (a * (1 - A))
  have hn (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : 0 ≤ positiveFrequencyDecay a A x :=
    positiveFrequencyDecay_nonneg ha.le A hx.le
  have hi := integrableOn_Ioi_deriv_of_nonneg' hderiv hn ht
  refine ⟨hi, ?_⟩
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hi ht
  rw [heq]
  simp only [F, mul_zero, add_zero, Real.one_rpow, zero_sub]
  field_simp [ha', hA', show A - 1 ≠ 0 by linarith]
  ring

theorem positiveFrequencyDecay_antitone {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) :
    AntitoneOn (positiveFrequencyDecay a A) (Ici 0) := by
  intro x hx y hy hxy
  apply Real.rpow_le_rpow_of_nonpos
  · have : 0 ≤ x := mem_Ici.mp hx
    nlinarith
  · gcongr
  · linarith

/-- The positive multiples are summable with the exact integral majorant. -/
theorem positiveFrequencyDecay_tsum {a A : ℝ} (ha : 0 < a) (hA : 1 < A) :
    Summable (fun n : ℕ => positiveFrequencyDecay a A (n + 1)) ∧
      (∑' n : ℕ, positiveFrequencyDecay a A (n + 1)) ≤ 1 / (a * (A - 1)) := by
  have hi := positiveFrequencyDecay_integral ha hA
  have hanti := positiveFrequencyDecay_antitone ha.le (by linarith : 0 ≤ A)
  have hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ positiveFrequencyDecay a A x :=
    fun x hx => positiveFrequencyDecay_nonneg ha.le A hx.le
  have hs := hanti.summable_of_integrableOn_Ioi_zero hi.1 hn
  refine ⟨?_, ?_⟩
  · have hh := hs.comp_injective (add_left_injective (1 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using hh
  · have hh := hanti.tsum_add_one_le_integral hi.1 hn
    simpa only [Nat.cast_add, Nat.cast_one, hi.2] using hh

/-- The actual nonzero integer envelope. -/
def integerFrequencyDecay (a A : ℝ) (c : ℤ) : ℝ :=
  if c = 0 then 0 else positiveFrequencyDecay a A |(c : ℝ)|

@[simp] theorem integerFrequencyDecay_zero (a A : ℝ) : integerFrequencyDecay a A 0 = 0 := by
  simp only [integerFrequencyDecay, ite_true]

@[simp] theorem integerFrequencyDecay_neg (a A : ℝ) (c : ℤ) :
    integerFrequencyDecay a A (-c) = integerFrequencyDecay a A c := by
  simp only [integerFrequencyDecay, neg_eq_zero, Int.cast_neg, abs_neg]

theorem integerFrequencyDecay_nonneg {a : ℝ} (ha : 0 ≤ a) (A : ℝ) (c : ℤ) :
    0 ≤ integerFrequencyDecay a A c := by
  unfold integerFrequencyDecay
  split_ifs
  · exact le_rfl
  · exact positiveFrequencyDecay_nonneg ha A (abs_nonneg _)

/-- The actual signed nonzero frequencies have total mass at most twice the half-line integral. -/
theorem integerFrequencyDecay_tsum {a A : ℝ} (ha : 0 < a) (hA : 1 < A) :
    Summable (integerFrequencyDecay a A) ∧
      (∑' c : ℤ, integerFrequencyDecay a A c) ≤ 2 / (a * (A - 1)) := by
  have hpos := positiveFrequencyDecay_tsum ha hA
  have hsucc (n : ℕ) : integerFrequencyDecay a A ((n : ℤ) + 1) =
      positiveFrequencyDecay a A ((n : ℝ) + 1) := by
    rw [integerFrequencyDecay, ite_eq_right (by omega)]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
  have hneg : (fun n : ℕ => integerFrequencyDecay a A (-(n + 1))) =
      fun n : ℕ => positiveFrequencyDecay a A (n + 1) := by
    funext n
    rw [integerFrequencyDecay_neg, hsucc]
  have hnatSum : Summable (fun n : ℕ => integerFrequencyDecay a A n) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, hsucc] using hpos.1
  have hnegSum : Summable (fun n : ℕ => integerFrequencyDecay a A (-(n + 1))) := by
    simpa only [hneg] using hpos.1
  refine ⟨hnatSum.of_nat_of_neg_add_one hnegSum, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hnatSum hnegSum, hneg]
  have hnatVal : (∑' n : ℕ, integerFrequencyDecay a A n) =
      ∑' n : ℕ, positiveFrequencyDecay a A (n + 1) := by
    rw [hnatSum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, integerFrequencyDecay_zero, zero_add,
      Nat.cast_add, Nat.cast_one, hsucc]
  rw [hnatVal]
  calc
    _ ≤ 1 / (a * (A - 1)) + 1 / (a * (A - 1)) := add_le_add hpos.2 hpos.2
    _ = _ := by ring

#print axioms positiveFrequencyDecay_integral
#print axioms positiveFrequencyDecay_tsum
#print axioms integerFrequencyDecay_tsum

end

end PrimeGap182.TypeIII
