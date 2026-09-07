import TypeIIIFrequencyScaling
import TypeIIIProductMasks

/-!
# Actual rectangular majorants for finite and curve exceptional sets

A curve is split into its finitely many bad vertical fibers and the remaining bounded
fibers.  The latter retain their dependence on the first frequency.  Finite exceptional
sets are covered by their two coordinate projections.  The five labels below enumerate
these actual sets and the ordinary term; inactive terms have coefficient zero.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

inductive MaskKind
  | base | finite | vertical | fiber | origin
  deriving DecidableEq

instance : Fintype MaskKind where
  elems := {.base, .finite, .vertical, .fiber, .origin}
  complete t := by cases t <;> simp

theorem sum_maskKind (a : MaskKind → ℝ) :
    (∑ t, a t) = a .base + a .finite + a .vertical + a .fiber + a .origin := by
  have hu : (Finset.univ : Finset MaskKind) = {.base, .finite, .vertical, .fiber, .origin} :=
    by decide
  rw [hu]
  simp [add_assoc]

/-- All finite-set and fiber bounds used by the local rectangular decomposition. -/
structure LocalMaskData (s : ℕ) [NeZero s] (D : ℕ) where
  repeated : Bool
  finiteSet : Finset (ZMod s × ZMod s)
  curveSet : Finset (ZMod s × ZMod s)
  badVertical : Finset (ZMod s)
  finite_card : finiteSet.card ≤ D
  vertical_card : badVertical.card ≤ D
  fiber_card : ∀ h ∉ badVertical,
    (Finset.univ.filter (fun k : ZMod s => (h, k) ∈ curveSet)).card ≤ D

abbrev maskFirstMod (s : ℕ) : MaskKind → ℕ
  | .base | .fiber => 1
  | .finite | .vertical | .origin => s

abbrev maskSecondMod (s : ℕ) : MaskKind → ℕ
  | .base | .vertical => 1
  | .finite | .fiber | .origin => s

instance (s : ℕ) [NeZero s] (t : MaskKind) : NeZero (maskFirstMod s t) := by
  cases t <;> simp only [maskFirstMod] <;> infer_instance

instance (s : ℕ) [NeZero s] (t : MaskKind) : NeZero (maskSecondMod s t) := by
  cases t <;> simp only [maskSecondMod] <;> infer_instance

theorem maskFirstMod_dvd (s : ℕ) (t : MaskKind) : maskFirstMod s t ∣ s := by
  cases t <;> simp only [maskFirstMod, one_dvd, dvd_refl]

theorem maskSecondMod_dvd (s : ℕ) (t : MaskKind) : maskSecondMod s t ∣ s := by
  cases t <;> simp only [maskSecondMod, one_dvd, dvd_refl]

def maskWeight (s : ℕ) (repeated : Bool) : MaskKind → ℝ
  | .base => 1
  | .finite => if repeated then 0 else Real.sqrt s
  | .vertical | .fiber => if repeated then Real.sqrt s else 0
  | .origin => if repeated then s else 0

def maskFirstResidues {s D : ℕ} [NeZero s] (E : LocalMaskData s D) :
    (t : MaskKind) → Finset (ZMod (maskFirstMod s t))
  | .base | .fiber => Finset.univ
  | .finite => E.finiteSet.image Prod.fst
  | .vertical => E.badVertical
  | .origin => {0}

def maskSecondResidues {s D : ℕ} [NeZero s] (E : LocalMaskData s D) :
    (t : MaskKind) → ZMod s → Finset (ZMod (maskSecondMod s t))
  | .base, _ | .vertical, _ => Finset.univ
  | .finite, _ => E.finiteSet.image Prod.snd
  | .fiber, h => if h ∈ E.badVertical then ∅ else
      Finset.univ.filter (fun k : ZMod s => (h, k) ∈ E.curveSet)
  | .origin, _ => {0}

theorem maskFirstResidues_card {s D : ℕ} [NeZero s] (E : LocalMaskData s D)
    (t : MaskKind) : (maskFirstResidues E t).card ≤ max D 1 := by
  cases t with
  | base => simp only [maskFirstResidues, Finset.card_univ, ZMod.card]; exact le_max_right _ _
  | finite => exact (Finset.card_image_le).trans (E.finite_card.trans (le_max_left _ _))
  | vertical => exact E.vertical_card.trans (le_max_left _ _)
  | fiber => simp only [maskFirstResidues, Finset.card_univ, ZMod.card]; exact le_max_right _ _
  | origin => simp only [maskFirstResidues, Finset.card_singleton]; exact le_max_right _ _

theorem maskSecondResidues_card {s D : ℕ} [NeZero s] (E : LocalMaskData s D)
    (t : MaskKind) (h : ZMod s) : (maskSecondResidues E t h).card ≤ max D 1 := by
  cases t with
  | base => simp only [maskSecondResidues, Finset.card_univ, ZMod.card]; exact le_max_right _ _
  | finite => exact (Finset.card_image_le).trans (E.finite_card.trans (le_max_left _ _))
  | vertical => simp only [maskSecondResidues, Finset.card_univ, ZMod.card]; exact le_max_right _ _
  | fiber =>
    by_cases hh : h ∈ E.badVertical
    · simp only [maskSecondResidues, ite_eq_left hh, Finset.card_empty, Nat.zero_le]
    · simp only [maskSecondResidues, ite_eq_right hh]
      exact (E.fiber_card h hh).trans (le_max_left D 1)
  | origin => simp only [maskSecondResidues, Finset.card_singleton]; exact le_max_right _ _

theorem maskWeight_nonneg (s : ℕ) (repeated : Bool) (t : MaskKind) :
    0 ≤ maskWeight s repeated t := by
  cases repeated <;> cases t <;> simp [maskWeight, Real.sqrt_nonneg]

/-- All four scalar estimates needed after expanding the completed rectangle. -/
theorem maskWeight_bounds (s : ℕ) [NeZero s] (repeated : Bool) (t : MaskKind) :
    (maskWeight s repeated t) ^ 2 ≤ (s : ℝ) * (if repeated then s else 1) ∧
    (maskWeight s repeated t) ^ 2 ≤ (maskFirstMod s t : ℝ) ^ 2 *
      (if repeated then s else 1) ∧
    (maskWeight s repeated t) ^ 2 ≤ (maskSecondMod s t : ℝ) ^ 2 *
      (if repeated then s else 1) ∧
    maskWeight s repeated t ≤ (maskFirstMod s t : ℝ) * maskSecondMod s t := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s from NeZero.one_le)
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hr0 : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt hs0
  have hs2 : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
  have hs3 : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 * s :=
    le_mul_of_one_le_right (sq_nonneg _) hs
  have hfalse : ¬(false = true) := by decide
  cases repeated <;> cases t <;>
    simp only [maskWeight, maskFirstMod, maskSecondMod,
      ite_true, ite_eq_right hfalse, Nat.cast_one] <;>
    (refine ⟨?_, ?_, ?_, ?_⟩) <;> nlinarith

/-- The local Fourier majorant written before decomposing the exceptional set. -/
def localExceptionalEnvelope {s D : ℕ} [NeZero s] (E : LocalMaskData s D)
    (h k : ZMod s) : ℝ :=
  1 + Real.sqrt s *
      (if E.repeated then (if (h, k) ∈ E.curveSet then 1 else 0)
       else (if (h, k) ∈ E.finiteSet then 1 else 0)) +
    (if E.repeated then (s : ℝ) * (if h = 0 ∧ k = 0 then 1 else 0) else 0)

/-- Each local exceptional envelope is bounded by the sum of its actual rectangle masks. -/
theorem localExceptionalEnvelope_le_rectangles {s D : ℕ} [NeZero s]
    (E : LocalMaskData s D) (h k : ZMod s) :
    localExceptionalEnvelope E h k ≤
      ∑ t : MaskKind, maskWeight s E.repeated t *
        if (h.val : ZMod (maskFirstMod s t)) ∈ maskFirstResidues E t ∧
            (k.val : ZMod (maskSecondMod s t)) ∈ maskSecondResidues E t h then 1 else 0 := by
  rw [sum_maskKind]
  by_cases hrep : E.repeated = true
  · have hp : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
    have hroot : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
    by_cases hv : h ∈ E.badVertical <;>
      by_cases he : (h, k) ∈ E.curveSet <;>
      simp only [localExceptionalEnvelope, maskWeight, maskFirstMod, maskSecondMod,
        maskFirstResidues, maskSecondResidues, hrep, ite_true,
        Finset.mem_univ, ZMod.natCast_zmod_val, Finset.mem_singleton,
        Finset.notMem_empty, Finset.mem_filter, hv, he, ite_false, ite_true,
        mul_zero, zero_mul, mul_one, add_zero, and_true, and_false] <;>
      linarith
  · have hrep' : E.repeated = false := Bool.eq_false_iff.mpr hrep
    have hroot : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
    by_cases hz : (h, k) ∈ E.finiteSet
    · have hh : h ∈ E.finiteSet.image Prod.fst := Finset.mem_image.mpr ⟨(h, k), hz, rfl⟩
      have hk : k ∈ E.finiteSet.image Prod.snd := Finset.mem_image.mpr ⟨(h, k), hz, rfl⟩
      simp only [localExceptionalEnvelope, maskWeight, maskFirstMod, maskSecondMod,
        maskFirstResidues, maskSecondResidues, hrep', Bool.false_eq_true, ite_false,
        Finset.mem_univ, true_and, ZMod.natCast_zmod_val, hh, hk, hz, ite_true,
        and_self, mul_one, zero_mul, add_zero, le_refl]
    · simp only [localExceptionalEnvelope, maskWeight, maskFirstMod, maskSecondMod,
        maskFirstResidues, maskSecondResidues, hrep', Bool.false_eq_true, ite_false,
        Finset.mem_univ, true_and, ZMod.natCast_zmod_val, hz, mul_zero, zero_mul,
        add_zero]
      split_ifs <;> linarith

#print axioms maskFirstResidues_card
#print axioms maskSecondResidues_card
#print axioms maskWeight_bounds
#print axioms localExceptionalEnvelope_le_rectangles

end

end PrimeGap182.TypeIII
