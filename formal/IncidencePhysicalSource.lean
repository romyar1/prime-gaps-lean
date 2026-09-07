import IncidenceFrequencyCoefficients
import IncidenceSourcePhase
import IncidenceSourceWindow

/-!
# The actual positive physical source form

This module identifies the baseline's quotient Gram form with the
coefficient-grouped physical residue energy. The masks for the original
numerator and for the frequency coprimality are retained. The residue
energy includes every class, including zero.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

theorem incidenceGroupedCoefficient_sum {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (ell : ι → ℤ) (a : ι → ℂ) (G : ℤ → ℂ) :
    (∑ l ∈ F.image ell, incidenceGroupedCoefficient F ell a l * G l) =
      ∑ h ∈ F, a h * G (ell h) := by
  classical
  unfold incidenceGroupedCoefficient
  simp only [Finset.sum_mul]
  have he : (∑ l ∈ F.image ell, ∑ h ∈ F with ell h = l, a h * G l) =
      ∑ l ∈ F.image ell, ∑ h ∈ F with ell h = l, a h * G (ell h) := by
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro h hh
    rw [(Finset.mem_filter.mp hh).2]
  rw [he]
  exact Finset.sum_fiberwise_of_maps_to (fun h hh => Finset.mem_image_of_mem ell hh) _

def incidencePhysicalRow {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (Λ I : Finset ℤ) (c χ : ℤ → ℂ) (γ : ZMod e) : ℂ :=
  ∑ l ∈ Λ, c l * if IsUnit (l : ZMod e) then
    ∑ n ∈ I, if IsUnit (n : ZMod w) ∧ (n : ZMod e) = γ * (l : ZMod e) then
      χ n * PrimeGap186.reciprocalUnitPhase m ((A : ZMod m) * (l : ZMod m))
        ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m)))
      else 0
    else 0

def incidencePhysicalEnergy {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (Λ I : Finset ℤ) (c χ : ℤ → ℂ) : ℝ :=
  ∑ γ : ZMod e, ‖incidencePhysicalRow (m := m) (w := w) A B Λ I c χ γ‖ ^ 2

def incidencePhysicalRawRow {ι : Type*} {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (F : Finset ι) (I : Finset ℤ) (ell : ι → ℤ)
    (a : ι → ℂ) (χ : ℤ → ℂ) (γ : ZMod e) : ℂ :=
  ∑ h ∈ F, ∑ n ∈ I,
    if IsUnit (ell h : ZMod e) ∧ IsUnit (n : ZMod w) ∧
        (n : ZMod e) * (((w : ℤ) * ell h : ℤ) : ZMod e)⁻¹ = γ then
      (χ n * a h) * PrimeGap186.reciprocalUnitPhase m
        ((A : ZMod m) * (((w : ℤ) * ell h : ℤ) : ZMod m))
        (((w * e : ℕ) : ZMod m) *
          ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m)))
      else 0

theorem incidencePhysicalRawRow_eq {ι : Type*} [DecidableEq ι]
    {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (hwe : Nat.Coprime w e) (hwm : Nat.Coprime w m)
    (A B : ℤ) (F : Finset ι) (I : Finset ℤ) (ell : ι → ℤ)
    (a : ι → ℂ) (χ : ℤ → ℂ) (γ : ZMod e) :
    incidencePhysicalRawRow (m := m) (w := w) A B F I ell a χ γ =
      incidencePhysicalRow (m := m) (w := w) A B (F.image ell) I
        (incidenceGroupedCoefficient F ell a) χ ((w : ZMod e) * γ) := by
  classical
  have hwE : IsUnit (w : ZMod e) := (ZMod.isUnit_iff_coprime w e).mpr hwe
  let uw : (ZMod m)ˣ := ZMod.unitOfCoprime w hwm
  have hphase (l n : ℤ) : PrimeGap186.reciprocalUnitPhase m
      ((A : ZMod m) * (((w : ℤ) * l : ℤ) : ZMod m))
      (((w * e : ℕ) : ZMod m) *
        ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m))) =
      PrimeGap186.reciprocalUnitPhase m ((A : ZMod m) * (l : ZMod m))
        ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m))) := by
    have h := incidenceReciprocalPhase_cancel_unit uw ((A : ZMod m) * (l : ZMod m))
      ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m)))
    simpa only [uw, ZMod.coe_unitOfCoprime, Int.cast_mul, Int.cast_natCast,
      Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
  unfold incidencePhysicalRow
  rw [incidenceGroupedCoefficient_sum]
  unfold incidencePhysicalRawRow
  apply Finset.sum_congr rfl
  intro h _
  by_cases hu : IsUnit (ell h : ZMod e)
  · have hratio (n : ℤ) :
        (n : ZMod e) * (((w : ℤ) * ell h : ℤ) : ZMod e)⁻¹ = γ ↔
          (n : ZMod e) = ((w : ZMod e) * γ) * (ell h : ZMod e) := by
      have hv : IsUnit (((w : ℤ) * ell h : ℤ) : ZMod e) := by
        simpa only [Int.cast_mul, Int.cast_natCast] using hwE.mul hu
      have hi := incidenceUnitRatio_eq_iff
        (((w : ℤ) * ell h : ℤ) : ZMod e) 1 (n : ZMod e) γ hv isUnit_one
      simpa only [ZMod.inv_one, mul_one, one_mul, Int.cast_mul, Int.cast_natCast,
        mul_assoc, mul_comm, mul_left_comm] using hi
    simp only [hu, true_and, ite_eq_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [hratio n, hphase]
    split_ifs <;> ring
  · simp [hu]

def incidencePhysicalGram {ι : Type*} {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (F : Finset ι) (I : Finset ℤ) (ell : ι → ℤ)
    (a : ι → ℂ) (χ : ℤ → ℂ) : ℂ :=
  let S := (F.filter (fun h => IsUnit (ell h : ZMod e))).product I
  let V := S.filter (fun p => IsUnit (p.2 : ZMod w))
  let y := fun h => (w : ℤ) * ell h
  ∑ p ∈ V, ∑ r ∈ V with
      Int.ModEq ((w * e : ℕ) : ℤ) (y p.1 * r.2) (y r.1 * p.2),
    (χ p.2 * a p.1) * star (χ r.2 * a r.1) *
      PrimeGap186.reciprocalUnitPhase m
        ((A : ZMod m) *
          (((y p.1 * (r.2 + B * ((w * e : ℕ) : ℤ)) -
              y r.1 * (p.2 + B * ((w * e : ℕ) : ℤ))) /
            ((w * e : ℕ) : ℤ) : ℤ) : ZMod m))
        (((p.2 : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m)) *
          ((r.2 : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m)))

set_option maxHeartbeats 800000 in
/-- Exact bridge from the baseline's original masked quotient Gram to
the grouped physical form; this is an identity, without an energy bound. -/
theorem incidencePhysicalGram_eq {ι : Type} [DecidableEq ι]
    {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (hwe : Nat.Coprime w e) (hdm : Nat.Coprime (w * e) m)
    (A B : ℤ) (F : Finset ι) (I : Finset ℤ) (ell : ι → ℤ)
    (a : ι → ℂ) (χ : ℤ → ℂ) :
    incidencePhysicalGram (m := m) (w := w) (e := e) A B F I ell a χ =
      (incidencePhysicalEnergy (m := m) (w := w) (e := e) A B (F.image ell) I
        (incidenceGroupedCoefficient F ell a) χ : ℂ) := by
  classical
  let S := (F.filter (fun h => IsUnit (ell h : ZMod e))).product I
  have hwE : IsUnit (w : ZMod e) := (ZMod.isUnit_iff_coprime w e).mpr hwe
  have hy : ∀ p ∈ S,
      Int.gcd ((w : ℤ) * ell p.1) ((w * e : ℕ) : ℤ) = w := by
    intro p hp
    have hu := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    apply (PrimeGap186.sourceSecondaryGcd_quotient_unit_iff w e hwe _).mpr
    exact ⟨dvd_mul_right _ _, by simpa only [Int.cast_mul, Int.cast_natCast] using hwE.mul hu⟩
  let Fq : ZMod e → ℂ := fun γ =>
    ∑ p ∈ (S.filter (fun p => IsUnit (p.2 : ZMod w))).filter
        (fun p => (p.2 : ZMod e) * (((w : ℤ) * ell p.1 : ℤ) : ZMod e)⁻¹ = γ),
      (χ p.2 * a p.1) * PrimeGap186.reciprocalUnitPhase m
        ((A : ZMod m) * (((w : ℤ) * ell p.1 : ℤ) : ZMod m))
        (((w * e : ℕ) : ZMod m) *
          ((p.2 : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m)))
  have hg : ((∑ γ : ZMod e, ‖Fq γ‖ ^ 2 : ℝ) : ℂ) =
      incidencePhysicalGram (m := m) (w := w) (e := e) A B F I ell a χ :=
    (PrimeGap186.sourceSecondary_quotient_gram_cauchy S
      (fun p => p.2) (fun p => (w : ℤ) * ell p.1) (fun p => χ p.2 * a p.1)
      w e m hwe hdm hy 0 A B).1
  have hrow (γ : ZMod e) : Fq γ =
      incidencePhysicalRawRow (m := m) (w := w) A B F I ell a χ γ := by
    dsimp only [Fq]
    simp only [Finset.sum_filter]
    change (∑ p ∈ (F.filter (fun h => IsUnit (ell h : ZMod e))).product I, _) = _
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp only [Finset.sum_filter, incidencePhysicalRawRow, Finset.sum_ite_irrel,
      Finset.sum_const_zero, ite_and]
  have hrows : (∑ γ : ZMod e, ‖Fq γ‖ ^ 2) =
      ∑ γ : ZMod e, ‖incidencePhysicalRow (m := m) (w := w) A B (F.image ell) I
        (incidenceGroupedCoefficient F ell a) χ ((w : ZMod e) * γ)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro γ _
    rw [hrow γ, incidencePhysicalRawRow_eq hwe (Nat.coprime_mul_iff_left.mp hdm).1]
  let ew : ZMod e ≃ ZMod e := incidenceInputUnitEquiv (ZMod.unitOfCoprime w hwe)
  have he := ew.sum_comp (fun γ =>
    ‖incidencePhysicalRow (m := m) (w := w) A B (F.image ell) I
      (incidenceGroupedCoefficient F ell a) χ γ‖ ^ 2)
  change (∑ γ, ‖incidencePhysicalRow (m := m) (w := w) A B (F.image ell) I
    (incidenceGroupedCoefficient F ell a) χ ((w : ZMod e) * γ)‖ ^ 2) =
      incidencePhysicalEnergy (m := m) (w := w) (e := e) A B (F.image ell) I
        (incidenceGroupedCoefficient F ell a) χ at he
  exact hg.symm.trans (congrArg (fun t : ℝ => (t : ℂ)) (hrows.trans he))

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceGroupedCoefficient_sum
#print axioms PrimeGap182Audit.incidencePhysicalRawRow_eq
#print axioms PrimeGap182Audit.incidencePhysicalGram_eq
