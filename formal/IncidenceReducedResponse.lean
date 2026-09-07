import IncidenceProgressionResponse
import IncidenceAngularSource

/-!
# The original progression sum is an actual incidence response

This module retains the q₀ coefficient phase and the g input pole mask.
The integer numerator sum, the source profile, and the original γ range
are unchanged. The finite-field identity is applied term by term.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceSourceCoefficientPhase (q₀ g q : ℕ) [NeZero q₀] (A B ζ t r : ℤ)
    (e₀ : ZMod q₀) : ℂ :=
  PrimeGap186.reciprocalUnitPhase q₀
    (((g * q : ℕ) : ZMod q₀)⁻¹ * (A : ZMod q₀) * (t : ZMod q₀) * (r : ZMod q₀))
    (e₀ ^ 2 * ((ζ : ZMod q₀) + (B : ZMod q₀)))

def incidenceReducedInputMask (g : ℕ) [NeZero g] (Bhat k : ℤ) : ℂ :=
  if IsUnit ((k : ZMod g) + (Bhat : ZMod g)) then 1 else 0

theorem incidenceSourceCoefficientPhase_norm (q₀ g q : ℕ) [NeZero q₀]
    (A B ζ t r : ℤ) (e₀ : ZMod q₀) :
    ‖incidenceSourceCoefficientPhase q₀ g q A B ζ t r e₀‖ ≤ 1 :=
  incidenceReciprocalPhase_norm_le_one _ _

theorem incidenceReducedInputMask_norm (g : ℕ) [NeZero g] (Bhat k : ℤ) :
    ‖incidenceReducedInputMask g Bhat k‖ ≤ 1 := by
  unfold incidenceReducedInputMask
  split_ifs <;> norm_num

set_option maxHeartbeats 1600000 in
theorem incidenceProgressionResponse_crt
    {q₀ g q : ℕ} [NeZero q₀] [NeZero g] [NeZero q]
    (h0 : Nat.Coprime q₀ (g * q)) (hg : Nat.Coprime g q)
    (A B ζ γ t r E : ℤ) (e : ℕ) (he : (e : ℤ) = t * E)
    (e₀ : ZMod q₀) (he₀ : (e : ZMod q₀) = e₀)
    (Bhat : ℤ)
    (hBhat : (Bhat : ZMod (g * q)) =
      (q₀ : ZMod (g * q))⁻¹ * ((B : ZMod (g * q)) + (ζ : ZMod (g * q))))
    (hrg : (r : ZMod g) = 0) (heg : IsUnit (e : ZMod g))
    (st sr : (ZMod q)ˣ) (hst : (st : ZMod q) = (t : ZMod q))
    (hsr : (sr : ZMod q) = (r : ZMod q))
    (ψ : ℝ → ℝ) (N c : ℝ) :
    incidenceProgressionResponse (m := q₀ * (g * q)) (A : ZMod _) B q₀ e ζ γ
        (fun n => (ψ (c * (n : ℝ) / N) : ℂ)) (t * r) =
      incidenceSourceCoefficientPhase q₀ g q A B ζ t r e₀ *
        ∑' k : ℤ, incidenceReducedInputMask g Bhat k *
          incidenceMatrixMod (incidenceReducedSourceCoefficient q₀ g A 1 st)
            ((E : ZMod q), (γ : ZMod q))
            (((k : ZMod q) + (Bhat : ZMod q)) * ((sr⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          (ψ (c * ((ζ : ℝ) * (e : ℝ) + (q₀ : ℝ) *
            ((γ : ℝ) * ((t * r : ℤ) : ℝ) + (e : ℝ) * (k : ℝ))) / N) : ℂ) := by
  have hecast (s : ℕ) : (e : ZMod s) = (t : ZMod s) * (E : ZMod s) := by
    simpa only [Int.cast_natCast, Int.cast_mul] using
      congrArg (fun a : ℤ => (a : ZMod s)) he
  have he0' : ((t * E : ℤ) : ZMod q₀) = e₀ := by
    simpa only [Int.cast_mul, ← hecast] using he₀
  have hrowg : IsUnit ((1 : ZMod g) * ((t : ZMod g) * (E : ZMod g)) ^ 2) := by
    simpa only [one_mul, ← hecast] using heg.pow 2
  unfold incidenceProgressionResponse
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hp := incidencePhysicalSource_crt h0 hg A 1 t r E γ k B ζ Bhat e₀ he0' hBhat
    hrg (by simpa only [Int.cast_one] using hrowg) (1 : (ZMod q)ˣ) st sr
    (by simp only [Units.val_one, Int.cast_one]) hst hsr
  have hphase : PrimeGap186.reciprocalUnitPhase (q₀ * (g * q))
      ((A : ZMod _) * ((t * r : ℤ) : ZMod _))
      ((e : ZMod _) *
        (((ζ * (e : ℤ) + (q₀ : ℤ) * (γ * (t * r) + (e : ℤ) * k) : ℤ) : ZMod _) +
          (B : ZMod _) * (e : ZMod _))) =
      incidenceSourceCoefficientPhase q₀ g q A B ζ t r e₀ *
        incidenceReducedInputMask g Bhat k *
        incidenceMatrixMod (incidenceReducedSourceCoefficient q₀ g A 1 st)
          ((E : ZMod q), (γ : ZMod q))
          (((k : ZMod q) + (Bhat : ZMod q)) * ((sr⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
    simpa only [incidenceSourceCoefficientPhase, incidenceReducedInputMask,
      Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, one_mul,
      hecast, mul_assoc] using hp
  rw [hphase]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

theorem incidenceFareyResidue_product_unit {q : ℕ} (uw ua : (ZMod q)ˣ)
    (a B k : ℤ) (hua : (ua : ZMod q) = (a : ZMod q)) :
    (((k : ZMod q) + (B : ZMod q)) *
        (((uw * ua)⁻¹ : (ZMod q)ˣ) : ZMod q)) =
      ((uw⁻¹ : (ZMod q)ˣ) : ZMod q) * incidenceFareyResidue q B a k := by
  simp only [mul_inv_rev, Units.val_mul, incidenceFareyResidue, Int.cast_add,
    ← ZMod.inv_coe_unit, hua]
  ring

set_option maxHeartbeats 1600000 in
theorem incidenceSourceSector_eq_response
    {q₀ g q : ℕ} [NeZero q₀] [NeZero g] [NeZero q]
    (h0 : Nat.Coprime q₀ (g * q)) (hg : Nat.Coprime g q)
    (A B ζ r₀ Bhat : ℤ) (t w₂ e : ℕ)
    (ht : Nat.Coprime t q) (hw : Nat.Coprime w₂ q) (hgw : g ∣ w₂)
    (heg : Nat.Coprime e g) (e₀ : ZMod q₀) (he₀ : (e : ZMod q₀) = e₀)
    (hBhat : (Bhat : ZMod (g * q)) =
      (q₀ : ZMod (g * q))⁻¹ * ((B : ZMod (g * q)) + (ζ : ZMod (g * q))))
    (z : ℤ × ℤ) (he : (e : ℤ) = (t : ℤ) * ((q₀ : ℤ) * z.1 + r₀))
    (S : Finset ℤ) (hS : ∀ a ∈ S, IsUnit (a : ZMod q))
    (coeff : ℤ → ℂ) (ψ : ℝ → ℝ) (N c : ℝ) :
    (∑ a ∈ S, coeff (((t * w₂ : ℕ) : ℤ) * a) *
      incidenceProgressionResponse (m := q₀ * (g * q)) (A : ZMod _) B q₀ e ζ z.2
        (fun n => (ψ (c * (n : ℝ) / N) : ℂ)) (((t * w₂ : ℕ) : ℤ) * a)) =
      incidenceUnrestrictedSourceResponse
        (incidenceReducedSourceCoefficient q₀ g A 1 (ZMod.unitOfCoprime t ht))
        ((ZMod.unitOfCoprime w₂ hw)⁻¹) q₀ r₀ S Bhat
        (fun a => coeff (((t * w₂ : ℕ) : ℤ) * a) *
          incidenceSourceCoefficientPhase q₀ g q A B ζ (t : ℤ) ((w₂ : ℤ) * a) e₀)
        (fun _ k => incidenceReducedInputMask g Bhat k) ψ N c (q₀ : ℝ) (ζ : ℝ)
        (fun z => (t : ℝ) * ((q₀ : ℝ) * (z.1 : ℝ) + (r₀ : ℝ)))
        (fun a => (((t * w₂ : ℕ) : ℤ) * a : ℤ)) z := by
  unfold incidenceUnrestrictedSourceResponse
  apply Finset.sum_congr rfl
  intro a ha
  let st : (ZMod q)ˣ := ZMod.unitOfCoprime t ht
  let uw : (ZMod q)ˣ := ZMod.unitOfCoprime w₂ hw
  let ua : (ZMod q)ˣ := (hS a ha).unit
  have hua : (ua : ZMod q) = (a : ZMod q) := (hS a ha).unit_spec
  have hsr : ((uw * ua : (ZMod q)ˣ) : ZMod q) = (((w₂ : ℤ) * a : ℤ) : ZMod q) := by
    simp only [Units.val_mul, uw, ZMod.coe_unitOfCoprime, hua, Int.cast_mul, Int.cast_natCast]
  have hrg : (((w₂ : ℤ) * a : ℤ) : ZMod g) = 0 := by
    simp only [Int.cast_mul, Int.cast_natCast, (ZMod.natCast_eq_zero_iff w₂ g).mpr hgw, zero_mul]
  have hphase := incidenceProgressionResponse_crt h0 hg A B ζ z.2 (t : ℤ)
    ((w₂ : ℤ) * a) ((q₀ : ℤ) * z.1 + r₀) e he e₀ he₀ Bhat hBhat hrg
    ((ZMod.isUnit_iff_coprime e g).mpr heg) st (uw * ua)
    (by simp only [st, ZMod.coe_unitOfCoprime, Int.cast_natCast]) hsr ψ N c
  have heR : (e : ℝ) = (t : ℝ) * ((q₀ : ℝ) * (z.1 : ℝ) + (r₀ : ℝ)) := by
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_natCast] using
      congrArg (fun v : ℤ => (v : ℝ)) he
  have hl : ((t * w₂ : ℕ) : ℤ) * a = (t : ℤ) * ((w₂ : ℤ) * a) := by
    push_cast
    ring
  simp only [hl]
  rw [hphase, ← mul_assoc]
  congr 1
  apply tsum_congr
  intro k
  rw [incidenceFareyResidue_product_unit uw ua a Bhat k hua]
  simp only [st, uw, Int.cast_add, Int.cast_mul, Int.cast_natCast, heR]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourceCoefficientPhase_norm
#print axioms PrimeGap182Audit.incidenceReducedInputMask_norm
#print axioms PrimeGap182Audit.incidenceProgressionResponse_crt
#print axioms PrimeGap182Audit.incidenceFareyResidue_product_unit
#print axioms PrimeGap182Audit.incidenceSourceSector_eq_response
