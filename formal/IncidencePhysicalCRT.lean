import IncidencePhysicalCompatibility

/-!
# The literal three-factor source phase

For m=q₀gq this theorem proves, on the original unit rows, the exact
coefficient phase at q₀, the surviving input pole mask at g, and the
incidence kernel at q. The shift is an actual modular lift. No integer
division of B+ζ by q₀ is assumed.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceReducedSourceCoefficient {q : ℕ} (q₀ g : ℕ) (A : ℤ)
    (c t : (ZMod q)ˣ) : ZMod q :=
  ((g : ZMod q)⁻¹ * (q₀ : ZMod q)⁻¹ * (q₀ : ZMod q)⁻¹ * (A : ZMod q)) *
    (((c * t)⁻¹ : (ZMod q)ˣ) : ZMod q)

theorem incidenceReducedSourceCoefficient_isUnit {q : ℕ}
    (q₀ g : ℕ) (A : ℤ) (c t : (ZMod q)ˣ)
    (hq₀ : Nat.Coprime q₀ q) (hg : Nat.Coprime g q) (hA : IsUnit (A : ZMod q)) :
    IsUnit (incidenceReducedSourceCoefficient q₀ g A c t) := by
  have h0 : IsUnit ((q₀ : ZMod q)⁻¹) := by
    simpa only [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime] using
      ((ZMod.unitOfCoprime q₀ hq₀)⁻¹).isUnit
  have h1 : IsUnit ((g : ZMod q)⁻¹) := by
    simpa only [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime] using
      ((ZMod.unitOfCoprime g hg)⁻¹).isUnit
  exact (((h1.mul h0).mul h0).mul hA).mul ((c * t)⁻¹).isUnit

set_option maxHeartbeats 1000000 in
theorem incidencePhysicalSource_crt
    {q₀ g q : ℕ} [NeZero q₀] [NeZero g] [NeZero q]
    (h0 : Nat.Coprime q₀ (g * q)) (hg : Nat.Coprime g q)
    (A c t r E γ k B ζ Bhat : ℤ) (e₀ : ZMod q₀)
    (he₀ : ((t * E : ℤ) : ZMod q₀) = e₀)
    (hBhat : (Bhat : ZMod (g * q)) =
      (q₀ : ZMod (g * q))⁻¹ * ((B : ZMod (g * q)) + (ζ : ZMod (g * q))))
    (hrg : (r : ZMod g) = 0)
    (hrowg : IsUnit ((c : ZMod g) * ((t : ZMod g) * (E : ZMod g)) ^ 2))
    (sc st sr : (ZMod q)ˣ)
    (hsc : (sc : ZMod q) = (c : ZMod q))
    (hst : (st : ZMod q) = (t : ZMod q))
    (hsr : (sr : ZMod q) = (r : ZMod q)) :
    PrimeGap186.reciprocalUnitPhase (q₀ * (g * q))
      (((A * t * r : ℤ) : ZMod (q₀ * (g * q))))
      (((c * (t * E) * (ζ * (t * E) + (q₀ : ℤ) * (γ * (t * r) + (t * E) * k) +
        B * (t * E)) : ℤ) : ZMod (q₀ * (g * q)))) =
      PrimeGap186.reciprocalUnitPhase q₀
        (((g * q : ℕ) : ZMod q₀)⁻¹ * (A : ZMod q₀) * (t : ZMod q₀) * (r : ZMod q₀))
        ((c : ZMod q₀) * e₀ ^ 2 * ((ζ : ZMod q₀) + (B : ZMod q₀))) *
      (if IsUnit ((k : ZMod g) + (Bhat : ZMod g)) then (1 : ℂ) else 0) *
      incidenceMatrixMod (incidenceReducedSourceCoefficient q₀ g A sc st)
        ((E : ZMod q), (γ : ZMod q))
        (((k : ZMod q) + (Bhat : ZMod q)) * ((sr⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  let u0 : (ZMod (g * q))ˣ := ZMod.unitOfCoprime q₀ h0
  let Abar : ZMod (g * q) :=
    (q₀ : ZMod (g * q))⁻¹ * (q₀ : ZMod (g * q))⁻¹ * (A : ZMod (g * q))
  let P0 : ℂ := PrimeGap186.reciprocalUnitPhase q₀
    (((g * q : ℕ) : ZMod q₀)⁻¹ * (A : ZMod q₀) * (t : ZMod q₀) * (r : ZMod q₀))
    ((c : ZMod q₀) * e₀ ^ 2 * ((ζ : ZMod q₀) + (B : ZMod q₀)))
  have hfirst : PrimeGap186.reciprocalUnitPhase (q₀ * (g * q))
      (((A * t * r : ℤ) : ZMod (q₀ * (g * q))))
      (((c * (t * E) * (ζ * (t * E) + (q₀ : ℤ) * (γ * (t * r) + (t * E) * k) +
        B * (t * E)) : ℤ) : ZMod (q₀ * (g * q)))) =
      P0 * PrimeGap186.reciprocalUnitPhase (g * q)
        ((q₀ : ZMod (g * q))⁻¹ * (A : ZMod (g * q)) * (t : ZMod (g * q)) * (r : ZMod (g * q)))
        ((c : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
          ((ζ : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q))) +
            (q₀ : ZMod (g * q)) * ((γ : ZMod (g * q)) * ((t : ZMod (g * q)) * (r : ZMod (g * q))) +
              ((t : ZMod (g * q)) * (E : ZMod (g * q))) * (k : ZMod (g * q))) +
            (B : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q))))) := by
    rw [incidenceReciprocalPhase_crt h0]
    simp only [incidenceCRTScaledLeft, incidenceCRTScaledRight, map_intCast, map_mul, map_add, map_natCast,
      Int.cast_mul, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
    congr 1
    · dsimp only [P0]
      congr 1
      · ring
      · have he : (t : ZMod q₀) * (E : ZMod q₀) = e₀ := by
          simpa only [Int.cast_mul] using he₀
        rw [he]
        ring
    · congr 1
      ring
  rw [hfirst]
  have hshift := incidenceSource_modular_shift u0
    ((q₀ : ZMod (g * q))⁻¹ * (A : ZMod (g * q)) * (t : ZMod (g * q)) * (r : ZMod (g * q)))
    (c : ZMod (g * q)) ((t : ZMod (g * q)) * (E : ZMod (g * q)))
    ((γ : ZMod (g * q)) * ((t : ZMod (g * q)) * (r : ZMod (g * q))) +
      ((t : ZMod (g * q)) * (E : ZMod (g * q))) * (k : ZMod (g * q)))
    (B : ZMod (g * q)) (ζ : ZMod (g * q))
  simp only [u0, ZMod.coe_unitOfCoprime, ← ZMod.inv_coe_unit, ← hBhat] at hshift
  rw [hshift]
  have hnum : ((q₀ : ZMod (g * q))⁻¹ * (A : ZMod (g * q)) * (t : ZMod (g * q)) *
      (r : ZMod (g * q))) * (q₀ : ZMod (g * q))⁻¹ =
      Abar * (t : ZMod (g * q)) * (r : ZMod (g * q)) := by dsimp only [Abar]; ring
  have hden : (c : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
      (((γ : ZMod (g * q)) * ((t : ZMod (g * q)) * (r : ZMod (g * q))) +
        ((t : ZMod (g * q)) * (E : ZMod (g * q))) * (k : ZMod (g * q))) +
        (Bhat : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q)))) =
      (c : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
        ((γ : ZMod (g * q)) * ((t : ZMod (g * q)) * (r : ZMod (g * q))) +
          ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
            ((k : ZMod (g * q)) + (Bhat : ZMod (g * q)))) := by ring
  rw [hnum, hden, incidenceReciprocalPhase_crt hg]
  have h0unit : IsUnit (q₀ : ZMod (g * q)) := (ZMod.isUnit_iff_coprime _ _).mpr h0
  have hAbar : incidenceCRTRight hg Abar =
      (q₀ : ZMod q)⁻¹ * (q₀ : ZMod q)⁻¹ * (A : ZMod q) := by
    simp only [Abar, map_mul, PrimeGap186.phaseCRT_map_inv _ h0unit, map_natCast, map_intCast]
  have hleft : PrimeGap186.reciprocalUnitPhase g
      (incidenceCRTScaledLeft hg (Abar * (t : ZMod (g * q)) * (r : ZMod (g * q))))
      (incidenceCRTLeft hg
        ((c : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
          ((γ : ZMod (g * q)) * ((t : ZMod (g * q)) * (r : ZMod (g * q))) +
            ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
              ((k : ZMod (g * q)) + (Bhat : ZMod (g * q)))))) =
      if IsUnit ((k : ZMod g) + (Bhat : ZMod g)) then (1 : ℂ) else 0 := by
    simp only [incidenceCRTScaledLeft, map_mul, map_add, map_intCast, hrg, mul_zero,
      zero_add, incidenceReciprocalPhase_zero_numerator]
    have heq : (c : ZMod g) * ((t : ZMod g) * (E : ZMod g)) *
        (((t : ZMod g) * (E : ZMod g)) * ((k : ZMod g) + (Bhat : ZMod g))) =
        ((c : ZMod g) * ((t : ZMod g) * (E : ZMod g)) ^ 2) *
          ((k : ZMod g) + (Bhat : ZMod g)) := by ring
    rw [heq]
    simp only [IsUnit.mul_iff, hrowg, true_and]
  rw [hleft]
  have hright := incidenceSource_phase sc st sr
    ((g : ZMod q)⁻¹ * (q₀ : ZMod q)⁻¹ * (q₀ : ZMod q)⁻¹ * (A : ZMod q))
    (E : ZMod q) (γ : ZMod q) (k : ZMod q) (Bhat : ZMod q)
  simp only [Units.val_mul, hsc, hst, hsr] at hright
  have hright' : PrimeGap186.reciprocalUnitPhase q
      (incidenceCRTScaledRight hg (Abar * (t : ZMod (g * q)) * (r : ZMod (g * q))))
      (incidenceCRTRight hg
        ((c : ZMod (g * q)) * ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
          ((γ : ZMod (g * q)) * ((t : ZMod (g * q)) * (r : ZMod (g * q))) +
            ((t : ZMod (g * q)) * (E : ZMod (g * q))) *
              ((k : ZMod (g * q)) + (Bhat : ZMod (g * q)))))) =
      incidenceMatrixMod (incidenceReducedSourceCoefficient q₀ g A sc st)
        ((E : ZMod q), (γ : ZMod q))
        (((k : ZMod q) + (Bhat : ZMod q)) * ((sr⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
    simp only [incidenceCRTScaledRight, map_mul, map_add, map_intCast, hAbar]
    simpa only [incidenceReducedSourceCoefficient, mul_assoc] using hright
  rw [hright', mul_assoc]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceReducedSourceCoefficient_isUnit
#print axioms PrimeGap182Audit.incidencePhysicalSource_crt
