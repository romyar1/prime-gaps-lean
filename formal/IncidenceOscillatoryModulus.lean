import IncidencePhysicalCRT

/-!
# The actual oscillatory modulus selected by the source gcd

The split q=m/(q₀ gcd(w₂,m/q₀)) is derived from squarefreeness. In
particular w₂ is a unit modulo q even when it contains prime powers.
-/

noncomputable section

namespace PrimeGap182Audit

def incidenceOscillatoryModulus (m q₀ w₂ : ℕ) : ℕ :=
  (m / q₀) / (Nat.gcd w₂ (m / q₀))

theorem incidenceOscillatoryModulus_spec (m q₀ w₂ : ℕ)
    (hm : Squarefree m) (hq₀ : q₀ ∣ m) :
    let g := Nat.gcd w₂ (m / q₀)
    let q := incidenceOscillatoryModulus m q₀ w₂
    0 < q₀ ∧ 0 < g ∧ 0 < q ∧ m = q₀ * (g * q) ∧
      Nat.Coprime q₀ (g * q) ∧ Nat.Coprime g q ∧ Squarefree q ∧
      Nat.Coprime w₂ q ∧ g ∣ w₂ := by
  intro g q
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have h0pos : 0 < q₀ := Nat.pos_of_dvd_of_pos hq₀ hmpos
  have hm1pos : 0 < m / q₀ := Nat.div_pos (Nat.le_of_dvd hmpos hq₀) h0pos
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right w₂ hm1pos
  have hgdiv : g ∣ m / q₀ := Nat.gcd_dvd_right _ _
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hm1pos hgdiv) hgpos
  have hgq : g * q = m / q₀ := Nat.mul_div_cancel' hgdiv
  have hsplit : m = q₀ * (g * q) := by rw [hgq, Nat.mul_div_cancel' hq₀]
  have hsf : Squarefree (q₀ * (g * q)) := hsplit ▸ hm
  have hcop0 : Nat.Coprime q₀ (g * q) := Nat.coprime_of_squarefree_mul hsf
  have hcopg : Nat.Coprime g q := Nat.coprime_of_squarefree_mul hsf.of_mul_right
  have hqdiv : q ∣ m / q₀ := by rw [← hgq]; exact dvd_mul_left _ _
  have hwq : Nat.Coprime w₂ q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hgcd : Nat.gcd w₂ q = Nat.gcd g q := by
      change Nat.gcd w₂ q = Nat.gcd (Nat.gcd w₂ (m / q₀)) q
      rw [Nat.gcd_assoc, Nat.gcd_eq_right hqdiv]
    rw [hgcd]
    exact hcopg.gcd_eq_one
  exact ⟨h0pos, hgpos, hqpos, hsplit, hcop0, hcopg,
    hsf.of_mul_right.of_mul_right, hwq, Nat.gcd_dvd_left _ _⟩

theorem incidenceModularShift_exists (q₀ m : ℕ) [NeZero m] (B ζ : ℤ) :
    ∃ Bhat : ℤ, 0 ≤ Bhat ∧ Bhat < (m : ℤ) ∧
      (Bhat : ZMod m) = (q₀ : ZMod m)⁻¹ * ((B : ZMod m) + (ζ : ZMod m)) := by
  let z : ZMod m := (q₀ : ZMod m)⁻¹ * ((B : ZMod m) + (ζ : ZMod m))
  refine ⟨(z.val : ℤ), by positivity, ?_, ?_⟩
  · exact_mod_cast z.val_lt
  · simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val z

theorem incidenceReciprocalPhase_norm_le_one {m : ℕ} [NeZero m] (A x : ZMod m) :
    ‖PrimeGap186.reciprocalUnitPhase m A x‖ ≤ 1 := by
  classical
  by_cases hx : IsUnit x
  · exact (incidenceReciprocalPhase_norm_of_unit A x hx).le
  · simp only [PrimeGap186.reciprocalUnitPhase, ite_eq_right hx, norm_zero, zero_le_one]

theorem incidenceSupportedPart_coprime (m e n : ℕ) (hme : Nat.Coprime m e) :
    Nat.Coprime (∏ p ∈ m.primeFactors, p ^ n.factorization p) e := by
  apply Nat.Coprime.prod_left
  intro p hp
  exact (hme.of_dvd_left (Nat.dvd_of_mem_primeFactors hp)).pow_left _

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceOscillatoryModulus_spec
#print axioms PrimeGap182Audit.incidenceModularShift_exists
#print axioms PrimeGap182Audit.incidenceReciprocalPhase_norm_le_one
#print axioms PrimeGap182Audit.incidenceSupportedPart_coprime
