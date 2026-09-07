import IncidenceMobiusMasks

/-!
# The baseline's actual masked pair kernel as physical incidence energy

The numerator weight below is the original source weight, including
both coprimality masks and the compatibility set. The theorem is an
exact equality for the baseline `sourceSecondaryPairTerm`.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceSourceNumerator (r₁ q₀ u₁ v₁ v₂ q₂ d : ℕ)
    (ℓ : ℤ) (E : ZMod q₀ → Finset (ZMod q₀)) (ψN : ℝ → ℝ) (N : ℝ) (n : ℤ) : ℂ :=
  if Int.gcd n ((r₁ * q₀ * u₁ * v₁ * v₂ : ℕ) : ℤ) = 1 ∧
      Int.gcd (n + ℓ * (d : ℤ) * (r₁ : ℤ)) ((q₀ * q₂ : ℕ) : ℤ) = 1 then
    (if (n : ZMod q₀) ∈ E (d : ZMod q₀) then (1 : ℂ) else 0) *
      (ψN ((n : ℝ) / N) : ℂ)
  else 0

theorem incidenceQuotientFrequencyMask {m w e : ℕ} [NeZero w]
    (hem : Nat.Coprime e m) (l l' : ℤ) :
    Int.gcd (e : ℤ)
        (((m : ℤ) * ((w : ℤ) * l) * ((w : ℤ) * l')) / (w : ℤ) ^ 2) = 1 ↔
      IsUnit (l : ZMod e) ∧ IsUnit (l' : ZMod e) := by
  have hw : (w : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne w)
  have hquot : ((m : ℤ) * ((w : ℤ) * l) * ((w : ℤ) * l')) / (w : ℤ) ^ 2 =
      (m : ℤ) * l * l' := by
    rw [show (m : ℤ) * ((w : ℤ) * l) * ((w : ℤ) * l') =
      (w : ℤ) ^ 2 * ((m : ℤ) * l * l') by ring,
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hw)]
  rw [hquot, ← Int.isCoprime_iff_gcd_eq_one, ← ZMod.coe_int_isUnit_iff_isCoprime]
  simp only [Int.cast_mul, Int.cast_natCast, IsUnit.mul_iff,
    (ZMod.isUnit_iff_coprime m e).mpr hem.symm, true_and]

set_option maxHeartbeats 1000000 in
theorem incidenceSourceEnergyRow_eq
    {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (hwe : Nat.Coprime w e) (hdm : Nat.Coprime (w * e) m)
    (r₁ q₀ u₁ v₁ v₂ q₂ : ℕ) (A B ℓ : ℤ)
    (E : ZMod q₀ → Finset (ZMod q₀)) (ψN : ℝ → ℝ) (N : ℝ)
    (F : Finset (ℤ × ℤ)) (I : Finset ℤ) (ell : (ℤ × ℤ) → ℤ)
    (amplitude : (ℤ × ℤ) → ℂ) :
    (∑ h ∈ F, ∑ h' ∈ F,
      if Int.gcd (e : ℤ)
          (((m : ℤ) * ((w : ℤ) * ell h) * ((w : ℤ) * ell h')) / (w : ℤ) ^ 2) = 1 then
        (∑ n ∈ I, ∑ n' ∈ I,
          PrimeGap186.sourceSecondaryPairTerm m r₁ q₀ u₁ v₁ v₂ q₂ w
            A B ℓ E ψN N ((w : ℤ) * ell h) ((w : ℤ) * ell h') ⊤ (w * e) n n') *
          (amplitude h * star (amplitude h'))
      else 0) =
      (incidencePhysicalEnergy (m := m) (w := w) (e := e) A B (F.image ell) I
        (incidenceGroupedCoefficient F ell amplitude)
        (incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N) : ℂ) := by
  have hem : Nat.Coprime e m := (Nat.coprime_mul_iff_left.mp hdm).2
  let Fu := F.filter (fun h => IsUnit (ell h : ZMod e))
  have hpair := PrimeGap186.sourceSecondary_pair_kernel_gram_identity
    m r₁ q₀ u₁ v₁ v₂ q₂ w (w * e) A B ℓ E ψN N Fu I
      (fun h => (w : ℤ) * ell h) amplitude
      (fun h h' => amplitude h * star (amplitude h')) (fun _ _ => rfl)
  have hpair' : incidencePhysicalGram (m := m) (w := w) (e := e) A B F I ell amplitude
      (incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N) =
      ∑ h ∈ Fu, ∑ h' ∈ Fu,
        (∑ n ∈ I, ∑ n' ∈ I,
          PrimeGap186.sourceSecondaryPairTerm m r₁ q₀ u₁ v₁ v₂ q₂ w
            A B ℓ E ψN N ((w : ℤ) * ell h) ((w : ℤ) * ell h') ⊤ (w * e) n n') *
          (amplitude h * star (amplitude h')) := by
    have hfilter (s : Finset ((ℤ × ℤ) × ℤ))
        (dec : DecidablePred (fun i : (ℤ × ℤ) × ℤ => IsUnit (i.2 : ZMod w))) :
        @Finset.filter ((ℤ × ℤ) × ℤ) (fun i => IsUnit (i.2 : ZMod w)) dec s =
          @Finset.filter ((ℤ × ℤ) × ℤ) (fun i => IsUnit (i.2 : ZMod w))
            (fun i => Classical.propDecidable (IsUnit (i.2 : ZMod w))) s :=
      @Finset.filter_congr_decidable ((ℤ × ℤ) × ℤ) s
        (fun i => IsUnit (i.2 : ZMod w)) dec
        (fun i => Classical.propDecidable (IsUnit (i.2 : ZMod w)))
    simpa only [incidencePhysicalGram, incidenceSourceNumerator, Fu,
      Finset.product_eq_sprod, hfilter] using hpair
  rw [← incidencePhysicalGram_eq hwe hdm, hpair']
  simp only [Fu, Finset.sum_filter, Finset.ite_sum_zero,
    incidenceQuotientFrequencyMask hem, ite_and]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceQuotientFrequencyMask
#print axioms PrimeGap182Audit.incidenceSourceEnergyRow_eq
