import IncidencePhysicalTaylor
import IncidenceFrequencyBlock

/-!
# Exact original-row selection for the positive source energy

The original sum over d is reindexed by d = w e. Its frequency gcd
gate itself removes every row not prime to m. No row is discarded on
the basis of a desired estimate.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem incidenceSum_multiples {α : Type*} [AddCommMonoid α]
    (Dmax w : ℕ) (hw : 0 < w) (f : ℕ → α) :
    (∑ d ∈ Finset.Icc 1 Dmax, if w ∣ d then f (d / w) else 0) =
      ∑ e ∈ Finset.Icc 1 (Dmax / w), f e := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun d _ => d / w) ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hd, hwd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdmax⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hd1 hwd) hw,
      Nat.div_le_div_right hdmax⟩
  · intro d hd d' hd' he
    have hwd := (Finset.mem_filter.mp hd).2
    have hwd' := (Finset.mem_filter.mp hd').2
    calc
      d = w * (d / w) := (Nat.mul_div_cancel' hwd).symm
      _ = w * (d' / w) := congrArg (w * ·) he
      _ = d' := Nat.mul_div_cancel' hwd'
  · intro e he
    obtain ⟨he1, hemax⟩ := Finset.mem_Icc.mp he
    refine ⟨w * e, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hw he1, ?_⟩,
      dvd_mul_right _ _⟩, Nat.mul_div_cancel_left e hw⟩
    exact (Nat.mul_comm w e).trans_le ((Nat.le_div_iff_mul_le hw).mp hemax)
  · intro d _
    rfl

theorem incidenceFrequencyGate_coprime {m w e : ℕ} [NeZero w]
    (l l' : ℤ)
    (hgate : Int.gcd (e : ℤ)
      (((m : ℤ) * ((w : ℤ) * l) * ((w : ℤ) * l')) / (w : ℤ) ^ 2) = 1) :
    Nat.Coprime e m := by
  have hw : (w : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne w
  have hquot : ((m : ℤ) * ((w : ℤ) * l) * ((w : ℤ) * l')) / (w : ℤ) ^ 2 =
      (m : ℤ) * l * l' := by
    rw [show (m : ℤ) * ((w : ℤ) * l) * ((w : ℤ) * l') =
      (w : ℤ) ^ 2 * ((m : ℤ) * l * l') by ring,
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hw)]
  rw [hquot, ← Int.isCoprime_iff_gcd_eq_one,
    ← ZMod.coe_int_isUnit_iff_isCoprime] at hgate
  simp only [Int.cast_mul, Int.cast_natCast, IsUnit.mul_iff] at hgate
  exact ((ZMod.isUnit_iff_coprime m e).mp hgate.1.1).symm

def incidenceEnergyRows (Dmax w m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Dmax / w)).filter (fun e => Nat.Coprime e w ∧ Nat.Coprime e m)

def incidenceRawBlockEnergy (m w Dmax r₁ q₀ u₁ v₁ v₂ q₂ : ℕ)
    (A B ℓ : ℤ) (E : ZMod q₀ → Finset (ZMod q₀)) (ψN : ℝ → ℝ) (N : ℝ)
    (F : Finset (ℤ × ℤ)) (I : Finset ℤ) (ell : ℤ × ℤ → ℤ)
    (amp : ℕ → ℤ × ℤ → ℂ) (ρ : ℕ → ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Dmax,
    if w ∣ d ∧ Nat.Coprime (d / w) w then
      (ρ d : ℂ) * ∑ h ∈ F, ∑ h' ∈ F,
        if Int.gcd ((d / w : ℕ) : ℤ)
            (((m : ℤ) * ((w : ℤ) * ell h) * ((w : ℤ) * ell h')) / (w : ℤ) ^ 2) = 1 then
          (∑ n ∈ I, ∑ n' ∈ I,
            PrimeGap186.sourceSecondaryPairTerm m r₁ q₀ u₁ v₁ v₂ q₂ w
              A B ℓ E ψN N ((w : ℤ) * ell h) ((w : ℤ) * ell h') ⊤ d n n') *
            (amp d h * star (amp d h'))
        else 0
    else 0

theorem incidenceRawBlockEnergy_eq {m w : ℕ} [NeZero m] [NeZero w]
    (hwm : Nat.Coprime w m)
    (Dmax r₁ q₀ u₁ v₁ v₂ q₂ : ℕ) (A B ℓ : ℤ)
    (E : ZMod q₀ → Finset (ZMod q₀)) (ψN : ℝ → ℝ) (N : ℝ)
    (F : Finset (ℤ × ℤ)) (I : Finset ℤ) (ell : ℤ × ℤ → ℤ)
    (amp : ℕ → ℤ × ℤ → ℂ) (ρ : ℕ → ℝ) :
    incidenceRawBlockEnergy m w Dmax r₁ q₀ u₁ v₁ v₂ q₂ A B ℓ E ψN N F I ell amp ρ =
      ((∑ e ∈ incidenceEnergyRows Dmax w m,
        ρ (w * e) * incidencePhysicalEnergyOrZero (m := m) (w := w) e A B (F.image ell) I
          (incidenceGroupedCoefficient F ell (amp (w * e)))
          (incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N)) : ℝ) := by
  let f (e : ℕ) : ℂ :=
    if Nat.Coprime e w then
      (ρ (w * e) : ℂ) * ∑ h ∈ F, ∑ h' ∈ F,
        if Int.gcd (e : ℤ)
            (((m : ℤ) * ((w : ℤ) * ell h) * ((w : ℤ) * ell h')) / (w : ℤ) ^ 2) = 1 then
          (∑ n ∈ I, ∑ n' ∈ I,
            PrimeGap186.sourceSecondaryPairTerm m r₁ q₀ u₁ v₁ v₂ q₂ w
              A B ℓ E ψN N ((w : ℤ) * ell h) ((w : ℤ) * ell h') ⊤ (w * e) n n') *
            (amp (w * e) h * star (amp (w * e) h'))
        else 0
    else 0
  have hmultiple : incidenceRawBlockEnergy m w Dmax r₁ q₀ u₁ v₁ v₂ q₂
      A B ℓ E ψN N F I ell amp ρ =
      ∑ d ∈ Finset.Icc 1 Dmax, if w ∣ d then f (d / w) else 0 := by
    unfold incidenceRawBlockEnergy
    apply Finset.sum_congr rfl
    intro d _
    by_cases hwd : w ∣ d
    · rw [ite_eq_left hwd]
      dsimp only [f]
      rw [Nat.mul_div_cancel' hwd]
      simp only [hwd, true_and]
    · rw [ite_eq_right hwd, ite_eq_right (fun h => hwd h.1)]
  rw [hmultiple, incidenceSum_multiples Dmax w (Nat.pos_of_ne_zero (NeZero.ne w))]
  calc
    _ = ∑ e ∈ incidenceEnergyRows Dmax w m,
        (ρ (w * e) : ℂ) *
          (incidencePhysicalEnergyOrZero (m := m) (w := w) e A B (F.image ell) I
            (incidenceGroupedCoefficient F ell (amp (w * e)))
            (incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N) : ℂ) := by
      rw [incidenceEnergyRows, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      have he0 : e ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp he).1
      have : NeZero e := ⟨he0⟩
      dsimp only [f]
      by_cases hew : Nat.Coprime e w
      · rw [ite_eq_left hew]
        by_cases hem : Nat.Coprime e m
        · rw [ite_eq_left ⟨hew, hem⟩, incidencePhysicalEnergyOrZero_of_ne,
            incidenceSourceEnergyRow_eq hew.symm ((Nat.coprime_mul_iff_left).mpr ⟨hwm, hem⟩)]
        · rw [ite_eq_right (fun h => hem h.2)]
          apply mul_eq_zero_of_right
          apply Finset.sum_eq_zero
          intro h _
          apply Finset.sum_eq_zero
          intro h' _
          exact ite_eq_right (fun hg => hem (incidenceFrequencyGate_coprime (ell h) (ell h') hg))
      · rw [ite_eq_right hew, ite_eq_right (fun h => hew h.1)]
    _ = _ := by simp only [Complex.ofReal_sum, Complex.ofReal_mul]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSum_multiples
#print axioms PrimeGap182Audit.incidenceFrequencyGate_coprime
#print axioms PrimeGap182Audit.incidenceRawBlockEnergy_eq
