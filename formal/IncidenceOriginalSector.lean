import IncidenceRowPartition
import IncidencePhysicalSector

/-!
# Incidence bounds summed over the actual source rows

The compatibility lines, frequency divisors, and original integer γ
are partitioned exactly. The resulting estimate uses the previously
proved physical incidence bound on every nonempty original sector.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators ContDiff

set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

def incidenceAllCompatibilityLines {q₀ : ℕ} [NeZero q₀]
    (c : (ZMod q₀)ˣ) (S : ZMod q₀ → Finset (ZMod q₀)) (e : ZMod q₀) :
    Finset (ZMod q₀) :=
  if he : IsUnit e then incidenceCompatibilityLines c he.unit (S e) else ∅

theorem incidenceAllCompatibilityLines_card {q₀ : ℕ} [NeZero q₀]
    (c : (ZMod q₀)ˣ) (S : ZMod q₀ → Finset (ZMod q₀)) (κ : ℝ) (hκ : 0 ≤ κ)
    (hS : ∀ e, IsUnit e → ((S e).card : ℝ) ≤ κ) (e : ZMod q₀) :
    ((incidenceAllCompatibilityLines c S e).card : ℝ) ≤ κ := by
  unfold incidenceAllCompatibilityLines
  split_ifs with he
  · exact (Nat.cast_le.mpr (incidenceCompatibilityLines_card c he.unit (S e))).trans (hS e he)
  · simpa only [Finset.card_empty, Nat.cast_zero] using hκ

theorem incidenceAllCompatibilityLines_unit {q₀ : ℕ} [NeZero q₀]
    (c e : (ZMod q₀)ˣ) (S : ZMod q₀ → Finset (ZMod q₀)) :
    incidenceAllCompatibilityLines c S (e : ZMod q₀) =
      incidenceCompatibilityLines c e (S (e : ZMod q₀)) := by
  unfold incidenceAllCompatibilityLines
  rw [dite_eq_left e.isUnit]
  congr 1
  apply Units.ext
  exact e.isUnit.unit_spec

theorem incidenceOriginalRows_line_partition {M : Type*} [AddCommMonoid M]
    (D : Finset ℕ) (q₀ : ℕ) [NeZero q₀] (Lines : ZMod q₀ → Finset (ZMod q₀))
    (f : ℕ → ℕ → ZMod q₀ → ℤ → M) :
    (∑ e ∈ D, ∑ t ∈ e.divisors, ∑ ζ ∈ Lines (e : ZMod q₀),
      ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ), f e t ζ γ) =
      ∑ t ∈ incidenceRowDivisors D, ∑ r : ZMod q₀,
        ∑ ζ ∈ Lines ((t : ZMod q₀) * r),
          ∑ p ∈ incidenceResidueRows D t q₀ r, f p.1 t ζ p.2 := by
  have hp := incidenceRows_divisor_residue_partition D q₀
    (fun t r p => ∑ ζ ∈ Lines ((t : ZMod q₀) * r), f p.1 t ζ p.2)
  rw [incidenceOriginalRows_sum] at hp
  calc
    _ = ∑ e ∈ D, ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ),
        ∑ t ∈ e.divisors, ∑ ζ ∈ Lines ((t : ZMod q₀) * ((e / t : ℕ) : ZMod q₀)),
          f e t ζ γ := by
      apply Finset.sum_congr rfl
      intro e _
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ht), Finset.sum_comm]
    _ = ∑ t ∈ incidenceRowDivisors D, ∑ r : ZMod q₀,
        ∑ p ∈ incidenceResidueRows D t q₀ r,
          ∑ ζ ∈ Lines ((t : ZMod q₀) * r), f p.1 t ζ p.2 := hp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm

theorem incidenceOriginalSector_window_bound (hK4 : AllIncidenceRankFourBounds)
    (η c₀ R : ℝ) (hη : 0 < η) (hc₀ : 0 < c₀) (hR : 0 ≤ R)
    (Ap Ep : ℕ → ℝ) (hAp : ∀ j, 0 ≤ Ap j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ j y, |iteratedDeriv j ψ y| ≤ Ap j * (Real.log x) ^ Ep j) →
      ∀ q₀ g q : ℕ, ∀ [NeZero q₀] [NeZero g] [NeZero q],
      Nat.Coprime q₀ (g * q) → Nat.Coprime g q → Squarefree q →
      ∀ A B : ℤ, IsUnit (A : ZMod q) →
      ∀ w₂ : ℕ, Nat.Coprime w₂ q → g ∣ w₂ →
      ∀ N c esc Λ Ewidth w d₀ L κ : ℝ,
      0 < N → 0 < c → 0 < esc → 0 < Λ → 0 < Ewidth → 0 < w →
      0 ≤ L → 0 ≤ κ →
      ∀ J : ℕ, 0 < J → Λ ≤ (J : ℝ) * (N / (c * (q₀ : ℝ) * esc)) →
      ∀ D : Finset ℕ, ∀ ρ : ℕ → ℝ,
      (∀ e ∈ D, 0 ≤ ρ e ∧ ρ e ≤ L) →
      (∀ e ∈ D, Nat.Coprime e (g * q) ∧
        |w * (e : ℝ) - d₀| ≤ Ewidth ∧ c₀ * esc ≤ (e : ℝ) ∧ (e : ℝ) ≤ 2 * esc) →
      ∀ Lines : ZMod q₀ → Finset (ZMod q₀), (∀ r, ((Lines r).card : ℝ) ≤ κ) →
      ∀ S : Finset ℤ, ∀ U : ℕ → ℝ, ∀ τD : ℝ, 0 ≤ τD →
      (∀ t ∈ incidenceRowDivisors D, 0 < U t) →
      (∀ t ∈ incidenceRowDivisors D, ∀ a ∈ incidenceDividedCoefficientSet S (t * w₂),
        U t ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U t ∧ IsUnit (a : ZMod q)) →
      (∀ t ∈ incidenceRowDivisors D, ∀ a ∈ incidenceDividedCoefficientSet S (t * w₂),
        (a.natAbs.divisors.card : ℝ) ≤ τD) →
      (∀ t ∈ incidenceRowDivisors D, ∀ a ∈ incidenceDividedCoefficientSet S (t * w₂),
        |((((t * w₂ : ℕ) : ℤ) * a : ℤ) : ℝ) / Λ| ≤ 2) →
      ∀ coeff : ℤ → ℂ,
      let V₀ := (R / c₀ + 2) * (N / (c * (q₀ : ℝ) * esc))
      (∑ e ∈ D, ρ e * ∑ t ∈ e.divisors, ∑ ζ ∈ Lines (e : ZMod q₀),
        ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ),
          ‖∑ a ∈ incidenceDividedCoefficientSet S (t * w₂),
            coeff (((t * w₂ : ℕ) : ℤ) * a) *
              incidenceProgressionResponse (m := q₀ * (g * q)) (A : ZMod _) B q₀ e
                (ζ.val : ℤ) γ (fun n => (ψ (c * (n : ℝ) / N) : ℂ))
                (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2) ≤
        (q₀ : ℝ) * κ * ((1 + x ^ (2 * η)) * K * L) *
          ∑ t ∈ incidenceRowDivisors D,
            (2 * (Ewidth / (w * (t : ℝ) * (q₀ : ℝ))) * esc +
              (J : ℝ) * (q : ℝ) ^ (3 / 2 + η) +
              (q : ℝ) ^ (1 / 2 + η) *
                ((J : ℝ) * (Ewidth / (w * (t : ℝ) * (q₀ : ℝ))) + 2 * esc)) *
            ((1 + 8 * U t * V₀ / (q : ℝ)) *
              (((incidenceDividedCoefficientSet S (t * w₂)).card : ℝ) + 8 * V₀ * τD)) *
            ∑ a ∈ incidenceDividedCoefficientSet S (t * w₂),
              ‖coeff (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2 := by
  obtain ⟨K, hK, hsector⟩ := incidencePhysicalSector_window_bound hK4 η c₀ R hη hc₀ hR Ap Ep hAp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsector, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro ψ hψ hsψ hder q₀ g q _ _ _ h0 hg hq A B hA w₂ hw₂ hgw₂
    N c esc Λ Ewidth w d₀ L κ hN hc hesc hΛ hEwidth hw hL hκ J hJ hJscale
    D ρ hρ hD Lines hLines S U τD hτD hU hS hτ hell coeff V₀
  have hq₀R : 0 < (q₀ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₀)
  have hV₀ : 0 < V₀ := by
    dsimp only [V₀]
    exact mul_pos (by positivity) (by positivity)
  let amp (e t : ℕ) (ζ : ZMod q₀) (γ : ℤ) : ℝ :=
    ‖∑ a ∈ incidenceDividedCoefficientSet S (t * w₂),
      coeff (((t * w₂ : ℕ) : ℤ) * a) *
        incidenceProgressionResponse (m := q₀ * (g * q)) (A : ZMod _) B q₀ e
          (ζ.val : ℤ) γ (fun n => (ψ (c * (n : ℝ) / N) : ℂ))
          (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2
  let bound (t : ℕ) : ℝ :=
    (1 + x ^ (2 * η)) * K * L *
      (2 * (Ewidth / (w * (t : ℝ) * (q₀ : ℝ))) * esc +
        (J : ℝ) * (q : ℝ) ^ (3 / 2 + η) +
        (q : ℝ) ^ (1 / 2 + η) *
          ((J : ℝ) * (Ewidth / (w * (t : ℝ) * (q₀ : ℝ))) + 2 * esc)) *
      ((1 + 8 * U t * V₀ / (q : ℝ)) *
        (((incidenceDividedCoefficientSet S (t * w₂)).card : ℝ) + 8 * V₀ * τD)) *
      ∑ a ∈ incidenceDividedCoefficientSet S (t * w₂),
        ‖coeff (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2
  have hb0 (t : ℕ) (ht : t ∈ incidenceRowDivisors D) : 0 ≤ bound t := by
    have hu := (hU t ht).le
    dsimp only [bound]
    positivity
  have hb (t : ℕ) (ht : t ∈ incidenceRowDivisors D) (r ζ : ZMod q₀) :
      (∑ p ∈ incidenceResidueRows D t q₀ r, ρ p.1 * amp p.1 t ζ p.2) ≤ bound t := by
    obtain ⟨e, he, hte⟩ := Finset.mem_biUnion.mp ht
    have htpos : 0 < t := Nat.pos_of_mem_divisors hte
    have htq : Nat.Coprime t q :=
      ((hD e he).1.of_dvd_left (Nat.dvd_of_mem_divisors hte)).of_dvd_right (dvd_mul_left q g)
    have htR : 0 < (t : ℝ) := by exact_mod_cast htpos
    obtain ⟨Bhat, _, _, hBhat⟩ := incidenceModularShift_exists q₀ (g * q) B (ζ.val : ℤ)
    have hrows (p : ℕ × ℤ) (hp : p ∈ incidenceResidueRows D t q₀ r) :=
      incidenceResidueRows_geometry D t q₀ r p hp
    have hgeom (p : ℕ × ℤ) (hp : p ∈ incidenceResidueRows D t q₀ r) :
        (t : ℤ) ∣ (p.1 : ℤ) ∧
        Int.ModEq (q₀ : ℤ) (r.val : ℤ) ((p.1 : ℤ) / (t : ℤ)) ∧
        (p.1 : ZMod q₀) = (t : ZMod q₀) * r ∧ Nat.Coprime p.1 g ∧
        |((incidenceSourceRowLabel t q₀ (r.val : ℤ) p).1 : ℝ) -
          ((d₀ / (w * (t : ℝ)) - (r.val : ℝ)) / (q₀ : ℝ))| ≤
            Ewidth / (w * (t : ℝ) * (q₀ : ℝ)) ∧
        c₀ * esc ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * esc ∧
        0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < (p.1 : ℝ) := by
      have hpD := (incidenceResidueRows_mem D t q₀ r p).mp hp |>.1
      have hrp := hrows p hp
      refine ⟨hrp.2.1, hrp.2.2.1, hrp.2.2.2.1,
        (hD p.1 hpD).1.of_dvd_right (dvd_mul_right g q), ?_, (hD p.1 hpD).2.2.1,
        (hD p.1 hpD).2.2.2, hrp.2.2.2.2⟩
      simpa only [mul_one] using incidenceSourceRowLabel_localized D t q₀ r p hp
        w d₀ Ewidth 1 hw (by simpa only [mul_one] using (hD p.1 hpD).2.1)
    exact hx ψ hψ hsψ hder q₀ g q h0 hg hq A B (ζ.val : ℤ) (r.val : ℤ) Bhat hA hBhat
      t w₂ htq hw₂ hgw₂ ((t : ZMod q₀) * r) N c esc Λ
      (Ewidth / (w * (t : ℝ) * (q₀ : ℝ)))
      ((d₀ / (w * (t : ℝ)) - (r.val : ℝ)) / (q₀ : ℝ)) L
      hN hc hesc hΛ (by positivity) hL J hJ hJscale
      (incidenceResidueRows D t q₀ r) (fun p => ρ p.1)
      (fun p hp => hρ p.1 ((incidenceResidueRows_mem D t q₀ r p).mp hp).1)
      hgeom (incidenceDividedCoefficientSet S (t * w₂)) (U t) τD (hU t ht) hτD
      (hS t ht) (hτ t ht) (hell t ht) coeff
  have hid :
      (∑ e ∈ D, ρ e * ∑ t ∈ e.divisors, ∑ ζ ∈ Lines (e : ZMod q₀),
        ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ), amp e t ζ γ) =
      ∑ t ∈ incidenceRowDivisors D, ∑ r : ZMod q₀,
        ∑ ζ ∈ Lines ((t : ZMod q₀) * r),
          ∑ p ∈ incidenceResidueRows D t q₀ r, ρ p.1 * amp p.1 t ζ p.2 := by
    simp_rw [Finset.mul_sum]
    exact incidenceOriginalRows_line_partition D q₀ Lines (fun e t ζ γ => ρ e * amp e t ζ γ)
  change (∑ e ∈ D, ρ e * ∑ t ∈ e.divisors, ∑ ζ ∈ Lines (e : ZMod q₀),
    ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ), amp e t ζ γ) ≤ _
  rw [hid]
  calc
    _ ≤ ∑ t ∈ incidenceRowDivisors D, ∑ _r : ZMod q₀, κ * bound t := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro r _
      calc
        _ ≤ ∑ _ζ ∈ Lines ((t : ZMod q₀) * r), bound t :=
          Finset.sum_le_sum (fun ζ _ => hb t ht r ζ)
        _ = ((Lines ((t : ZMod q₀) * r)).card : ℝ) * bound t := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ κ * bound t := mul_le_mul_of_nonneg_right (hLines _) (hb0 t ht)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [bound]
      ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceAllCompatibilityLines_card
#print axioms PrimeGap182Audit.incidenceAllCompatibilityLines_unit
#print axioms PrimeGap182Audit.incidenceOriginalRows_line_partition
#print axioms PrimeGap182Audit.incidenceOriginalSector_window_bound
