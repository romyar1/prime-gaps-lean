import IncidenceAngularSource

/-!
# Exact row transport from e=tE to E=r₀+q₀u

The finite physical row set is pushed to the integer plane with its
actual nonnegative weights. The map is injective on the original
divisibility/progression conditions, so there is no q₀ or t multiplicity
loss. The second coordinate remains the original integer γ.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceSourceRowLabel (t q₀ : ℕ) (r₀ : ℤ) (p : ℕ × ℤ) : ℤ × ℤ :=
  ((((p.1 : ℤ) / (t : ℤ)) - r₀) / (q₀ : ℤ), p.2)

theorem incidenceSourceRowLabel_spec (t q₀ : ℕ) (r₀ : ℤ) (p : ℕ × ℤ)
    (ht : (t : ℤ) ∣ (p.1 : ℤ))
    (hq : Int.ModEq (q₀ : ℤ) r₀ ((p.1 : ℤ) / (t : ℤ))) :
    (p.1 : ℤ) = (t : ℤ) *
      ((q₀ : ℤ) * (incidenceSourceRowLabel t q₀ r₀ p).1 + r₀) := by
  unfold incidenceSourceRowLabel
  dsimp only
  rw [Int.mul_ediv_cancel' (Int.modEq_iff_dvd.mp hq), sub_add_cancel,
    Int.mul_ediv_cancel' ht]

theorem incidenceSourceRowLabel_injective (t q₀ : ℕ) (r₀ : ℤ) (S : Finset (ℕ × ℤ))
    (ht : ∀ p ∈ S, (t : ℤ) ∣ (p.1 : ℤ))
    (hq : ∀ p ∈ S, Int.ModEq (q₀ : ℤ) r₀ ((p.1 : ℤ) / (t : ℤ))) :
    Set.InjOn (incidenceSourceRowLabel t q₀ r₀) S := by
  intro p hp r hr heq
  apply Prod.ext
  · have hh := congrArg (fun z : ℤ × ℤ => (t : ℤ) * ((q₀ : ℤ) * z.1 + r₀)) heq
    rw [← incidenceSourceRowLabel_spec t q₀ r₀ p (ht p hp) (hq p hp),
      ← incidenceSourceRowLabel_spec t q₀ r₀ r (ht r hr) (hq r hr)] at hh
    exact_mod_cast hh
  · exact congrArg (fun z : ℤ × ℤ => z.2) heq

def incidenceSourceRowWeight (t q₀ : ℕ) (r₀ : ℤ) (S : Finset (ℕ × ℤ))
    (ρ : ℕ × ℤ → ℝ) (z : ℤ × ℤ) : ℝ :=
  ∑ p ∈ S, if incidenceSourceRowLabel t q₀ r₀ p = z then ρ p else 0

theorem incidenceSourceRowWeight_support (t q₀ : ℕ) (r₀ : ℤ) (S : Finset (ℕ × ℤ))
    (ρ : ℕ × ℤ → ℝ) (z : ℤ × ℤ)
    (hz : incidenceSourceRowWeight t q₀ r₀ S ρ z ≠ 0) :
    ∃ p ∈ S, incidenceSourceRowLabel t q₀ r₀ p = z ∧ ρ p ≠ 0 := by
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact ⟨p, hp, by simpa only [ite_ne_right_iff] using hne⟩

theorem incidenceSourceRowWeight_nonneg (t q₀ : ℕ) (r₀ : ℤ) (S : Finset (ℕ × ℤ))
    (ρ : ℕ × ℤ → ℝ) (hρ : ∀ p ∈ S, 0 ≤ ρ p) (z : ℤ × ℤ) :
    0 ≤ incidenceSourceRowWeight t q₀ r₀ S ρ z := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact hρ p hp
  · rfl

theorem incidenceSourceRowWeight_apply (t q₀ : ℕ) (r₀ : ℤ) (S : Finset (ℕ × ℤ))
    (ht : ∀ p ∈ S, (t : ℤ) ∣ (p.1 : ℤ))
    (hq : ∀ p ∈ S, Int.ModEq (q₀ : ℤ) r₀ ((p.1 : ℤ) / (t : ℤ)))
    (ρ : ℕ × ℤ → ℝ) (p : ℕ × ℤ) (hp : p ∈ S) :
    incidenceSourceRowWeight t q₀ r₀ S ρ (incidenceSourceRowLabel t q₀ r₀ p) = ρ p := by
  unfold incidenceSourceRowWeight
  rw [Finset.sum_eq_single p]
  · simp only [ite_true]
  · intro r hr hrp
    exact ite_eq_right (fun heq => hrp
      (incidenceSourceRowLabel_injective t q₀ r₀ S ht hq hr hp heq))
  · exact fun hn => False.elim (hn hp)

theorem incidenceSourceRowWeight_le (t q₀ : ℕ) (r₀ : ℤ) (S : Finset (ℕ × ℤ))
    (ht : ∀ p ∈ S, (t : ℤ) ∣ (p.1 : ℤ))
    (hq : ∀ p ∈ S, Int.ModEq (q₀ : ℤ) r₀ ((p.1 : ℤ) / (t : ℤ)))
    (ρ : ℕ × ℤ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hρ : ∀ p ∈ S, ρ p ≤ L)
    (z : ℤ × ℤ) : incidenceSourceRowWeight t q₀ r₀ S ρ z ≤ L := by
  by_cases hz : incidenceSourceRowWeight t q₀ r₀ S ρ z = 0
  · simpa only [hz] using hL
  obtain ⟨p, hp, hlabel, _⟩ := incidenceSourceRowWeight_support t q₀ r₀ S ρ z hz
  rw [← hlabel, incidenceSourceRowWeight_apply t q₀ r₀ S ht hq ρ p hp]
  exact hρ p hp

theorem incidenceSourceRowWeight_sum (t q₀ : ℕ) (r₀ : ℤ) (S : Finset (ℕ × ℤ))
    (ht : ∀ p ∈ S, (t : ℤ) ∣ (p.1 : ℤ))
    (hq : ∀ p ∈ S, Int.ModEq (q₀ : ℤ) r₀ ((p.1 : ℤ) / (t : ℤ)))
    (ρ : ℕ × ℤ → ℝ) (F : ℤ × ℤ → ℝ) :
    (∑' z : ℤ × ℤ, incidenceSourceRowWeight t q₀ r₀ S ρ z * F z) =
      ∑ p ∈ S, ρ p * F (incidenceSourceRowLabel t q₀ r₀ p) := by
  have hs : (∑' z : ℤ × ℤ, incidenceSourceRowWeight t q₀ r₀ S ρ z * F z) =
      ∑ z ∈ S.image (incidenceSourceRowLabel t q₀ r₀),
        incidenceSourceRowWeight t q₀ r₀ S ρ z * F z := by
    apply tsum_eq_sum
    intro z hz
    have hw : incidenceSourceRowWeight t q₀ r₀ S ρ z = 0 := by
      by_contra hw
      obtain ⟨p, hp, heq, _⟩ := incidenceSourceRowWeight_support t q₀ r₀ S ρ z hw
      exact hz (Finset.mem_image.mpr ⟨p, hp, heq⟩)
    rw [hw, zero_mul]
  rw [hs, Finset.sum_image (incidenceSourceRowLabel_injective t q₀ r₀ S ht hq)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [incidenceSourceRowWeight_apply t q₀ r₀ S ht hq ρ p hp]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourceRowLabel_spec
#print axioms PrimeGap182Audit.incidenceSourceRowLabel_injective
#print axioms PrimeGap182Audit.incidenceSourceRowWeight_support
#print axioms PrimeGap182Audit.incidenceSourceRowWeight_nonneg
#print axioms PrimeGap182Audit.incidenceSourceRowWeight_apply
#print axioms PrimeGap182Audit.incidenceSourceRowWeight_le
#print axioms PrimeGap182Audit.incidenceSourceRowWeight_sum
