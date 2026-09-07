import IncidenceSourceRowReindex
import IncidenceCompatibilityLines

/-!
# Original row, divisor, and residue partitions

Every original integer γ with 0 ≤ γ < e is retained. The divisor t
and residue of e/t are partition labels; the identities introduce no
multiplicity factor. The affine box bound follows from the actual
localization |w e - d₀| ≤ T Δ₁.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceOriginalRows (D : Finset ℕ) : Finset (ℕ × ℤ) :=
  D.biUnion (fun e => (Finset.Ico (0 : ℤ) (e : ℤ)).image (fun γ => (e, γ)))

theorem incidenceOriginalRows_mem (D : Finset ℕ) (p : ℕ × ℤ) :
    p ∈ incidenceOriginalRows D ↔ p.1 ∈ D ∧ 0 ≤ p.2 ∧ p.2 < (p.1 : ℤ) := by
  simp [incidenceOriginalRows, Prod.ext_iff]

theorem incidenceOriginalRows_sum {M : Type*} [AddCommMonoid M]
    (D : Finset ℕ) (f : ℕ × ℤ → M) :
    (∑ p ∈ incidenceOriginalRows D, f p) =
      ∑ e ∈ D, ∑ γ ∈ Finset.Ico (0 : ℤ) (e : ℤ), f (e, γ) := by
  unfold incidenceOriginalRows
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    exact Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)
  · intro e _ d _ hed
    apply Finset.disjoint_left.mpr
    intro p he hd
    obtain ⟨γ, _, hγ⟩ := Finset.mem_image.mp he
    obtain ⟨γ', _, hγ'⟩ := Finset.mem_image.mp hd
    exact hed (congrArg Prod.fst (hγ.trans hγ'.symm))

def incidenceRowDivisors (D : Finset ℕ) : Finset ℕ := D.biUnion Nat.divisors

def incidenceResidueRows (D : Finset ℕ) (t q₀ : ℕ) [NeZero q₀] (r : ZMod q₀) :
    Finset (ℕ × ℤ) :=
  (incidenceOriginalRows D).filter
    (fun p => t ∈ p.1.divisors ∧ ((p.1 / t : ℕ) : ZMod q₀) = r)

theorem incidenceResidueRows_mem (D : Finset ℕ) (t q₀ : ℕ) [NeZero q₀]
    (r : ZMod q₀) (p : ℕ × ℤ) :
    p ∈ incidenceResidueRows D t q₀ r ↔
      p.1 ∈ D ∧ 0 ≤ p.2 ∧ p.2 < (p.1 : ℤ) ∧
        t ∈ p.1.divisors ∧ ((p.1 / t : ℕ) : ZMod q₀) = r := by
  simp only [incidenceResidueRows, Finset.mem_filter, incidenceOriginalRows_mem]
  tauto

theorem incidenceRows_divisor_residue_partition {M : Type*} [AddCommMonoid M]
    (D : Finset ℕ) (q₀ : ℕ) [NeZero q₀]
    (f : ℕ → ZMod q₀ → ℕ × ℤ → M) :
    (∑ p ∈ incidenceOriginalRows D, ∑ t ∈ p.1.divisors,
      f t ((p.1 / t : ℕ) : ZMod q₀) p) =
      ∑ t ∈ incidenceRowDivisors D, ∑ r : ZMod q₀,
        ∑ p ∈ incidenceResidueRows D t q₀ r, f t r p := by
  have hsub (p : ℕ × ℤ) (hp : p ∈ incidenceOriginalRows D) :
      p.1.divisors ⊆ incidenceRowDivisors D := by
    intro t ht
    exact Finset.mem_biUnion.mpr ⟨p.1, (incidenceOriginalRows_mem D p).mp hp |>.1, ht⟩
  calc
    _ = ∑ p ∈ incidenceOriginalRows D, ∑ t ∈ incidenceRowDivisors D,
        if t ∈ p.1.divisors then f t ((p.1 / t : ℕ) : ZMod q₀) p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      congr 1
      exact (Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (hsub p hp))).symm
    _ = ∑ t ∈ incidenceRowDivisors D, ∑ p ∈ incidenceOriginalRows D,
        if t ∈ p.1.divisors then f t ((p.1 / t : ℕ) : ZMod q₀) p else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [incidenceResidueRows, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases ht : t ∈ p.1.divisors
      · simp only [ht, true_and, ite_true]
        simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      · simp only [ht, false_and, ite_false, Finset.sum_const_zero]

theorem incidenceResidueRows_geometry (D : Finset ℕ) (t q₀ : ℕ) [NeZero q₀]
    (r : ZMod q₀) (p : ℕ × ℤ) (hp : p ∈ incidenceResidueRows D t q₀ r) :
    0 < t ∧ (t : ℤ) ∣ (p.1 : ℤ) ∧
      Int.ModEq (q₀ : ℤ) (r.val : ℤ) ((p.1 : ℤ) / (t : ℤ)) ∧
      (p.1 : ZMod q₀) = (t : ZMod q₀) * r ∧
      0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < (p.1 : ℝ) := by
  obtain ⟨_, hγ0, hγe, hte, hr⟩ := (incidenceResidueRows_mem D t q₀ r p).mp hp
  have htd := Nat.dvd_of_mem_divisors hte
  have ht : 0 < t := Nat.pos_of_mem_divisors hte
  have htdI : (t : ℤ) ∣ (p.1 : ℤ) := by exact_mod_cast htd
  have hrI : (((p.1 : ℤ) / (t : ℤ) : ℤ) : ZMod q₀) = (r.val : ZMod q₀) := by
    rw [← Int.natCast_ediv, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hr
  have hmod : Int.ModEq (q₀ : ℤ) (r.val : ℤ) ((p.1 : ℤ) / (t : ℤ)) := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [Int.cast_natCast] using hrI.symm
  have heq : (p.1 : ZMod q₀) = (t : ZMod q₀) * r := by
    rw [← hr, ← Nat.cast_mul, Nat.mul_div_cancel' htd]
  exact ⟨ht, htdI, hmod, heq, by exact_mod_cast hγ0, by exact_mod_cast hγe⟩

theorem incidenceSourceRowLabel_localized (D : Finset ℕ) (t q₀ : ℕ) [NeZero q₀]
    (r : ZMod q₀) (p : ℕ × ℤ) (hp : p ∈ incidenceResidueRows D t q₀ r)
    (w d₀ T Δ₁ : ℝ) (hw : 0 < w)
    (hlocal : |w * (p.1 : ℝ) - d₀| ≤ T * Δ₁) :
    |((incidenceSourceRowLabel t q₀ (r.val : ℤ) p).1 : ℝ) -
        ((d₀ / (w * (t : ℝ)) - (r.val : ℝ)) / (q₀ : ℝ))| ≤
      T * Δ₁ / (w * (t : ℝ) * (q₀ : ℝ)) := by
  obtain ⟨ht, htd, hmod, _, _, _⟩ := incidenceResidueRows_geometry D t q₀ r p hp
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hqR : 0 < (q₀ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₀)
  have hspec := congrArg (fun z : ℤ => (z : ℝ))
    (incidenceSourceRowLabel_spec t q₀ (r.val : ℤ) p htd hmod)
  simp only [Int.cast_natCast, Int.cast_mul, Int.cast_add] at hspec
  have hid :
      ((incidenceSourceRowLabel t q₀ (r.val : ℤ) p).1 : ℝ) -
          ((d₀ / (w * (t : ℝ)) - (r.val : ℝ)) / (q₀ : ℝ)) =
        (w * (p.1 : ℝ) - d₀) / (w * (t : ℝ) * (q₀ : ℝ)) := by
    rw [hspec]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (by positivity : 0 < w * (t : ℝ) * (q₀ : ℝ))]
  exact div_le_div_of_nonneg_right hlocal (by positivity)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceOriginalRows_mem
#print axioms PrimeGap182Audit.incidenceOriginalRows_sum
#print axioms PrimeGap182Audit.incidenceResidueRows_mem
#print axioms PrimeGap182Audit.incidenceRows_divisor_residue_partition
#print axioms PrimeGap182Audit.incidenceResidueRows_geometry
#print axioms PrimeGap182Audit.incidenceSourceRowLabel_localized
