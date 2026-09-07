import MixedMarkedLimit182

/-!
Finite assembly of uniform arithmetic moment limits. The residue parameter
remains arbitrary after the eventual threshold, so it may depend on x.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace PrimeGap182Analytic

def UniformScaledLimit {α β : Type*} (l : Filter α)
    (S : α → β → ℝ) (A : α → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ b : β, |S x b - A x * L| ≤ ε * A x

theorem UniformScaledLimit.congr {α β : Type*} {l : Filter α}
    {S T : α → β → ℝ} {A : α → ℝ} {L : ℝ}
    (hS : UniformScaledLimit l S A L) (hST : ∀ᶠ x in l, ∀ b, S x b = T x b) :
    UniformScaledLimit l T A L := by
  intro ε hε
  filter_upwards [hS ε hε, hST] with x hx he
  intro b
  rw [← he b]
  exact hx b

theorem UniformScaledLimit.const_mul {α β : Type*} {l : Filter α}
    {S : α → β → ℝ} {A : α → ℝ} {L : ℝ}
    (hS : UniformScaledLimit l S A L) (hA : ∀ᶠ x in l, 0 ≤ A x) (c : ℝ) :
    UniformScaledLimit l (fun x b => c * S x b) A (c * L) := by
  intro ε hε
  have hc : 0 < |c| + 1 := by positivity
  have hδ : 0 < ε / (|c| + 1) := div_pos hε hc
  have hsmall : |c| * (ε / (|c| + 1)) ≤ ε := by
    calc
      _ = ε * (|c| / (|c| + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hc).mpr (le_add_of_nonneg_right zero_le_one)) hε.le
      _ = _ := mul_one ε
  filter_upwards [hS _ hδ, hA] with x hx hAx
  intro b
  rw [show c * S x b - A x * (c * L) = c * (S x b - A x * L) by ring, abs_mul]
  calc
    _ ≤ |c| * ((ε / (|c| + 1)) * A x) :=
      mul_le_mul_of_nonneg_left (hx b) (abs_nonneg _)
    _ = (|c| * (ε / (|c| + 1))) * A x := by ring
    _ ≤ ε * A x := mul_le_mul_of_nonneg_right hsmall hAx

theorem uniformScaledLimit_finsetSum {α β J : Type*} {l : Filter α}
    (s : Finset J) (S : J → α → β → ℝ) (A : α → ℝ) (L : J → ℝ)
    (hA : ∀ᶠ x in l, 0 ≤ A x)
    (hS : ∀ j ∈ s, UniformScaledLimit l (S j) A (L j)) :
    UniformScaledLimit l (fun x b => ∑ j ∈ s, S j x b) A (∑ j ∈ s, L j) := by
  intro ε hε
  have hc : (0 : ℝ) < s.card + 1 := by positivity
  have hδ : 0 < ε / ((s.card : ℝ) + 1) := div_pos hε hc
  have hsmall : (s.card : ℝ) * (ε / ((s.card : ℝ) + 1)) ≤ ε := by
    calc
      _ = ε * ((s.card : ℝ) / ((s.card : ℝ) + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hc).mpr (le_add_of_nonneg_right zero_le_one)) hε.le
      _ = _ := mul_one ε
  have hall : ∀ᶠ x in l, ∀ j ∈ s, ∀ b,
      |S j x b - A x * L j| ≤ (ε / ((s.card : ℝ) + 1)) * A x :=
    (eventually_all_finset s).mpr fun j hj => hS j hj _ hδ
  filter_upwards [hall, hA] with x hx hAx
  intro b
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ s, |S j x b - A x * L j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ s, (ε / ((s.card : ℝ) + 1)) * A x :=
      Finset.sum_le_sum fun j hj => hx j hj b
    _ = ((s.card : ℝ) * (ε / ((s.card : ℝ) + 1))) * A x := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ε * A x := mul_le_mul_of_nonneg_right hsmall hAx

theorem uniformScaledLimit_weighted_sum {α β J : Type*} {l : Filter α}
    (s : Finset J) (c : J → ℝ) (S : J → α → β → ℝ) (A : α → ℝ) (L : J → ℝ)
    (hA : ∀ᶠ x in l, 0 ≤ A x)
    (hS : ∀ j ∈ s, UniformScaledLimit l (S j) A (L j)) :
    UniformScaledLimit l (fun x b => ∑ j ∈ s, c j * S j x b) A
      (∑ j ∈ s, c j * L j) :=
  uniformScaledLimit_finsetSum s _ A _ hA fun j hj => (hS j hj).const_mul hA (c j)

theorem UniformScaledLimit.eventually_upper {α β : Type*} {l : Filter α}
    {S : α → β → ℝ} {A : α → ℝ} {L K : ℝ}
    (hS : UniformScaledLimit l S A L) (hA : ∀ᶠ x in l, 0 ≤ A x) (hLK : L ≤ K)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in l, ∀ b : β, S x b ≤ A x * (K + ε) := by
  filter_upwards [hS ε hε, hA] with x hx hAx
  intro b
  have h := (le_abs_self _).trans (hx b)
  have hmain := mul_le_mul_of_nonneg_left hLK hAx
  nlinarith only [h, hmain]

theorem mixedHarmonic_self {α : Type*} (den : α → ℝ) (u : α →₀ ℝ) :
    mixedHarmonic den u u = diagonalHarmonic den u := by
  simp only [mixedHarmonic, diagonalHarmonic, pow_two, Finsupp.sum]

#print axioms uniformScaledLimit_finsetSum
#print axioms uniformScaledLimit_weighted_sum

end PrimeGap182Analytic
