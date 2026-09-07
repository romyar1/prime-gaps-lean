import SharpMinorant
import PrimeGaps186

/-!
Exact residual multiplicities over all integers, not a finite numerical
sample. The two literal order types have respectively four and twenty
labelings of any admissible set of five distinct primes.
-/

noncomputable section
open scoped BigOperators
open PrimeGap186

namespace PrimeGap182Analytic

def sharpResidualOrder {α : Type*} [LT α] (j : Fin 2) (p : Fin 5 → α) : Prop :=
  if j = 0 then p 3 < p 2 ∧ p 2 < p 1 ∧ p 1 < p 0 ∧ p 3 < p 4
  else p 1 < p 0 ∧ p 1 < p 2 ∧ p 3 < p 4

instance {α : Type*} [LT α] [DecidableLT α] (j : Fin 2) (p : Fin 5 → α) :
    Decidable (sharpResidualOrder j p) := by
  unfold sharpResidualOrder
  infer_instance

def sharpResidualPerms (j : Fin 2) : Finset (Equiv.Perm (Fin 5)) :=
  (permsOfFinset (Finset.univ : Finset (Fin 5))).filter (fun σ => sharpResidualOrder j σ)

theorem sharpResidualPerms_card : ∀ j : Fin 2,
    (sharpResidualPerms j).card = if j = 0 then 4 else 20 := by
  decide +kernel

open Classical in
def sharpResidualTuples (x a : ℝ) (n : ℕ) (j : Fin 2) : Finset (Fin 5 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n)).filter fun p =>
    Function.Injective p ∧ (∏ i, p i) = n ∧
      (∀ i k : Fin 5, i < k → (p i : ℝ) * (p k : ℝ) < x ^ a) ∧ sharpResidualOrder j p

theorem distinct_prime_product_squarefree {p : Fin 5 → ℕ}
    (hinj : Function.Injective p) (hp : ∀ i, (p i).Prime) : Squarefree (∏ i, p i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    change IsRelPrime (p i) (p j)
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))
  · intro i _
    exact (hp i).squarefree

theorem sharpExceptional_squarefree {x a : ℝ} {n : ℕ} (h : SharpExceptional x a n) :
    Squarefree n := by
  obtain ⟨p, hi, hp, he, _⟩ := h
  rw [← he]
  exact distinct_prime_product_squarefree hi hp

theorem sharp_pairs_reindex {x a : ℝ} {p : Fin 5 → ℕ}
    (hp : ∀ i j : Fin 5, i < j → (p i : ℝ) * (p j : ℝ) < x ^ a)
    (σ : Equiv.Perm (Fin 5)) :
    ∀ i j : Fin 5, i < j → (p (σ i) : ℝ) * (p (σ j) : ℝ) < x ^ a := by
  intro i j hij
  rcases lt_or_gt_of_ne (σ.injective.ne hij.ne) with hs | hs
  · exact hp _ _ hs
  · simpa only [mul_comm] using hp _ _ hs

theorem sharpResidualTuples_mem {x a : ℝ} {n : ℕ} {j : Fin 2} {p : Fin 5 → ℕ} :
    p ∈ sharpResidualTuples x a n j ↔
      (∀ i, (p i).Prime) ∧ Function.Injective p ∧ (∏ i, p i) = n ∧
      (∀ i k : Fin 5, i < k → (p i : ℝ) * (p k : ℝ) < x ^ a) ∧ sharpResidualOrder j p := by
  classical
  simp only [sharpResidualTuples, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hb, hi, hn, hc, ho⟩
    exact ⟨fun i => Nat.prime_of_mem_primesLE (hb i), hi, hn, hc, ho⟩
  · rintro ⟨hp, hi, hn, hc, ho⟩
    refine ⟨?_, hi, hn, hc, ho⟩
    intro i
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, hp i⟩
    have hpos : 0 < n := hn ▸ Finset.prod_pos (fun k _ => (hp k).pos)
    exact Nat.le_of_dvd hpos (hn ▸ Finset.dvd_prod_of_mem p (Finset.mem_univ i))

theorem sharpResidualOrder_orderEmb (f : Fin 5 ↪o ℕ) (j : Fin 2) (σ : Equiv.Perm (Fin 5)) :
    sharpResidualOrder j (fun i => f (σ i)) ↔ sharpResidualOrder j σ := by
  simp only [sharpResidualOrder, OrderEmbedding.lt_iff_lt]

theorem sharpResidualTuples_card_of_exceptional {x a : ℝ} {n : ℕ}
    (hex : SharpExceptional x a n) (j : Fin 2) :
    (sharpResidualTuples x a n j).card = if j = 0 then 4 else 20 := by
  classical
  obtain ⟨p, hi, hp, hn, hc⟩ := hex
  have hsq : Squarefree n := hn ▸ distinct_prime_product_squarefree hi hp
  obtain ⟨f, hf, hfn, _, hmodel⟩ := squarefree_five_prime_rank_model n hsq p hp hn
  obtain ⟨τ, hτ⟩ := hmodel p hp hn
  have hcf : ∀ i k : Fin 5, i < k → (f i : ℝ) * (f k : ℝ) < x ^ a := by
    have hr := sharp_pairs_reindex hc τ.symm
    simpa only [hτ, Equiv.apply_symm_apply] using hr
  have heq : sharpResidualTuples x a n j =
      (sharpResidualPerms j).image (fun σ i => f (σ i)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvp, _, hvn, _, hvo⟩ := sharpResidualTuples_mem.mp hv
      obtain ⟨σ, rfl⟩ := hmodel v hvp hvn
      refine Finset.mem_image.mpr ⟨σ, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨by simp [mem_perms_of_finset_iff],
        (sharpResidualOrder_orderEmb f j σ).mp hvo⟩
    · intro hv
      obtain ⟨σ, hs, rfl⟩ := Finset.mem_image.mp hv
      apply sharpResidualTuples_mem.mpr
      refine ⟨fun i => hf (σ i), f.injective.comp σ.injective, ?_, sharp_pairs_reindex hcf σ, ?_⟩
      · exact (Equiv.prod_comp σ (fun i => f i)).trans hfn
      · exact (sharpResidualOrder_orderEmb f j σ).mpr (Finset.mem_filter.mp hs).2
  rw [heq, Finset.card_image_of_injective]
  · exact sharpResidualPerms_card j
  · intro σ τ he
    apply Equiv.ext
    intro i
    exact f.injective (congrFun he i)

open Classical in
theorem sharpResidualTuples_card (x a : ℝ) (n : ℕ) (j : Fin 2) :
    (sharpResidualTuples x a n j).card =
      if SharpExceptional x a n then (if j = 0 then 4 else 20) else 0 := by
  classical
  by_cases hex : SharpExceptional x a n
  · rw [ite_eq_left hex]
    exact sharpResidualTuples_card_of_exceptional hex j
  · rw [ite_eq_right hex, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpr, hi, hn, hc, _⟩ := sharpResidualTuples_mem.mp hp
    exact hex ⟨p, hi, hpr, hn, hc⟩

theorem sharpDefect_eq_residual_counts (x a : ℝ) (n : ℕ) :
    sharpDefect x a n =
      (sharpResidualTuples x a n 0).card + (sharpResidualTuples x a n 1).card := by
  classical
  simp only [sharpResidualTuples_card, sharpDefect]
  split_ifs <;> norm_num at *

theorem sharpDefect_eq_six_first_count (x a : ℝ) (n : ℕ) :
    sharpDefect x a n = 6 * (sharpResidualTuples x a n 0).card := by
  classical
  simp only [sharpResidualTuples_card, sharpDefect]
  split_ifs <;> norm_num at *

#print axioms sharpResidualPerms_card
#print axioms sharpExceptional_squarefree
#print axioms sharpResidualTuples_card
#print axioms sharpDefect_eq_residual_counts
#print axioms sharpDefect_eq_six_first_count

end PrimeGap182Analytic
