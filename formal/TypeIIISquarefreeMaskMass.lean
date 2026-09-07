import TypeIIILocalRectangles
import TypeIIICompletionArithmetic

/-!
# Squarefree exceptional-set averaging with explicit constants

The product of the actual local exceptional envelopes is averaged against the two interval
Fourier weights.  The modulus factors are pairwise coprime, and the exceptional factor is
the product of those with repeated row or column residues.  No Fourier or averaging bound
is assumed in this file.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι]

theorem localExceptionalEnvelope_nonneg {s D : ℕ} [NeZero s]
    (E : LocalMaskData s D) (h k : ZMod s) : 0 ≤ localExceptionalEnvelope E h k := by
  unfold localExceptionalEnvelope
  split_ifs <;> positivity

/-- The actual product of the repeated-index modulus factors. -/
def repeatedFactor (q : ι → ℕ) [∀ i, NeZero (q i)] {D : ℕ}
    (E : ∀ i, LocalMaskData (q i) D) : ℕ :=
  ∏ i, if (E i).repeated then q i else 1

/-- The explicit finite combinatorial loss from at most five choices per factor and the
two local cardinality bounds. -/
def maskComplexity (D n : ℕ) : ℝ := (5 * ((max D 1 : ℕ) : ℝ) ^ 2) ^ n

theorem squarefree_exceptional_mask_mass
    (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (D : ℕ)
    (E : ∀ i, LocalMaskData (q i) D) (Ah Ak : ℤ) (Nh Nk : ℕ) :
    (∏ i, q i : ℕ) *
      (∑ h : ZMod (∏ i, q i), ∑ k : ZMod (∏ i, q i),
        (∏ i, localExceptionalEnvelope (E i) (h.val : ZMod (q i)) (k.val : ZMod (q i))) *
          ‖intervalFourier (∏ i, q i) Ah Nh h‖ * ‖intervalFourier (∏ i, q i) Ak Nk k‖) ≤
      maskComplexity D (Fintype.card ι) *
        squarefreeCompletionShape (∏ i, q i) (repeatedFactor q E) Nh Nk := by
  classical
  let s := ∏ i, q i
  let N : ℝ := (max D 1 : ℕ)
  let qh (i : ι) (t : MaskKind) := maskFirstMod (q i) t
  let qk (i : ι) (t : MaskKind) := maskSecondMod (q i) t
  let Rh (i : ι) (t : MaskKind) := maskFirstResidues (E i) t
  let Rk (i : ι) (t : MaskKind) (h : ZMod s) :=
    maskSecondResidues (E i) t (h.val : ZMod (q i))
  let c (i : ι) (t : MaskKind) := maskWeight (q i) (E i).repeated t
  let R (h k : ZMod s) := ∏ i, ∑ t : MaskKind, c i t *
    if (h.val : ZMod (qh i t)) ∈ Rh i t ∧ (k.val : ZMod (qk i t)) ∈ Rk i t h then 1 else 0
  have hc (i : ι) (t : MaskKind) : 0 ≤ c i t := maskWeight_nonneg _ _ _
  have hch (e : ι → MaskKind) : Pairwise (fun i j => (qh i (e i)).Coprime (qh j (e j))) := by
    intro i j hij
    exact Nat.Coprime.of_dvd (maskFirstMod_dvd _ _) (maskFirstMod_dvd _ _) (hcp hij)
  have hck (e : ι → MaskKind) : Pairwise (fun i j => (qk i (e i)).Coprime (qk j (e j))) := by
    intro i j hij
    exact Nat.Coprime.of_dvd (maskSecondMod_dvd _ _) (maskSecondMod_dvd _ _) (hcp hij)
  have hph (e : ι → MaskKind) : (∏ i, qh i (e i)) ∣ s :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => maskFirstMod_dvd _ _)
  have hpk (e : ι → MaskKind) : (∏ i, qk i (e i)) ∣ s :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => maskSecondMod_dvd _ _)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hlocal (h k : ZMod s) :
      (∏ i, localExceptionalEnvelope (E i) (h.val : ZMod (q i)) (k.val : ZMod (q i))) ≤ R h k := by
    apply Finset.prod_le_prod
    · intro i hi
      exact localExceptionalEnvelope_nonneg _ _ _
    · intro i hi
      have hh := localExceptionalEnvelope_le_rectangles (E i)
        (h.val : ZMod (q i)) (k.val : ZMod (q i))
      simpa only [residue_of_residue (q i) _ h.val (maskFirstMod_dvd (q i) _),
        residue_of_residue (q i) _ k.val (maskSecondMod_dvd (q i) _), c, qh, qk, Rh, Rk] using hh
  have hmass := product_rectangle_envelope_mass s qh qk hch hck hph hpk Rh Rk
    (fun _ _ => max D 1) (fun i t h => maskSecondResidues_card (E i) t _)
    c hc Ah Ak Nh Nk
  have hterm (e : ι → MaskKind) :
      (s : ℝ) * (∏ i, c i (e i)) * (∏ i, ((Rh i (e i)).card : ℝ)) *
        (∏ _i : ι, ((max D 1 : ℕ) : ℝ)) * intervalMassBound s (∏ i, qh i (e i)) Nh *
          intervalMassBound s (∏ i, qk i (e i)) Nk ≤
      N ^ (2 * Fintype.card ι) * squarefreeCompletionShape s (repeatedFactor q E) Nh Nk := by
    have : NeZero (∏ i, qh i (e i)) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne _)⟩
    have : NeZero (∏ i, qk i (e i)) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne _)⟩
    have hW : 0 ≤ ∏ i, c i (e i) := Finset.prod_nonneg (fun i _ => hc i (e i))
    have hw := product_completion_weight_bounds (fun i => (q i : ℝ))
      (fun i => ((if (E i).repeated then q i else 1 : ℕ) : ℝ))
      (fun i => (qh i (e i) : ℝ)) (fun i => (qk i (e i) : ℝ)) (fun i => c i (e i))
      (fun i => hc i (e i)) (fun i => maskWeight_bounds (q i) (E i).repeated (e i))
    simp only [← Nat.cast_prod] at hw
    have hscalar := intervalMass_completed_scalar_bound s (∏ i, qh i (e i))
      (∏ i, qk i (e i)) (repeatedFactor q E) (∏ i, c i (e i))
      (Nat.cast_nonneg _) hW Nh Nk hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
    have hcards : (∏ i, ((Rh i (e i)).card : ℝ)) ≤ N ^ Fintype.card ι := by
      calc
        _ ≤ ∏ _i : ι, N := by
          apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          intro i hi
          change ((maskFirstResidues (E i) (e i)).card : ℝ) ≤ ((max D 1 : ℕ) : ℝ)
          exact_mod_cast maskFirstResidues_card (E i) (e i)
        _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
    have hcards0 : 0 ≤ (∏ i, ((Rh i (e i)).card : ℝ)) :=
      Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hfirst : 0 ≤ (s : ℝ) * (∏ i, c i (e i)) *
        intervalMassBound s (∏ i, qh i (e i)) Nh *
          intervalMassBound s (∏ i, qk i (e i)) Nk := by
      have hh := intervalMassBound_nonneg s (∏ i, qh i (e i)) Nh
      have hk := intervalMassBound_nonneg s (∏ i, qk i (e i)) Nk
      positivity
    have hc2 : (∏ i, ((Rh i (e i)).card : ℝ)) * (∏ _i : ι, ((max D 1 : ℕ) : ℝ)) ≤
        N ^ (2 * Fintype.card ι) := by
      simp only [Finset.prod_const, Finset.card_univ]
      calc
        _ ≤ N ^ Fintype.card ι * N ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_right hcards (pow_nonneg hN _)
        _ = _ := by rw [← pow_add]; congr 1; omega
    calc
      _ = ((s : ℝ) * (∏ i, c i (e i)) * intervalMassBound s (∏ i, qh i (e i)) Nh *
          intervalMassBound s (∏ i, qk i (e i)) Nk) *
          ((∏ i, ((Rh i (e i)).card : ℝ)) * (∏ _i : ι, ((max D 1 : ℕ) : ℝ))) := by ring
      _ ≤ ((s : ℝ) * (∏ i, c i (e i)) * intervalMassBound s (∏ i, qh i (e i)) Nh *
          intervalMassBound s (∏ i, qk i (e i)) Nk) * N ^ (2 * Fintype.card ι) :=
        mul_le_mul_of_nonneg_left hc2 hfirst
      _ ≤ squarefreeCompletionShape s (repeatedFactor q E) Nh Nk * N ^ (2 * Fintype.card ι) :=
        mul_le_mul_of_nonneg_right hscalar (pow_nonneg hN _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ (s : ℝ) * (∑ h : ZMod s, ∑ k : ZMod s,
        R h k * ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hlocal h k) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (s : ℝ) * ∑ e : ι → MaskKind,
        (∏ i, c i (e i)) * (∏ i, ((Rh i (e i)).card : ℝ)) *
          (∏ _i : ι, ((max D 1 : ℕ) : ℝ)) * intervalMassBound s (∏ i, qh i (e i)) Nh *
            intervalMassBound s (∏ i, qk i (e i)) Nk :=
      mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _)
    _ ≤ ∑ _e : ι → MaskKind,
        N ^ (2 * Fintype.card ι) * squarefreeCompletionShape s (repeatedFactor q E) Nh Nk := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      simpa only [mul_assoc] using hterm e
    _ = _ := by
      have hcard : Fintype.card MaskKind = 5 := by decide
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, hcard,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, maskComplexity, mul_pow, pow_mul]
      dsimp only [N, s]
      simp only [Nat.cast_prod]
      ring

#print axioms localExceptionalEnvelope_nonneg
#print axioms squarefree_exceptional_mask_mass

end

end PrimeGap182.TypeIII
