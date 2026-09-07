import TypeIIICRTCounting

/-!
# Positive finite expansion of local exceptional masks

Every mask is an actual pair of residue restrictions.  The allowed second-coordinate
residues may depend on the entire first frequency.  The theorem expands the product of
local envelopes and applies the proved CRT/coset estimate separately to each positive
summand.  It does not enlarge a signed four-cycle sum.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The weighted mass of simultaneous local residue restrictions. -/
theorem weighted_local_rectangle_mass
    (s : ℕ) [NeZero s] (qh qk : ι → ℕ)
    [NeZero (∏ i, qh i)] [NeZero (∏ i, qk i)]
    (hch : Pairwise (fun i j => (qh i).Coprime (qh j)))
    (hck : Pairwise (fun i j => (qk i).Coprime (qk j)))
    (hph : (∏ i, qh i) ∣ s) (hpk : (∏ i, qk i) ∣ s)
    (Rh : ∀ i, Finset (ZMod (qh i)))
    (Rk : ZMod s → ∀ i, Finset (ZMod (qk i))) (Dk : ι → ℕ)
    (hDk : ∀ h i, (Rk h i).card ≤ Dk i) (Ah Ak : ℤ) (Nh Nk : ℕ) :
    (∑ h : ZMod s, ∑ k : ZMod s,
      if ∀ i, (h.val : ZMod (qh i)) ∈ Rh i ∧ (k.val : ZMod (qk i)) ∈ Rk h i then
        ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ else 0) ≤
      (∏ i, ((Rh i).card : ℝ)) * (∏ i, (Dk i : ℝ)) *
        intervalMassBound s (∏ i, qh i) Nh * intervalMassBound s (∏ i, qk i) Nk := by
  classical
  have heq :
      (∑ h : ZMod s, ∑ k : ZMod s,
        if ∀ i, (h.val : ZMod (qh i)) ∈ Rh i ∧ (k.val : ZMod (qk i)) ∈ Rk h i then
          ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ else 0) =
      ∑ h ∈ residueSet s (∏ i, qh i) (crtAllowedResidues qh Rh),
        ∑ k ∈ residueSet s (∏ i, qk i) (crtAllowedResidues qk (Rk h)),
          ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ := by
    have hseth : residueSet s (∏ i, qh i) (crtAllowedResidues qh Rh) =
        Finset.univ.filter (fun h : ZMod s => ∀ i, (h.val : ZMod (qh i)) ∈ Rh i) := by
      ext h
      simp only [mem_residueSet_crtAllowedResidues, Finset.mem_filter, Finset.mem_univ,
        true_and]
    have hsetk (h : ZMod s) : residueSet s (∏ i, qk i) (crtAllowedResidues qk (Rk h)) =
        Finset.univ.filter (fun k : ZMod s => ∀ i, (k.val : ZMod (qk i)) ∈ Rk h i) := by
      ext k
      simp only [mem_residueSet_crtAllowedResidues, Finset.mem_filter, Finset.mem_univ,
        true_and]
    rw [hseth]
    simp_rw [hsetk]
    simp only [Finset.sum_filter, forall_and]
    apply Finset.sum_congr rfl
    intro h hh
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [heq]
  exact dependent_crt_rectangle_mass s qh qk hch hck hph hpk Rh Rk Dk hDk Ah Ak Nh Nk

/-- Exact expansion of a product of positive local rectangle envelopes. -/
theorem prod_sum_rectangle_expansion
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (c : ∀ i, κ i → ℝ) (P : ∀ i, κ i → Prop) :
    (∏ i, ∑ t : κ i, c i t * if P i t then 1 else 0) =
      ∑ e : ∀ i, κ i, (∏ i, c i (e i)) * if ∀ i, P i (e i) then 1 else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.prod_mul_distrib, Fintype.prod_boole]

/-- The full finite product of local masks has the explicit sum of CRT/coset bounds.
All coefficient signs and local cardinal bounds are checked before the sums are reordered. -/
theorem product_rectangle_envelope_mass
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (s : ℕ) [NeZero s] (qh qk : ∀ i, κ i → ℕ)
    [∀ i t, NeZero (qh i t)] [∀ i t, NeZero (qk i t)]
    (hch : ∀ e : ∀ i, κ i, Pairwise (fun i j => (qh i (e i)).Coprime (qh j (e j))))
    (hck : ∀ e : ∀ i, κ i, Pairwise (fun i j => (qk i (e i)).Coprime (qk j (e j))))
    (hph : ∀ e : ∀ i, κ i, (∏ i, qh i (e i)) ∣ s)
    (hpk : ∀ e : ∀ i, κ i, (∏ i, qk i (e i)) ∣ s)
    (Rh : ∀ i t, Finset (ZMod (qh i t)))
    (Rk : ∀ i t, ZMod s → Finset (ZMod (qk i t))) (Dk : ∀ i, κ i → ℕ)
    (hDk : ∀ i t h, (Rk i t h).card ≤ Dk i t)
    (c : ∀ i, κ i → ℝ) (hc : ∀ i t, 0 ≤ c i t)
    (Ah Ak : ℤ) (Nh Nk : ℕ) :
    (∑ h : ZMod s, ∑ k : ZMod s,
      (∏ i, ∑ t : κ i, c i t *
        if (h.val : ZMod (qh i t)) ∈ Rh i t ∧ (k.val : ZMod (qk i t)) ∈ Rk i t h
          then 1 else 0) *
        ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) ≤
      ∑ e : ∀ i, κ i,
        (∏ i, c i (e i)) * (∏ i, ((Rh i (e i)).card : ℝ)) *
          (∏ i, (Dk i (e i) : ℝ)) *
            intervalMassBound s (∏ i, qh i (e i)) Nh *
              intervalMassBound s (∏ i, qk i (e i)) Nk := by
  classical
  let P (h k : ZMod s) (i : ι) (t : κ i) :=
    (h.val : ZMod (qh i t)) ∈ Rh i t ∧ (k.val : ZMod (qk i t)) ∈ Rk i t h
  let w (h k : ZMod s) := ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖
  have hterm (h k : ZMod s) :
      (∏ i, ∑ t : κ i, c i t * if P h k i t then 1 else 0) *
        ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ =
      ∑ e : ∀ i, κ i, (∏ i, c i (e i)) * if ∀ i, P h k i (e i) then w h k else 0 := by
    rw [Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [Fintype.prod_boole]
    by_cases hp : ∀ i, P h k i (e i)
    · simp only [ite_eq_left hp, mul_one, w, mul_assoc]
    · simp only [ite_eq_right hp, mul_zero, zero_mul]
  calc
    _ = ∑ h : ZMod s, ∑ k : ZMod s, ∑ e : ∀ i, κ i,
        (∏ i, c i (e i)) * if ∀ i, P h k i (e i) then w h k else 0 := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm h k
    _ = ∑ h : ZMod s, ∑ e : ∀ i, κ i, ∑ k : ZMod s,
        (∏ i, c i (e i)) * if ∀ i, P h k i (e i) then w h k else 0 := by
      apply Finset.sum_congr rfl
      intro h hh
      exact Finset.sum_comm
    _ = ∑ e : ∀ i, κ i, ∑ h : ZMod s, ∑ k : ZMod s,
        (∏ i, c i (e i)) * if ∀ i, P h k i (e i) then w h k else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      have : NeZero (∏ i, qh i (e i)) := ⟨Finset.prod_ne_zero_iff.mpr
        (fun i _ => NeZero.ne _)⟩
      have : NeZero (∏ i, qk i (e i)) := ⟨Finset.prod_ne_zero_iff.mpr
        (fun i _ => NeZero.ne _)⟩
      have hbound := weighted_local_rectangle_mass s (fun i => qh i (e i))
        (fun i => qk i (e i)) (hch e) (hck e) (hph e) (hpk e)
        (fun i => Rh i (e i)) (fun h i => Rk i (e i) h) (fun i => Dk i (e i))
        (fun h i => hDk i (e i) h) Ah Ak Nh Nk
      have hcprod : 0 ≤ ∏ i, c i (e i) := Finset.prod_nonneg (fun i _ => hc i (e i))
      simp only [← Finset.mul_sum]
      simpa only [P, w, mul_assoc] using mul_le_mul_of_nonneg_left hbound hcprod

#print axioms weighted_local_rectangle_mass
#print axioms prod_sum_rectangle_expansion
#print axioms product_rectangle_envelope_mass

end

end PrimeGap182.TypeIII
