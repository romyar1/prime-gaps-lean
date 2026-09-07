import MarkedBin182

/-!
# Mixed auxiliary sums and disjoint radial profiles

These exact finite identities keep every arithmetic cross term. Four square
limits give the mixed auxiliary limit by polarization. Only after that limit
may disjoint physical profiles force the mixed term to vanish. The final
finite-family theorem reconstructs the square of the full signed sum.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace PrimeGap182Analytic

def normalizedProductSquare {ι : Type*} (s : Finset ι)
    (w L C : ι → ℝ) (N : ℝ) : ℝ :=
  N * ∑ n ∈ s, w n * (L n * C n) ^ 2

def normalizedProductCross {ι : Type*} (s : Finset ι)
    (w L1 L2 C1 C2 : ι → ℝ) (N : ℝ) : ℝ :=
  N * ∑ n ∈ s, w n * L1 n * L2 n * C1 n * C2 n

theorem mixed_auxiliary_polarization {ι : Type*} (s : Finset ι)
    (w L1 L2 C1 C2 : ι → ℝ) (N : ℝ) :
    normalizedProductCross s w L1 L2 C1 C2 N =
      (normalizedProductSquare s w (L1 + L2) (C1 + C2) N -
       normalizedProductSquare s w (L1 - L2) (C1 + C2) N -
       normalizedProductSquare s w (L1 + L2) (C1 - C2) N +
       normalizedProductSquare s w (L1 - L2) (C1 - C2) N) / 16 := by
  unfold normalizedProductCross normalizedProductSquare
  have hpoint (n : ι) :
      16 * (w n * L1 n * L2 n * C1 n * C2 n) =
        w n * ((L1 + L2) n * (C1 + C2) n) ^ 2 -
        w n * ((L1 - L2) n * (C1 + C2) n) ^ 2 -
        w n * ((L1 + L2) n * (C1 - C2) n) ^ 2 +
        w n * ((L1 - L2) n * (C1 - C2) n) ^ 2 := by
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hsum := Finset.sum_congr rfl (fun n (_ : n ∈ s) => hpoint n)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  nlinarith only [congrArg (fun v : ℝ => N * v) hsum]

theorem mixed_auxiliary_tendsto_of_four_squares
    {ι β : Type*} (f : Filter β) (s : β → Finset ι)
    (w L1 L2 C1 C2 : β → ι → ℝ) (N : β → ℝ)
    (Uplus Uminus Vplus Vminus : ℝ)
    (hpp : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x + L2 x) (C1 x + C2 x) (N x)) f (nhds (Uplus * Vplus)))
    (hmp : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x - L2 x) (C1 x + C2 x) (N x)) f (nhds (Uminus * Vplus)))
    (hpm : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x + L2 x) (C1 x - C2 x) (N x)) f (nhds (Uplus * Vminus)))
    (hmm : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x - L2 x) (C1 x - C2 x) (N x)) f (nhds (Uminus * Vminus))) :
    Tendsto (fun x => normalizedProductCross (s x) (w x)
      (L1 x) (L2 x) (C1 x) (C2 x) (N x)) f
      (nhds ((Uplus - Uminus) * (Vplus - Vminus) / 16)) := by
  have h := (((hpp.sub hmp).sub hpm).add hmm).div_const 16
  convert h using 1
  · funext x
    exact mixed_auxiliary_polarization (s x) (w x) (L1 x) (L2 x) (C1 x) (C2 x) (N x)
  · congr 1
    ring

/-- Equal plus/minus profile norms are exactly what orthogonality supplies.
The auxiliary sums may be different and need not be orthogonal themselves. -/
theorem mixed_auxiliary_tendsto_zero_of_orthogonal_profiles
    {ι β : Type*} (f : Filter β) (s : β → Finset ι)
    (w L1 L2 C1 C2 : β → ι → ℝ) (N : β → ℝ)
    (Uplus Uminus V : ℝ)
    (hpp : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x + L2 x) (C1 x + C2 x) (N x)) f (nhds (Uplus * V)))
    (hmp : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x - L2 x) (C1 x + C2 x) (N x)) f (nhds (Uminus * V)))
    (hpm : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x + L2 x) (C1 x - C2 x) (N x)) f (nhds (Uplus * V)))
    (hmm : Tendsto (fun x => normalizedProductSquare (s x) (w x)
      (L1 x - L2 x) (C1 x - C2 x) (N x)) f (nhds (Uminus * V))) :
    Tendsto (fun x => normalizedProductCross (s x) (w x)
      (L1 x) (L2 x) (C1 x) (C2 x) (N x)) f (nhds 0) := by
  simpa only [sub_self, mul_zero, zero_div] using
    mixed_auxiliary_tendsto_of_four_squares f s w L1 L2 C1 C2 N
      Uplus Uminus V V hpp hmp hpm hmm

theorem finite_auxiliary_square_expansion {ι κ : Type*}
    (s : Finset ι) (J : Finset κ) (w : ι → ℝ) (L C : κ → ι → ℝ) (N : ℝ) :
    (N * ∑ n ∈ s, w n * (∑ j ∈ J, L j n * C j n) ^ 2) =
      ∑ j ∈ J, ∑ k ∈ J,
        normalizedProductCross s w (L j) (L k) (C j) (C k) N := by
  have hpoint (n : ι) :
      w n * (∑ j ∈ J, L j n * C j n) ^ 2 =
        ∑ j ∈ J, ∑ k ∈ J, w n * L j n * L k n * C j n * C k n := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hpoint]
  rw [Finset.sum_comm (s := s) (t := J)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm (s := s) (t := J), Finset.mul_sum]
  rfl

/-- Reassemble the full square after taking all mixed limits. This theorem
does not estimate the arithmetic square by a sum of diagonal squares. -/
theorem finite_auxiliary_square_tendsto {ι κ β : Type*}
    (f : Filter β) (s : β → Finset ι) (J : Finset κ)
    (w : β → ι → ℝ) (L C : κ → β → ι → ℝ) (N : β → ℝ) (d : κ → ℝ)
    (hdiag : ∀ j ∈ J, Tendsto (fun x => normalizedProductCross (s x) (w x)
      (L j x) (L j x) (C j x) (C j x) (N x)) f (nhds (d j)))
    (hoff : ∀ j ∈ J, ∀ k ∈ J, j ≠ k →
      Tendsto (fun x => normalizedProductCross (s x) (w x)
        (L j x) (L k x) (C j x) (C k x) (N x)) f (nhds 0)) :
    Tendsto (fun x => N x * ∑ n ∈ s x,
      w x n * (∑ j ∈ J, L j x n * C j x n) ^ 2) f (nhds (∑ j ∈ J, d j)) := by
  classical
  have hpair (j : κ) (hj : j ∈ J) (k : κ) (hk : k ∈ J) :
      Tendsto (fun x => normalizedProductCross (s x) (w x)
        (L j x) (L k x) (C j x) (C k x) (N x)) f
        (nhds (if j = k then d j else 0)) := by
    by_cases he : j = k
    · subst k
      simpa using hdiag j hj
    · simpa only [ite_eq_right he] using hoff j hj k hk he
  have h := tendsto_finsetSum J fun j hj => tendsto_finsetSum J fun k hk => hpair j hj k hk
  have hvalue : (∑ j ∈ J, ∑ k ∈ J, if j = k then d j else 0) = ∑ j ∈ J, d j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [hj]
  rw [hvalue] at h
  convert h using 1
  funext x
  exact finite_auxiliary_square_expansion (s x) J (w x) (fun j => L j x) (fun j => C j x) (N x)

#print axioms mixed_auxiliary_polarization
#print axioms mixed_auxiliary_tendsto_of_four_squares
#print axioms mixed_auxiliary_tendsto_zero_of_orthogonal_profiles
#print axioms finite_auxiliary_square_expansion
#print axioms finite_auxiliary_square_tendsto

end PrimeGap182Analytic
