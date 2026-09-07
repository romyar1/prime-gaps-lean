import IncidenceSchwartzSummability

/-!
# Actual two-dimensional Poisson summation under an arbitrary real shear

Both exchanges of sums are justified by Schwartz decay. The shear is a real
number, and no rationality or relation to the lattice is assumed.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators SchwartzMap FourierTransform

def incidenceShearedPhysical (u v : 𝓢(ℝ, ℂ)) (τ α β : ℝ) (z : ℤ × ℤ) : ℂ :=
  u (z.1 : ℝ) * v ((z.2 : ℝ) - τ * (z.1 : ℝ)) *
    incidenceRealChar (-α * (z.1 : ℝ) - β * (z.2 : ℝ))

def incidenceShearedFourier (u v : 𝓢(ℝ, ℂ)) (τ α β : ℝ) (z : ℤ × ℤ) : ℂ :=
  𝓕 u ((z.1 : ℝ) + α + τ * ((z.2 : ℝ) + β)) * 𝓕 v ((z.2 : ℝ) + β)

theorem incidenceShearedPhysical_summable (u v : 𝓢(ℝ, ℂ)) (τ α β : ℝ) :
    Summable (incidenceShearedPhysical u v τ α β) := by
  have hs := incidenceSchwartz_shearedProduct_phase_summable v u (-τ) 0 0
    (fun z => -α * (z.2 : ℝ) - β * (z.1 : ℝ))
  have hswap : Summable (fun z : ℤ × ℤ =>
      incidenceShearedPhysical u v τ α β (z.2, z.1)) := by
    apply hs.congr
    intro z
    simp only [add_zero, neg_mul, ← sub_eq_add_neg, incidenceShearedPhysical]
    ring
  exact (Equiv.prodComm ℤ ℤ).summable_iff.mp hswap

theorem incidenceShearedFourier_summable (u v : 𝓢(ℝ, ℂ)) (τ α β : ℝ) :
    Summable (incidenceShearedFourier u v τ α β) :=
  (incidenceSchwartz_shearedProduct_norm_summable (𝓕 u) (𝓕 v) τ α β).of_norm

private theorem incidencePoisson_vertical (v : 𝓢(ℝ, ℂ)) (τ β : ℝ) (e : ℤ) :
    (∑' γ : ℤ, v ((γ : ℝ) - τ * (e : ℝ)) * incidenceRealChar (-β * (γ : ℝ))) =
      ∑' ν : ℤ, 𝓕 v ((ν : ℝ) + β) *
        incidenceRealChar (-(τ * ((ν : ℝ) + β)) * (e : ℝ)) := by
  have hp := (incidencePoisson_translated v β (-τ * (e : ℝ))).tsum_eq.symm
  convert hp using 1 <;> apply tsum_congr <;> intro k
  · congr 2
    ring
  · congr 2
    ring

private theorem incidencePoisson_horizontal (u : 𝓢(ℝ, ℂ)) (θ : ℝ) :
    (∑' e : ℤ, u (e : ℝ) * incidenceRealChar (-θ * (e : ℝ))) =
      ∑' h : ℤ, 𝓕 u ((h : ℝ) + θ) := by
  have hp := (incidencePoisson_modulated u θ 0).tsum_eq.symm
  simpa only [add_zero, zero_add, mul_zero, incidenceRealChar_zero, mul_one,
    one_mul, mul_comm] using hp

set_option maxHeartbeats 800000 in
/-- The full lattice identity, including all zero and partially zero modes. -/
theorem incidencePoisson_sheared (u v : 𝓢(ℝ, ℂ)) (τ α β : ℝ) :
    (∑' z : ℤ × ℤ, incidenceShearedPhysical u v τ α β z) =
      ∑' z : ℤ × ℤ, incidenceShearedFourier u v τ α β z := by
  let mid (z : ℤ × ℤ) : ℂ := u (z.1 : ℝ) * 𝓕 v ((z.2 : ℝ) + β) *
    incidenceRealChar (-(α + τ * ((z.2 : ℝ) + β)) * (z.1 : ℝ))
  have hmid : Summable mid := by
    simpa only [mid, add_zero, zero_mul] using
      incidenceSchwartz_shearedProduct_phase_summable u (𝓕 v) 0 0 β
        (fun z => -(α + τ * ((z.2 : ℝ) + β)) * (z.1 : ℝ))
  have hvertical (e : ℤ) :
      (∑' γ : ℤ, incidenceShearedPhysical u v τ α β (e, γ)) =
        ∑' ν : ℤ, mid (e, ν) := by
    calc
      _ = (u (e : ℝ) * incidenceRealChar (-α * (e : ℝ))) *
          ∑' γ : ℤ, v ((γ : ℝ) - τ * (e : ℝ)) * incidenceRealChar (-β * (γ : ℝ)) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro γ
        unfold incidenceShearedPhysical
        rw [show -α * (e : ℝ) - β * (γ : ℝ) =
          -α * (e : ℝ) + -β * (γ : ℝ) by ring, incidenceRealChar_add]
        ring
      _ = (u (e : ℝ) * incidenceRealChar (-α * (e : ℝ))) *
          ∑' ν : ℤ, 𝓕 v ((ν : ℝ) + β) *
            incidenceRealChar (-(τ * ((ν : ℝ) + β)) * (e : ℝ)) := by
        rw [incidencePoisson_vertical]
      _ = _ := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro ν
        dsimp [mid]
        calc
          _ = u (e : ℝ) * 𝓕 v ((ν : ℝ) + β) *
              (incidenceRealChar (-α * (e : ℝ)) *
                incidenceRealChar (-(τ * ((ν : ℝ) + β)) * (e : ℝ))) := by ring
          _ = _ := by rw [← incidenceRealChar_add]; congr 2; ring
  have hhorizontal (ν : ℤ) :
      (∑' e : ℤ, mid (e, ν)) =
        ∑' h : ℤ, incidenceShearedFourier u v τ α β (h, ν) := by
    calc
      _ = (∑' e : ℤ, u (e : ℝ) *
          incidenceRealChar (-(α + τ * ((ν : ℝ) + β)) * (e : ℝ))) *
            𝓕 v ((ν : ℝ) + β) := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro e
        dsimp [mid]
        ring
      _ = (∑' h : ℤ, 𝓕 u ((h : ℝ) + (α + τ * ((ν : ℝ) + β)))) *
          𝓕 v ((ν : ℝ) + β) := by rw [incidencePoisson_horizontal]
      _ = _ := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro h
        simp only [incidenceShearedFourier, add_assoc]
  calc
    _ = ∑' e : ℤ, ∑' γ : ℤ, incidenceShearedPhysical u v τ α β (e, γ) :=
      (incidenceShearedPhysical_summable u v τ α β).tsum_prod
    _ = ∑' e : ℤ, ∑' ν : ℤ, mid (e, ν) := tsum_congr hvertical
    _ = ∑' ν : ℤ, ∑' e : ℤ, mid (e, ν) := hmid.tsum_comm.symm
    _ = ∑' ν : ℤ, ∑' h : ℤ, incidenceShearedFourier u v τ α β (h, ν) :=
      tsum_congr hhorizontal
    _ = _ := (incidenceShearedFourier_summable u v τ α β).prod_symm.tsum_prod.symm.trans
      ((Equiv.prodComm ℤ ℤ).tsum_eq _)

#print axioms incidenceShearedPhysical_summable
#print axioms incidenceShearedFourier_summable
#print axioms incidencePoisson_sheared

end PrimeGap182Audit
