import IncidenceSmoothSourceWindow
import IncidenceUniformProfile

/-!
# Uniform source-window estimate with explicit Fourier cost

The window constant is chosen before the joint Schwartz profile. This
keeps the uniform source-family quantifier explicit; the preceding
module proves that its actual Fourier cost is subpower under the
source derivative envelopes.
-/

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem incidenceSmoothSourceWindow_uniform_bound (hK4 : AllIncidenceRankFourBounds)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : 𝓢(V, ℂ), ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ AQ : ZMod q, IsUnit AQ → ∀ u : (ZMod q)ˣ,
      ∀ d : ℕ, Nat.Coprime d q → ∀ r₀ : ℤ,
      ∀ E₁ E₂ e₀ γ₀ shear L : ℝ, 0 < E₁ → 0 < E₂ → 0 ≤ L →
      ∀ w : ℤ × ℤ → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - shear * (z.1 : ℝ) - γ₀| ≤ E₂) →
      ∀ A : Finset ℤ, ∀ I : ℤ → Finset ℤ, ∀ B : ℤ,
      ∀ U V₀ τ : ℝ, 0 < U → 0 ≤ V₀ → 0 ≤ τ →
      (∀ a ∈ A, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U ∧ IsUnit (a : ZMod q)) →
      (∀ a ∈ A, (a.natAbs.divisors.card : ℝ) ≤ τ) →
      ∀ center : ℤ → ℝ,
      (∀ a ∈ A, ∀ k ∈ I a, |(k : ℝ) - center a| ≤ V₀) →
      ∀ c : ℤ → ℂ, ∀ β : ℤ → ℤ → ℂ,
      (∀ a ∈ A, ∀ k ∈ I a, ‖β a k‖ ≤ 1) →
      ∀ xrow : ℤ × ℤ → V, ∀ yinput : ℤ → ℤ → V,
      (∑' z : ℤ × ℤ, w z * ‖∑ a ∈ A, c a * ∑ k ∈ I a,
        β a k * incidenceMatrixMod AQ
          ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
          ((u : ZMod q) * incidenceFareyResidue q B a k) *
            F (xrow z + yinput a k)‖ ^ 2) ≤
        (1 + (∫ ξ : V, ‖(𝓕 F : 𝓢(V, ℂ)) ξ‖) ^ 2) *
          C * L * incidenceWindowScale η q E₁ E₂ *
          ((1 + 8 * U * V₀ / (q : ℝ)) * ((A.card : ℝ) + 8 * V₀ * τ)) *
            ∑ a ∈ A, ‖c a‖ ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hsource⟩ := incidenceSourceWindow_bound hK4 η hη
  refine ⟨C₀, hC₀, ?_⟩
  intro F q _ hq AQ hAQ u d hd r₀ E₁ E₂ e₀ γ₀ shear L hE₁ hE₂ hL w hw0 hwL hwbox
    A I B U V₀ τ hU hV₀ hτ0 hA hτ center hI c β hβ xrow yinput
  let P : ℝ := (∫ ξ : V, ‖(𝓕 F : 𝓢(V, ℂ)) ξ‖) ^ 2
  let K : ℝ := C₀ * L * incidenceWindowScale η q E₁ E₂ *
    ((1 + 8 * U * V₀ / (q : ℝ)) * ((A.card : ℝ) + 8 * V₀ * τ)) *
      ∑ a ∈ A, ‖c a‖ ^ 2
  have hK : 0 ≤ K := by dsimp only [K, incidenceWindowScale]; positivity
  let kernel : (ℤ × ℤ) → ℤ → ℤ → ℂ := fun z a k =>
    incidenceMatrixMod AQ
      ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
      ((u : ZMod q) * incidenceFareyResidue q B a k)
  let κ := (a : A) × (I a.val)
  let Z : (ℤ × ℤ) → κ → ℂ := fun z p =>
    c p.1.val * β p.1.val p.2.val * kernel z p.1.val p.2.val
  have hsum (z : ℤ × ℤ) (f : ℤ → ℤ → ℂ) :
      (∑ p : κ, Z z p * f p.1.val p.2.val) =
        ∑ a ∈ A, c a * ∑ k ∈ I a, β a k * kernel z a k * f a k := by
    rw [incidenceSourceSigma_sum A I (fun a k => c a * β a k * kernel z a k * f a k)]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (hw0 z) (sq_nonneg _))
  intro S
  let wS : ℤ × ℤ → ℝ := fun z => if z ∈ S then w z else 0
  have hwS0 : ∀ z, 0 ≤ wS z := fun z => by
    dsimp only [wS]
    split_ifs
    · exact hw0 z
    · exact le_refl _
  have hwSL : ∀ z, wS z ≤ L := fun z => by
    dsimp only [wS]
    split_ifs
    · exact hwL z
    · exact hL
  have hwSbox : ∀ z, wS z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
      |(z.2 : ℝ) - shear * (z.1 : ℝ) - γ₀| ≤ E₂ := by
    intro z hz
    apply hwbox z
    intro hwz
    exact hz (by simp [wS, hwz])
  have hresponse (v : κ → ℂ) (hv : ∀ p, ‖v p‖ ≤ 1) :
      (∑ z : S, w z.val * ‖∑ p : κ, Z z.val p * v p‖ ^ 2) ≤ K := by
    let v' : ℤ → ℤ → ℂ := fun a k =>
      if ha : a ∈ A then if hk : k ∈ I a then v ⟨⟨a, ha⟩, ⟨k, hk⟩⟩ else 0 else 0
    have hv' : ∀ a ∈ A, ∀ k ∈ I a, ‖β a k * v' a k‖ ≤ 1 := by
      intro a ha k hk
      rw [norm_mul]
      exact (mul_le_mul (hβ a ha k hk) (by simpa [v', ha, hk] using hv ⟨⟨a, ha⟩, ⟨k, hk⟩⟩)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hb := hsource q hq AQ hAQ u d hd r₀ E₁ E₂ e₀ γ₀ shear L hE₁ hE₂ hL
      wS hwS0 hwSL hwSbox A I B U V₀ τ hU hV₀ hA hτ center hI c
        (fun a k => β a k * v' a k) hv'
    have hresp (z : ℤ × ℤ) : (∑ p : κ, Z z p * v p) =
        incidenceSourceResponse AQ u d r₀ A I B c (fun a k => β a k * v' a k) z := by
      have hs : (∑ p : κ, Z z p * v p) = ∑ p : κ, Z z p * v' p.1.val p.2.val := by
        apply Finset.sum_congr rfl
        intro p _
        rcases p with ⟨⟨a, ha⟩, ⟨k, hk⟩⟩
        simp only [v', ha, hk, dite_eq_left]
      rw [hs, hsum z v']
      unfold incidenceSourceResponse
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [kernel]
      ring
    have ht : (∑' z, wS z *
        ‖incidenceSourceResponse AQ u d r₀ A I B c (fun a k => β a k * v' a k) z‖ ^ 2) =
        ∑ z ∈ S, w z *
          ‖incidenceSourceResponse AQ u d r₀ A I B c (fun a k => β a k * v' a k) z‖ ^ 2 := by
      rw [tsum_eq_sum (s := S) (fun z hz => by simp [wS, hz])]
      exact Finset.sum_congr rfl (fun z hz => by simp only [wS, ite_eq_left hz])
    rw [ht] at hb
    simp only [hresp]
    rw [Finset.sum_coe_sort S (fun z => w z *
      ‖incidenceSourceResponse AQ u d r₀ A I B c (fun a k => β a k * v' a k) z‖ ^ 2)]
    exact hb
  have hsep := incidenceSchwartz_weighted_separation (fun z : S => w z.val)
    (fun z => hw0 z.val) (fun z : S => Z z.val) (fun z : S => xrow z.val)
    (fun p : κ => yinput p.1.val p.2.val) F K hK hresponse
  have hsmooth (z : ℤ × ℤ) := hsum z (fun a k => F (xrow z + yinput a k))
  simp only [hsmooth] at hsep
  rw [Finset.sum_coe_sort S (fun z => w z *
    ‖∑ a ∈ A, c a * ∑ k ∈ I a, β a k * kernel z a k * F (xrow z + yinput a k)‖ ^ 2)] at hsep
  apply hsep.trans
  change P * K ≤ _
  have hPK : P * K ≤ (1 + P) * K := by nlinarith only [hK]
  apply hPK.trans_eq
  dsimp only [K]
  ring


#print axioms incidenceSmoothSourceWindow_uniform_bound

end PrimeGap182Audit
