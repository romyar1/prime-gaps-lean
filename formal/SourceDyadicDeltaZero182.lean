import SourceIncidenceDeltaZero182

/-! A uniform dyadic discrepancy estimate for actual coefficient
families, with its elementary interval restriction and gluing laws. -/

noncomputable section
open scoped BigOperators
open PrimeGap186
namespace PrimeGap182Audit

open Classical in
def SourceDyadicDeltaZeroEstimate («ω» δ ε γlo γhi : ℝ) : Prop :=
  ∀ (C cM TM cN TN : ℝ),
    1 ≤ C → 0 < cM → cM ≤ TM → 0 < cN → cN ≤ TN →
    ∀ (dα dβ : ℕ) (Eα Eβ A η : ℝ), 0 < A → 0 < η →
    ∃ X₀ : ℝ, Real.exp 1 ≤ X₀ ∧
      ∀ (x : ℝ), X₀ ≤ x →
      ∀ (M N R Q γ : ℝ),
      0 < M → 0 < N → 0 < R → 0 < Q →
      x / C ≤ M * N → M * N ≤ C * x → N = x ^ γ →
      γlo ≤ γ → γ ≤ γhi →
      N ≤ C * x ^ (δ + 4 * ε) * R →
      R ≤ C * x ^ (-2 * ε) * N →
      x ^ (1 / 2 - ε) ≤ C * R * Q →
      R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
      ∀ (α β : ℕ →₀ ℂ),
      (∀ n ∈ α.support,
        cM * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ TM * M ∧
        ‖α n‖ ≤ C * (n.divisors.card : ℝ) ^ dα * (Real.log x) ^ Eα) →
      (∀ n ∈ β.support,
        cN * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ TN * N ∧
        ‖β n‖ ≤ C * (n.divisors.card : ℝ) ^ dβ * (Real.log x) ^ Eβ) →
      ∀ (S : Finset (ℕ × ℕ)),
      (∀ p ∈ S,
        0 < p.1 ∧ 0 < p.2 ∧ Squarefree (p.1 * p.2) ∧
        Q ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * Q ∧
        R ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), le_max_left (1 : ℝ) (x ^ δ)⟩ 1 p.1) ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), le_max_left (1 : ℝ) (x ^ δ)⟩ 1 p.2) ∧
        (∀ t ∈ p.1.primeFactors,
          Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (t : ℝ))) →
      ∀ (a b₁ b₂ : ℕ),
      (∀ p ∈ S, Nat.Coprime (a * b₁ * b₂) (p.1 * p.2)) →
      (∑ p ∈ S, ‖deltaZero (finiteConvolution α β) p.1 p.2 a b₁ b₂‖) ≤
        η * (M * N) * (Real.log x) ^ (-A)

theorem SourceDyadicDeltaZeroEstimate.mono_range
    {«ω» δ ε γlo γhi γlo' γhi' : ℝ}
    (h : SourceDyadicDeltaZeroEstimate «ω» δ ε γlo γhi)
    (hlo : γlo ≤ γlo') (hhi : γhi' ≤ γhi) :
    SourceDyadicDeltaZeroEstimate «ω» δ ε γlo' γhi' := by
  intro C cM TM cN TN hC hcM hMT hcN hNT dα dβ Eα Eβ A η hA hη
  obtain ⟨X, hX, hb⟩ := h C cM TM cN TN hC hcM hMT hcN hNT dα dβ Eα Eβ A η hA hη
  refine ⟨X, hX, ?_⟩
  intro x hx M N R Q γ hM hN hR hQ hMNlo hMNhi hNγ hγlo hγhi
  exact hb x hx M N R Q γ hM hN hR hQ hMNlo hMNhi hNγ
    (hlo.trans hγlo) (hγhi.trans hhi)

theorem SourceDyadicDeltaZeroEstimate.join
    {«ω» δ ε γlo γmid γhi : ℝ}
    (hlo : SourceDyadicDeltaZeroEstimate «ω» δ ε γlo γmid)
    (hhi : SourceDyadicDeltaZeroEstimate «ω» δ ε γmid γhi) :
    SourceDyadicDeltaZeroEstimate «ω» δ ε γlo γhi := by
  intro C cM TM cN TN hC hcM hMT hcN hNT dα dβ Eα Eβ A η hA hη
  obtain ⟨XL, hXL, hl⟩ := hlo C cM TM cN TN hC hcM hMT hcN hNT dα dβ Eα Eβ A η hA hη
  obtain ⟨XH, _hXH, hh⟩ := hhi C cM TM cN TN hC hcM hMT hcN hNT dα dβ Eα Eβ A η hA hη
  refine ⟨max XL XH, hXL.trans (le_max_left _ _), ?_⟩
  intro x hx M N R Q γ hM hN hR hQ hMNlo hMNhi hNγ hγlo hγhi
  by_cases hmid : γ ≤ γmid
  · exact hl x ((le_max_left _ _).trans hx) M N R Q γ hM hN hR hQ hMNlo hMNhi hNγ hγlo hmid
  · exact hh x ((le_max_right _ _).trans hx) M N R Q γ hM hN hR hQ hMNlo hMNhi hNγ
      (le_of_lt (lt_of_not_ge hmid)) hγhi

theorem sourceDyadicDeltaZeroEstimate_of_incidence
    («ω» δ ε γlo γhi : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hωsmall : «ω» < 1 / 16) (hδsmall : δ < 1 / 8) (hεsmall : ε < 1 / 1000)
    (hγmin : 1 / 4 + 4 * «ω» + δ + 100 * ε ≤ γlo)
    (hγsource : 8 * «ω» + 2 * δ + 100 * ε ≤ γlo)
    (hγmax : γhi ≤ 1 / 2 - 2 * «ω» - 50 * ε)
    (hsecondary : IncidenceSecondaryEstimate «ω» δ ε γlo γhi) :
    SourceDyadicDeltaZeroEstimate «ω» δ ε γlo γhi := by
  intro C cM TM cN TN hC hcM hMT hcN hNT dα dβ Eα Eβ A η hA hη
  exact sourceDeltaZero_rough_dyadic_uniform_log_saving_of_incidence
    «ω» δ ε γlo γhi C cM TM cN TN hω hδ hε
    hωsmall hδsmall hεsmall hγmin hγsource hγmax hsecondary
    hC hcM hMT hcN hNT dα dβ Eα Eβ A η hA hη

#print axioms SourceDyadicDeltaZeroEstimate.mono_range
#print axioms SourceDyadicDeltaZeroEstimate.join
#print axioms sourceDyadicDeltaZeroEstimate_of_incidence

end PrimeGap182Audit
