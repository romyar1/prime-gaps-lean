import TrialAnalyticParameters182
import IncidenceSecondaryInterface

/-! Positive parameter room for the actual incidence source argument.
The working parameters are increased before epsilon is chosen. Epsilon
can then be arbitrarily small, as required by the source estimates. -/

noncomputable section
namespace PrimeGap182Audit

structure IncidenceBilinearWindow («ω» δ σ γhi : ℝ) : Prop where
  hω : 0 < «ω»
  hδ : 0 < δ
  hσ : 0 < σ
  hσupper : σ < 1 / 4
  hωupper : «ω» < 3 / 200
  hγcap : 1 / 2 - σ ≤ 41361 / 100000
  h1 : 12 * «ω» + 6 * δ < 1 / 2 - σ
  h2 : γhi < 1 / 2 - 2 * «ω»
  h3 : 2 * γhi + 4 * «ω» + 2 * δ < 1
  h4 : 16 * «ω» + 7 * δ < 1 / 2 - σ
  h5 : 3 / 2 + 40 * «ω» + 16 * δ < 5 * (1 / 2 - σ)
  hhigh : 1 / 4 + 14 * «ω» + 4 * δ < γhi

namespace IncidenceBilinearWindow
variable {«ω» δ σ γhi : ℝ}

theorem coarse (h : IncidenceBilinearWindow «ω» δ σ γhi) :
    «ω» < 1 / 16 ∧ δ < 1 / 8 ∧ 68 * «ω» + 20 * δ < 1 ∧
      1 / 4 + 4 * «ω» + δ < 1 / 2 - σ ∧
      8 * «ω» + 2 * δ < 1 / 2 - σ := by
  refine ⟨by linarith only [h.hωupper], ?_, ?_, ?_, ?_⟩
  · linarith only [h.h5, h.hγcap, h.hω]
  · linarith only [h.h5, h.hγcap, h.hωupper]
  · linarith only [h.h5, h.hω, h.hδ]
  · linarith only [h.h5, h.hδ]

theorem retreat (h : IncidenceBilinearWindow «ω» δ σ γhi) :
    ∃ r : ℝ, 0 < r ∧ IncidenceBilinearWindow («ω» + r) (δ + r) σ γhi := by
  classical
  let F : Finset ℝ := {
    3 / 200 - «ω»,
    1 / 2 - σ - 12 * «ω» - 6 * δ,
    1 / 2 - 2 * «ω» - γhi,
    1 - 2 * γhi - 4 * «ω» - 2 * δ,
    1 / 2 - σ - 16 * «ω» - 7 * δ,
    5 * (1 / 2 - σ) - 3 / 2 - 40 * «ω» - 16 * δ,
    γhi - 1 / 4 - 14 * «ω» - 4 * δ }
  have hF : F.Nonempty := ⟨3 / 200 - «ω», by simp [F]⟩
  have hFpos : ∀ t ∈ F, 0 < t := by
    intro t ht
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals linarith only [h.hωupper, h.h1, h.h2, h.h3, h.h4, h.h5, h.hhigh]
  let r : ℝ := F.min' hF / 1000
  have hr : 0 < r := div_pos (hFpos _ (Finset.min'_mem F hF)) (by norm_num)
  have hb (t : ℝ) (ht : t ∈ F) : 1000 * r ≤ t := by
    calc
      1000 * r = F.min' hF := by dsimp only [r]; ring
      _ ≤ t := Finset.min'_le F t ht
  have hb0 := hb (3 / 200 - «ω») (by simp [F])
  have hb1 := hb (1 / 2 - σ - 12 * «ω» - 6 * δ) (by simp [F])
  have hb2 := hb (1 / 2 - 2 * «ω» - γhi) (by simp [F])
  have hb3 := hb (1 - 2 * γhi - 4 * «ω» - 2 * δ) (by simp [F])
  have hb4 := hb (1 / 2 - σ - 16 * «ω» - 7 * δ) (by simp [F])
  have hb5 := hb (5 * (1 / 2 - σ) - 3 / 2 - 40 * «ω» - 16 * δ) (by simp [F])
  have hbh := hb (γhi - 1 / 4 - 14 * «ω» - 4 * δ) (by simp [F])
  refine ⟨r, hr, {
    hω := add_pos h.hω hr
    hδ := add_pos h.hδ hr
    hσ := h.hσ
    hσupper := h.hσupper
    hωupper := by linarith only [hb0, hr]
    hγcap := h.hγcap
    h1 := by linarith only [hb1, hr]
    h2 := by linarith only [hb2, hr]
    h3 := by linarith only [hb3, hr]
    h4 := by linarith only [hb4, hr]
    h5 := by linarith only [hb5, hr]
    hhigh := by linarith only [hbh, hr] }⟩

theorem choose_epsilon (h : IncidenceBilinearWindow «ω» δ σ γhi)
    (δbase ε₀ : ℝ) (hδbase : δbase < δ) (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ ε < δ / 10 ^ 100 ∧ ε < 1 / 1000 ∧
      δbase + ε ≤ δ ∧
      1 / 4 + 4 * «ω» + δ + 100 * ε ≤ 1 / 2 - σ ∧
      8 * «ω» + 2 * δ + 100 * ε ≤ 1 / 2 - σ ∧
      γhi ≤ 1 / 2 - 2 * «ω» - 50 * ε ∧
      1 / 4 + 14 * «ω» + 4 * δ + 100 * ε ≤ γhi := by
  classical
  obtain ⟨_, _, _, hmin, hsource⟩ := h.coarse
  have hδε : 0 < δ / 10 ^ 100 := div_pos h.hδ (by norm_num)
  let F : Finset ℝ := {
    ε₀, δ / 10 ^ 100, 1 / 1000, δ - δbase,
    1 / 2 - σ - (1 / 4 + 4 * «ω» + δ),
    1 / 2 - σ - (8 * «ω» + 2 * δ),
    1 / 2 - 2 * «ω» - γhi,
    γhi - (1 / 4 + 14 * «ω» + 4 * δ) }
  have hF : F.Nonempty := ⟨ε₀, by simp [F]⟩
  have hFpos : ∀ t ∈ F, 0 < t := by
    intro t ht
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals linarith only [hε₀, hδε, hδbase, hmin, hsource, h.h2, h.hhigh]
  let ε : ℝ := F.min' hF / 1000
  have hε : 0 < ε := div_pos (hFpos _ (Finset.min'_mem F hF)) (by norm_num)
  have hb (t : ℝ) (ht : t ∈ F) : 1000 * ε ≤ t := by
    calc
      1000 * ε = F.min' hF := by dsimp only [ε]; ring
      _ ≤ t := Finset.min'_le F t ht
  have hb0 := hb ε₀ (by simp [F])
  have hb1 := hb (δ / 10 ^ 100) (by simp [F])
  have hb2 := hb (1 / 1000) (by simp [F])
  have hb3 := hb (δ - δbase) (by simp [F])
  have hb4 := hb (1 / 2 - σ - (1 / 4 + 4 * «ω» + δ)) (by simp [F])
  have hb5 := hb (1 / 2 - σ - (8 * «ω» + 2 * δ)) (by simp [F])
  have hb6 := hb (1 / 2 - 2 * «ω» - γhi) (by simp [F])
  have hb7 := hb (γhi - (1 / 4 + 14 * «ω» + 4 * δ)) (by simp [F])
  refine ⟨ε, hε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hb0, hε]
  · linarith only [hb1, hε]
  · linarith only [hb2, hε]
  · linarith only [hb3, hε]
  · linarith only [hb4, hε]
  · linarith only [hb5, hε]
  · linarith only [hb6, hε]
  · linarith only [hb7, hε]

end IncidenceBilinearWindow

theorem incidenceBilinearWindow_of_minorant_guards
    {«ω» δ τ : ℝ} (h : PrimeGap182.MinorantAnalyticGuards182 3 «ω» δ τ) :
    IncidenceBilinearWindow («ω» + τ) (δ + τ)
      ((1 / 2 : ℝ) - 41361 / 100000 + 2 * τ) (9 / 20) := by
  dsimp only [PrimeGap182.MinorantAnalyticGuards182] at h
  obtain ⟨hω, hδ, hτ, hτsmall, hu, hσ, _hσhalf, _hsmooth, _hIII, _hII, hcases⟩ := h
  have h3 : 12 * («ω» + τ) + 6 * (δ + τ) <
      1 / 2 - (1 / 2 - 41361 / 100000 + 2 * τ) ∧
      9 / 20 < 1 / 2 - 2 * («ω» + τ) ∧
      2 * (9 / 20) + 4 * («ω» + τ) + 2 * (δ + τ) < 1 ∧
      16 * («ω» + τ) + 7 * (δ + τ) <
        1 / 2 - (1 / 2 - 41361 / 100000 + 2 * τ) ∧
      3 / 2 + 40 * («ω» + τ) + 16 * (δ + τ) <
        5 * (1 / 2 - (1 / 2 - 41361 / 100000 + 2 * τ)) ∧
      1 / 4 + 14 * («ω» + τ) + 4 * (δ + τ) < 9 / 20 := by
    rcases hcases with h1 | h2 | h3
    · norm_num at h1
    · norm_num at h2
    · exact h3.2
  exact {
    hω := add_pos hω hτ
    hδ := add_pos hδ hτ
    hσ := hσ
    hσupper := by linarith only [hτsmall]
    hωupper := hu
    hγcap := by linarith only [hτ]
    h1 := h3.1
    h2 := h3.2.1
    h3 := h3.2.2.1
    h4 := h3.2.2.2.1
    h5 := h3.2.2.2.2.1
    hhigh := h3.2.2.2.2.2 }

/-- This is an intermediate family of estimates, to be proved from the
explicit finite-field rank-four bound by the incidence development. -/
def IncidenceSecondaryFamily182 : Prop :=
  ∀ («ω» δ γlo γhi : ℝ), 0 < «ω» → 0 < δ →
    12 * «ω» + 6 * δ < γlo → γhi < 1 / 2 - 2 * «ω» →
    2 * γhi + 4 * «ω» + 2 * δ < 1 → 16 * «ω» + 7 * δ < γlo →
    3 / 2 + 40 * «ω» + 16 * δ < 5 * γlo →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IncidenceSecondaryEstimate «ω» δ ε γlo γhi

#print axioms IncidenceBilinearWindow.coarse
#print axioms IncidenceBilinearWindow.retreat
#print axioms IncidenceBilinearWindow.choose_epsilon
#print axioms incidenceBilinearWindow_of_minorant_guards

end PrimeGap182Audit
