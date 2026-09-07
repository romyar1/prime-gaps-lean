import TypeIIIFrequencyMasks
import Mathlib.Data.ZMod.QuotientRing

/-!
# Actual CRT residue-set counting and its Fourier consequence

The finite product is over pairwise coprime nonzero factors. The proof uses the genuine
Chinese-remainder ring equivalence and the exact product cardinality of the allowed local
residue sets. No local-to-global counting assumption is introduced.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The actual residues modulo the product satisfying every local restriction. -/
def crtAllowedResidues (q : ι → ℕ) [NeZero (∏ i, q i)]
    (R : ∀ i, Finset (ZMod (q i))) : Finset (ZMod (∏ i, q i)) :=
  Finset.univ.filter (fun h => ∀ i, (h.val : ZMod (q i)) ∈ R i)

/-- The CRT coordinates are the natural reductions of the same integer representative. -/
theorem crt_coordinates
    (q : ι → ℕ) [NeZero (∏ i, q i)]
    (hcoprime : Pairwise (fun i j => (q i).Coprime (q j)))
    (h : ZMod (∏ i, q i)) (i : ι) :
    ZMod.prodEquivPi q hcoprime h i = (h.val : ZMod (q i)) := by
  rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.natCast_val]

/-- Exact cardinality, valid also for an empty factor family (product modulus one). -/
theorem crtAllowedResidues_card
    (q : ι → ℕ) [NeZero (∏ i, q i)]
    (hcoprime : Pairwise (fun i j => (q i).Coprime (q j)))
    (R : ∀ i, Finset (ZMod (q i))) :
    (crtAllowedResidues q R).card = ∏ i, (R i).card := by
  classical
  let e := ZMod.prodEquivPi q hcoprime
  have himage : (crtAllowedResidues q R).image e = Fintype.piFinset R := by
    ext z
    simp only [Finset.mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hh' := (Finset.mem_filter.mp hh).2
      intro i
      simpa only [e, crt_coordinates] using hh' i
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i
      have hcoord := congrFun (e.apply_symm_apply z) i
      rw [show e (e.symm z) i = ((e.symm z).val : ZMod (q i)) by
        exact crt_coordinates q hcoprime _ i] at hcoord
      rw [hcoord]
      exact hz i
  calc
    _ = ((crtAllowedResidues q R).image e).card :=
      (Finset.card_image_of_injective _ e.injective).symm
    _ = (Fintype.piFinset R).card := congrArg Finset.card himage
    _ = ∏ i, (R i).card := Fintype.card_piFinset R

/-- Product cardinal bounds follow from actual CRT, rather than being assumed. -/
theorem crtAllowedResidues_card_le
    (q : ι → ℕ) [NeZero (∏ i, q i)]
    (hcoprime : Pairwise (fun i j => (q i).Coprime (q j)))
    (R : ∀ i, Finset (ZMod (q i))) (D : ι → ℕ)
    (hD : ∀ i, (R i).card ≤ D i) :
    (crtAllowedResidues q R).card ≤ ∏ i, D i := by
  rw [crtAllowedResidues_card q hcoprime]
  exact Finset.prod_le_prod' (fun i _ => hD i)

/-- The Fourier mass of all allowed CRT residue classes has the exact product-cardinality
factor and the proved coset majorant. -/
theorem crtAllowedResidues_fourier_mass
    (s : ℕ) [NeZero s] (q : ι → ℕ) [NeZero (∏ i, q i)]
    (hcoprime : Pairwise (fun i j => (q i).Coprime (q j)))
    (hprod : (∏ i, q i) ∣ s) (R : ∀ i, Finset (ZMod (q i))) (A : ℤ) (N : ℕ) :
    (∑ h ∈ residueSet s (∏ i, q i) (crtAllowedResidues q R),
      ‖intervalFourier s A N h‖) ≤
        (∏ i, ((R i).card : ℝ)) * intervalMassBound s (∏ i, q i) N := by
  have hh := intervalFourier_residueSet_l1 s (∏ i, q i) A N hprod (crtAllowedResidues q R)
  simpa only [crtAllowedResidues_card q hcoprime, Nat.cast_prod] using hh

/-- Reducing an integer representative through a multiple does not change its smaller
residue. This records the actual representative compatibility in the CRT masks. -/
theorem residue_of_residue (Q q n : ℕ) [NeZero Q] (hq : q ∣ Q) :
    ((((n : ZMod Q).val) : ℕ) : ZMod q) = (n : ZMod q) := by
  rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_mod_of_dvd n hq

theorem mem_residueSet_crtAllowedResidues
    (s : ℕ) [NeZero s] (q : ι → ℕ) [NeZero (∏ i, q i)]
    (R : ∀ i, Finset (ZMod (q i))) (h : ZMod s) :
    h ∈ residueSet s (∏ i, q i) (crtAllowedResidues q R) ↔
      ∀ i, (h.val : ZMod (q i)) ∈ R i := by
  classical
  simp only [residueSet, crtAllowedResidues, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [residue_of_residue (∏ i, q i) _ h.val
    (Finset.dvd_prod_of_mem q (Finset.mem_univ _))]

/-- The CRT Fourier-mass bound stated directly with the original local residue tests. -/
theorem local_residue_tests_fourier_mass
    (s : ℕ) [NeZero s] (q : ι → ℕ) [NeZero (∏ i, q i)]
    (hcoprime : Pairwise (fun i j => (q i).Coprime (q j)))
    (hprod : (∏ i, q i) ∣ s) (R : ∀ i, Finset (ZMod (q i))) (A : ℤ) (N : ℕ) :
    (∑ h ∈ Finset.univ.filter (fun h : ZMod s =>
      ∀ i, (h.val : ZMod (q i)) ∈ R i), ‖intervalFourier s A N h‖) ≤
        (∏ i, ((R i).card : ℝ)) * intervalMassBound s (∏ i, q i) N := by
  have hset : Finset.univ.filter (fun h : ZMod s =>
      ∀ i, (h.val : ZMod (q i)) ∈ R i) =
        residueSet s (∏ i, q i) (crtAllowedResidues q R) := by
    ext h
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (mem_residueSet_crtAllowedResidues s q R h).symm
  rw [hset]
  exact crtAllowedResidues_fourier_mass s q hcoprime hprod R A N

/-- The second-coordinate CRT restrictions may depend on the full first frequency. Local
cardinality bounds are multiplied using the proved CRT cardinal formula. -/
theorem dependent_crt_rectangle_mass
    {κ : Type*} [Fintype κ]
    (s : ℕ) [NeZero s] (qh : ι → ℕ) (qk : κ → ℕ)
    [NeZero (∏ i, qh i)] [NeZero (∏ j, qk j)]
    (hch : Pairwise (fun i j => (qh i).Coprime (qh j)))
    (hck : Pairwise (fun i j => (qk i).Coprime (qk j)))
    (hph : (∏ i, qh i) ∣ s) (hpk : (∏ j, qk j) ∣ s)
    (Rh : ∀ i, Finset (ZMod (qh i)))
    (Rk : ZMod s → ∀ j, Finset (ZMod (qk j))) (Dk : κ → ℕ)
    (hDk : ∀ h j, (Rk h j).card ≤ Dk j) (Ah Ak : ℤ) (Nh Nk : ℕ) :
    (∑ h ∈ residueSet s (∏ i, qh i) (crtAllowedResidues qh Rh),
      ∑ k ∈ residueSet s (∏ j, qk j) (crtAllowedResidues qk (Rk h)),
        ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) ≤
      (∏ i, ((Rh i).card : ℝ)) * (∏ j, (Dk j : ℝ)) *
        intervalMassBound s (∏ i, qh i) Nh * intervalMassBound s (∏ j, qk j) Nk := by
  have hh := dependent_residue_rectangle_mass s (∏ i, qh i) (∏ j, qk j)
    Ah Ak Nh Nk (∏ j, Dk j) hph hpk
    (crtAllowedResidues qh Rh) (fun h => crtAllowedResidues qk (Rk h))
    (fun h => crtAllowedResidues_card_le qk hck (Rk h) Dk (hDk h))
  simpa only [crtAllowedResidues_card qh hch, Nat.cast_prod] using hh

#print axioms crt_coordinates
#print axioms crtAllowedResidues_card
#print axioms crtAllowedResidues_card_le
#print axioms crtAllowedResidues_fourier_mass
#print axioms mem_residueSet_crtAllowedResidues
#print axioms local_residue_tests_fourier_mass
#print axioms dependent_crt_rectangle_mass

end

end PrimeGap182.TypeIII
