import SourcePairingMoments182

/-! Actual presieving residue for any admissible 39-element tuple.
The CRT proof is adapted from the public 186 proof, lines 202119--202170;
the cardinality has been changed in the statement and every indexed step. -/

noncomputable section
open PrimeGap186
open scoped BigOperators
namespace PrimeGap182Analytic

theorem exists_admissible_presieve_residue182
    {𝓗 : Finset ℕ}
    {h𝓗_card : 𝓗.card = 39}
    {h𝓗_admissible : ∀ p : ℕ, p.Prime →
      ∃ a ∈ Finset.range p, a ∉ 𝓗.image (fun h => h % p)} (W : ℕ) (hW : 0 < W) :
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    ∃ v : ℕ, v < W ∧ ∀ i : Fin 39, Nat.Coprime (v + h i) W := by
  classical
  intro h
  let P : Finset ℕ := W.primeFactors
  have hP (p : P) : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  have havailable (p : P) : ∃ a ∈ Finset.range (p : ℕ),
      a ∉ 𝓗.image (fun n => n % (p : ℕ)) :=
    h𝓗_admissible p (hP p)
  choose a haRange haMissing using havailable
  let r : (p : P) → ZMod (p : ℕ) := fun p => -(a p : ZMod (p : ℕ))
  have hnz (p : P) (_ : p ∈ (Finset.univ : Finset P)) : (p : ℕ) ≠ 0 := (hP p).ne_zero
  have hpair : Set.Pairwise (↑(Finset.univ : Finset P) : Set P)
      (fun p q => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p _ q _ hpq
    exact (Nat.coprime_primes (hP p) (hP q)).mpr
      (fun hpq' => hpq (Subtype.ext hpq'))
  let raw : ℕ :=
    (Nat.chineseRemainderOfFinset (fun p : P => (r p).val)
      (fun p : P => (p : ℕ)) Finset.univ hnz hpair).val
  have hraw (p : P) : (raw : ZMod (p : ℕ)) = -(a p : ZMod (p : ℕ)) := by
    let : NeZero (p : ℕ) := ⟨(hP p).ne_zero⟩
    have hh : Nat.ModEq (p : ℕ) raw (r p).val :=
      (Nat.chineseRemainderOfFinset (fun p : P => (r p).val)
        (fun p : P => (p : ℕ)) Finset.univ hnz hpair).property p (Finset.mem_univ p)
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hh).trans (ZMod.natCast_zmod_val _)
  have hcoprime (i : Fin 39) : Nat.Coprime (raw + h i) W := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpW
    let pp : P := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpW, hW.ne'⟩⟩
    have hz : (raw : ZMod p) + (h i : ZMod p) = 0 := by
      simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff (raw + h i) p).mpr hpd
    rw [hraw pp] at hz
    have heq : (h i : ZMod p) = (a pp : ZMod p) :=
      sub_eq_zero.mp (by simpa only [sub_eq_add_neg, add_comm] using hz)
    have hmod : h i % p = a pp :=
      ((ZMod.natCast_eq_natCast_iff' (h i) (a pp) p).mp heq).trans
        (Nat.mod_eq_of_lt (Finset.mem_range.mp (haRange pp)))
    exact haMissing pp (Finset.mem_image.mpr
      ⟨h i, 𝓗.orderEmbOfFin_mem h𝓗_card i, hmod⟩)
  refine ⟨raw % W, Nat.mod_lt raw hW, ?_⟩
  intro i
  have hh := (Nat.mod_modEq raw W).add_right (h i)
  rw [Nat.coprime_iff_gcd_eq_one, hh.gcd_eq]
  exact hcoprime i

#print axioms exists_admissible_presieve_residue182
end PrimeGap182Analytic
