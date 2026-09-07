import TypeIIISharedCRT
import TypeIIISharedFrequency

/-!
# Exact prime-factor product of the shared pair correlation

The CRT inverse cubes are absorbed by a bijective unit reindexing. The resulting local
additive frequency is `c * (w/p)^2`; this gives precisely the fixed matrix parameter
`a/c * (w/p)^(-2)` after frequency normalization.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem modCorrelation_one (A B c : ZMod 1) : modCorrelation 1 A B c = 1 := by
  simp only [modCorrelation, PrimeGap186.normalizedKloosterman3Mod_one, star_one, one_mul]
  have hc (h : (ZMod 1)ˣ) : c * (h : ZMod 1) = 0 := Subsingleton.elim _ _
  simp only [hc, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_smul]

/-- The exact two-factor correlation formula already proved in the public baseline. -/
theorem modCorrelation_mul_int (u v : ℕ) [NeZero u] [NeZero v]
    (huv : u.Coprime v) (A B c : ℤ) :
    modCorrelation (u * v) (A : ZMod (u * v)) (B : ZMod (u * v)) (c : ZMod (u * v)) =
      modCorrelation u (A : ZMod u) (B : ZMod u) ((c * (v : ℤ) ^ 2 : ℤ) : ZMod u) *
      modCorrelation v (A : ZMod v) (B : ZMod v) ((c * (u : ℤ) ^ 2 : ℤ) : ZMod v) :=
  PrimeGap186.kl3Mod_pair_twisted_mul u v huv A B c

theorem modCorrelation_modulus_congr (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q = r) (A B c : ℤ) :
    modCorrelation q (A : ZMod q) (B : ZMod q) (c : ZMod q) =
      modCorrelation r (A : ZMod r) (B : ZMod r) (c : ZMod r) := by
  subst r
  rfl

/-- Iterating the exact CRT formula over a finite coprime family. -/
theorem modCorrelation_finset_crt {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hcp : Pairwise (fun i j => (q i).Coprime (q j)))
    (S : Finset ι) [hS : NeZero (∏ i ∈ S, q i)] (A B c : ℤ) :
    modCorrelation (∏ i ∈ S, q i) (A : ZMod (∏ i ∈ S, q i))
      (B : ZMod (∏ i ∈ S, q i)) (c : ZMod (∏ i ∈ S, q i)) =
      ∏ i ∈ S, modCorrelation (q i) (A : ZMod (q i)) (B : ZMod (q i))
        ((c * ((∏ j ∈ S.erase i, q j : ℕ) : ℤ) ^ 2 : ℤ) : ZMod (q i)) := by
  revert hS
  induction S using Finset.induction_on generalizing c with
  | empty =>
    intro _
    simp only [Finset.prod_empty, modCorrelation_one]
  | @insert i S hi ih =>
    intro _
    let : NeZero (∏ j ∈ S, q j) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun j _ => NeZero.ne (q j))⟩
    have hcop : (q i).Coprime (∏ j ∈ S, q j) :=
      Nat.Coprime.prod_right (fun j hj => hcp (fun hij => hi (hij ▸ hj)))
    have his (j : ι) (hj : j ∈ S) : i ≠ j := fun hij => hi (hij ▸ hj)
    have herase (j : ι) (hj : j ∈ S) :
        (insert i S).erase j = insert i (S.erase j) :=
      Finset.erase_insert_of_ne (his j hj)
    have hterm (j : ι) (hj : j ∈ S) :
        (c * (q i : ℤ) ^ 2) * ((∏ k ∈ S.erase j, q k : ℕ) : ℤ) ^ 2 =
          c * ((∏ k ∈ (insert i S).erase j, q k : ℕ) : ℤ) ^ 2 := by
      rw [herase j hj, Finset.prod_insert (fun hk => hi (Finset.mem_of_mem_erase hk)),
        Nat.cast_mul]
      ring
    calc
      _ = modCorrelation (q i * ∏ j ∈ S, q j)
          (A : ZMod (q i * ∏ j ∈ S, q j)) (B : ZMod (q i * ∏ j ∈ S, q j))
          (c : ZMod (q i * ∏ j ∈ S, q j)) :=
        modCorrelation_modulus_congr _ _ (Finset.prod_insert hi) A B c
      _ = modCorrelation (q i) (A : ZMod (q i)) (B : ZMod (q i))
          ((c * ((∏ j ∈ S, q j : ℕ) : ℤ) ^ 2 : ℤ) : ZMod (q i)) *
          modCorrelation (∏ j ∈ S, q j) (A : ZMod (∏ j ∈ S, q j))
            (B : ZMod (∏ j ∈ S, q j))
            ((c * (q i : ℤ) ^ 2 : ℤ) : ZMod (∏ j ∈ S, q j)) := by
        exact modCorrelation_mul_int (q i) (∏ j ∈ S, q j) hcop A B c
      _ = _ := by
        rw [ih (c * (q i : ℤ) ^ 2), Finset.prod_insert hi, Finset.erase_insert hi]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [hterm j hj]

/-- The actual complementary factor in a finite CRT family. -/
def crtComplement {ι : Type*} [Fintype ι] (q : ι → ℕ) (i : ι) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, q j

theorem modCorrelation_fintype_crt_int {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (A B c : ℤ) :
    modCorrelation (∏ i, q i) (A : ZMod (∏ i, q i))
      (B : ZMod (∏ i, q i)) (c : ZMod (∏ i, q i)) =
      ∏ i, modCorrelation (q i) (A : ZMod (q i)) (B : ZMod (q i))
        ((c * (crtComplement q i : ℤ) ^ 2 : ℤ) : ZMod (q i)) := by
  simpa only [crtComplement] using modCorrelation_finset_crt q hcp Finset.univ A B c

theorem crtComplement_mul {ι : Type*} [Fintype ι] (q : ι → ℕ) (i : ι) :
    q i * crtComplement q i = ∏ j, q j := by
  exact Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)

theorem crtComplement_eq_div {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (i : ι) :
    crtComplement q i = (∏ j, q j) / q i := by
  exact (Nat.div_eq_of_eq_mul_right (NeZero.pos (q i)) (crtComplement_mul q i).symm).symm

theorem crtComplement_coprime {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (i : ι) :
    (q i).Coprime (crtComplement q i) := by
  apply Nat.Coprime.prod_right
  intro j hj
  exact hcp (Finset.ne_of_mem_erase hj).symm

/-- The same exact factorization for arbitrary actual residues at the composite modulus. -/
theorem modCorrelation_fintype_crt {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j)))
    (A B c : ZMod (∏ i, q i)) :
    modCorrelation (∏ i, q i) A B c =
      ∏ i, modCorrelation (q i) (A.val : ZMod (q i)) (B.val : ZMod (q i))
        ((c.val : ZMod (q i)) * (crtComplement q i : ZMod (q i)) ^ 2) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective A
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective B
  obtain ⟨d, rfl⟩ := ZMod.intCast_surjective c
  have hreduce (i : ι) (x : ℤ) :
      ((x : ZMod (∏ j, q j)).val : ZMod (q i)) = (x : ZMod (q i)) := by
    rw [← ZMod.cast_eq_val,
      ZMod.cast_intCast (Finset.dvd_prod_of_mem q (Finset.mem_univ i))]
  simpa only [hreduce, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using
    modCorrelation_fintype_crt_int q hcp a b d

/-- The composite shared factor in the actual inverse-index CRT identity is precisely the
product of the local expressions used by the fixed-parameter matrix estimate. -/
theorem shared_modCorrelation_prime_product {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime] [NeZero (∏ i, q i)]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j)))
    (a m n u v c : ℤ) (hm : IsUnit (m : ZMod (∏ i, q i)))
    (hn : IsUnit (n : ZMod (∏ i, q i))) (hu : IsUnit (u : ZMod (∏ i, q i)))
    (hv : IsUnit (v : ZMod (∏ i, q i))) :
    modCorrelation (∏ i, q i)
      ((a : ZMod (∏ i, q i)) * (m : ZMod (∏ i, q i))⁻¹ * ((u : ZMod (∏ i, q i))⁻¹) ^ 3)
      ((a : ZMod (∏ i, q i)) * (n : ZMod (∏ i, q i))⁻¹ * ((v : ZMod (∏ i, q i))⁻¹) ^ 3)
      ((c : ZMod (∏ i, q i)) * ((u : ZMod (∏ i, q i)) * (v : ZMod (∏ i, q i)))⁻¹) =
      ∏ i, correlation (q i)
        ((a : ZMod (q i)) / ((m : ZMod (q i)) * (u : ZMod (q i)) ^ 3))
        ((a : ZMod (q i)) / ((n : ZMod (q i)) * (v : ZMod (q i)) ^ 3))
        (((c : ZMod (q i)) * (crtComplement q i : ZMod (q i)) ^ 2) /
          ((u : ZMod (q i)) * (v : ZMod (q i)))) := by
  rw [modCorrelation_fintype_crt q hcp]
  apply Finset.prod_congr rfl
  intro i _
  let π := ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) (ZMod (q i))
  have hval (x : ZMod (∏ j, q j)) : (x.val : ZMod (q i)) = π x := by
    simp only [π, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [modCorrelation_prime]
  simp only [hval, map_mul, map_pow, map_intCast, PrimeGap186.phaseCRT_map_inv π hm,
    PrimeGap186.phaseCRT_map_inv π hn, PrimeGap186.phaseCRT_map_inv π hu,
    PrimeGap186.phaseCRT_map_inv π hv, PrimeGap186.phaseCRT_map_inv π (hu.mul hv)]
  have hm' : (m : ZMod (q i)) ≠ 0 := by
    simpa only [map_intCast] using (hm.map π).ne_zero
  have hn' : (n : ZMod (q i)) ≠ 0 := by
    simpa only [map_intCast] using (hn.map π).ne_zero
  have hu' : (u : ZMod (q i)) ≠ 0 := by
    simpa only [map_intCast] using (hu.map π).ne_zero
  have hv' : (v : ZMod (q i)) ≠ 0 := by
    simpa only [map_intCast] using (hv.map π).ne_zero
  congr 1 <;> field_simp

#print axioms modCorrelation_mul_int
#print axioms modCorrelation_finset_crt
#print axioms modCorrelation_fintype_crt_int
#print axioms modCorrelation_fintype_crt
#print axioms shared_modCorrelation_prime_product

end

end PrimeGap182.TypeIII
