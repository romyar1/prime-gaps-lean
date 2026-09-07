import HarmanData182

/-! The three-colour Heath-Brown case split at the new 182 parameters.
Adapted from the Apache-2.0 baseline, with two strengthened combinatorial
arguments documented and checked by scripts/build_harman_trichotomy.py.
This is a finite theorem about actual factor exponents, not a distribution
assumption. Type III singles lie in [.17272 - tau, .41364 + tau] and
all three pair sums exceed .58636 - tau. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem minorant_three_prime_heathBrown_trichotomy
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10)
    {n : ℕ} (α : Fin n → ℝ) (color : Fin n → Fin 3)
    (hα : ∀ i, 0 ≤ α i)
    (htotal : |(∑ i, α i) - 1| ≤ τ / 1000)
    (hcolor : ∀ c : Fin 3,
      1 - 34941 / 100000 - 41361 / 100000 - τ / 5 ≤
        ∑ i ∈ (Finset.univ.filter (fun i => color i = c)), α i) :
    (∃ i, 34941 / 100000 - τ ≤ α i) ∨
    (∃ s : Finset (Fin n),
      41361 / 100000 - τ ≤ ∑ i ∈ s, α i ∧
        ∑ i ∈ s, α i ≤ 58639 / 100000 + τ) ∨
    (∃ i j k : Fin n,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (4318 / 25000 - τ ≤ α i ∧ α i ≤ 10341 / 25000 + τ) ∧
      (4318 / 25000 - τ ≤ α j ∧ α j ≤ 10341 / 25000 + τ) ∧
      (4318 / 25000 - τ ≤ α k ∧ α k ≤ 10341 / 25000 + τ) ∧
      14659 / 25000 - τ ≤ α i + α j ∧
      14659 / 25000 - τ ≤ α i + α k ∧
      14659 / 25000 - τ ≤ α j + α k) := by
  let A : ℝ := 41361 / 100000 - τ
  let B : ℝ := 58639 / 100000 + τ
  let C : ℝ := 34941 / 100000 - τ
  let D : ℝ := B - A
  let T : ℝ := ∑ i, α i
  change |T - 1| ≤ τ / 1000 at htotal
  obtain ⟨htotalLo, htotalHi⟩ := abs_le.mp htotal
  have hTlo : 1 - τ / 1000 ≤ T := by linarith
  have hThi : T ≤ 1 + τ / 1000 := by linarith
  have hA : 0 < A := by dsimp [A]; linarith only [hτsmall]
  have hD : 0 < D := by dsimp [D, B, A]; linarith only [hτ]
  have hCA : C < A := by dsimp [C, A]; linarith only []
  have hAC : A + C < 1 - τ / 1000 := by dsimp [A, C]; linarith only [hτ]
  have htwoA : 2 * A < 1 - τ / 1000 := by dsimp [A]; linarith only [hτ]
  have hcross : A < 2 * (B - C) := by dsimp [A, B, C]; linarith only [hτ]
  have hcrossLarge : 2 * A < B + 2 * D := by dsimp [A, B, D]; linarith only [hτ]
  have hBClo : 4318 / 25000 - τ < B - C := by dsimp [B, C]; linarith only [hτ]
  have hDlo : 4318 / 25000 - τ < D := by dsimp [D, B, A]; linarith only [hτ]
  have hCup : C < 10341 / 25000 + τ := by dsimp [C]; linarith only [hτ]
  have hBlo : 14659 / 25000 - τ < B := by dsimp [B]; linarith only [hτ]
  have hsix : 1 + τ / 1000 < 6 * D := by dsimp [D, B, A]; linarith only [hτ]
  have hcolorGap : 1 + τ / 1000 - 4 * B / 3 <
      1 - 34941 / 100000 - 41361 / 100000 - τ / 5 := by dsimp [D, B, A]; linarith only [hτ]
  by_cases hI : ∃ i, C ≤ α i
  · exact Or.inl hI
  right
  by_cases hII : ∃ s : Finset (Fin n), A ≤ ∑ i ∈ s, α i ∧ ∑ i ∈ s, α i ≤ B
  · exact Or.inl hII
  right
  by_contra hIII
  have hupper (i : Fin n) : α i < C := lt_of_not_ge (fun hi => hI ⟨i, hi⟩)
  have hsmall (i : Fin n) : α i < A := (hupper i).trans hCA
  have havoid (s : Finset (Fin n)) :
      ¬ (A ≤ ∑ i ∈ s, α i ∧ ∑ i ∈ s, α i ≤ B) := fun hs => hII ⟨s, hs⟩
  have habove (s : Finset (Fin n)) (hs : A ≤ ∑ i ∈ s, α i) :
      B < ∑ i ∈ s, α i := lt_of_not_ge (fun ht => havoid s ⟨hs, ht⟩)
  have hpair (i j : Fin n) (hij : i ≠ j) : α i + α j < A := by
    by_contra hijLow
    have hijHigh : B < α i + α j := by
      have hh := habove {i, j} (by simpa [Finset.sum_insert, hij] using le_of_not_gt hijLow)
      simpa [Finset.sum_insert, hij] using hh
    let V : Finset (Fin n) := ({i, j} : Finset (Fin n))ᶜ
    have hTsplit : α i + α j + (∑ k ∈ V, α k) = T := by
      simpa [V, T, Finset.sum_insert, hij] using
        Finset.sum_add_sum_compl ({i, j} : Finset (Fin n)) α
    have hk : ∃ k ∈ V, D < α k := by
      by_contra hk
      push Not at hk
      have hdisjoint : Disjoint ({i} : Finset (Fin n)) V := by
        apply Finset.disjoint_left.mpr
        intro k hki hkV
        have hki' : k = i := Finset.mem_singleton.mp hki
        subst k
        simp [V] at hkV
      have hh := sum_add_sum_lt_of_no_subset_sum_in_Icc α A B havoid {i} V hdisjoint
        (by simpa only [Finset.sum_singleton] using hsmall i) hk
      simp only [Finset.sum_singleton] at hh
      have hTu : T < A + C := by
        calc
          T = (α i + ∑ k ∈ V, α k) + α j := by rw [← hTsplit]; ring
          _ < A + C := add_lt_add hh (hupper j)
      exact (not_lt_of_ge hTlo) (hTu.trans hAC)
    obtain ⟨k, hkV, hkD⟩ := hk
    have hki : k ≠ i ∧ k ≠ j := by simpa [V] using hkV
    have hik : i ≠ k := hki.1.symm
    have hjk : j ≠ k := hki.2.symm
    have hiBC : B - C < α i := by
      simpa only [add_sub_cancel_right] using sub_lt_sub hijHigh (hupper j)
    have hjBC : B - C < α j := by
      have hh := sub_lt_sub hijHigh (hupper i)
      simpa only [add_sub_cancel_left] using hh
    have hsome : A ≤ α i + α k ∨ A ≤ α j + α k := by
      by_contra h
      push Not at h
      linarith only [h.1, h.2, hijHigh, hkD, hcrossLarge]
    have hh : B < α i + α k ∧ B < α j + α k := by
      rcases hsome with hikA | hjkA
      · have hikHigh : B < α i + α k := by
          have hh := habove {i, k} (by simpa [Finset.sum_insert, hik] using hikA)
          simpa [Finset.sum_insert, hik] using hh
        have hkBC : B - C < α k := by
          linarith only [hikHigh, hupper i]
        have hjkA : A ≤ α j + α k := by
          linarith only [hjBC, hkBC, hcross]
        have hjkHigh : B < α j + α k := by
          have hh := habove {j, k} (by simpa [Finset.sum_insert, hjk] using hjkA)
          simpa [Finset.sum_insert, hjk] using hh
        exact ⟨hikHigh, hjkHigh⟩
      · have hjkHigh : B < α j + α k := by
          have hh := habove {j, k} (by simpa [Finset.sum_insert, hjk] using hjkA)
          simpa [Finset.sum_insert, hjk] using hh
        have hkBC : B - C < α k := by
          linarith only [hjkHigh, hupper j]
        have hikA : A ≤ α i + α k := by
          linarith only [hiBC, hkBC, hcross]
        have hikHigh : B < α i + α k := by
          have hh := habove {i, k} (by simpa [Finset.sum_insert, hik] using hikA)
          simpa [Finset.sum_insert, hik] using hh
        exact ⟨hikHigh, hjkHigh⟩
    obtain ⟨hikHigh, hjkHigh⟩ := hh
    apply hIII
    refine ⟨i, j, k, hij, hik, hjk, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact hBClo.le.trans hiBC.le
    · exact (hupper i).le.trans hCup.le
    · exact hBClo.le.trans hjBC.le
    · exact (hupper j).le.trans hCup.le
    · exact hDlo.le.trans hkD.le
    · exact (hupper k).le.trans hCup.le
    · exact hBlo.le.trans hijHigh.le
    · exact hBlo.le.trans hikHigh.le
    · exact hBlo.le.trans hjkHigh.le
  let H : Finset (Fin n) := Finset.univ.filter (fun i => D < α i)
  let S : Finset (Fin n) := Hᶜ
  have hSupper (i : Fin n) (hi : i ∈ S) : α i ≤ D := by
    have hiH : i ∉ H := Finset.mem_compl.mp hi
    by_contra hnot
    exact hiH (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hnot⟩)
  have hHfive : 5 ≤ H.card := by
    by_contra hnot
    have hHfour : H.card ≤ 4 := by omega
    obtain ⟨U, hUH, hUcard⟩ := Finset.exists_subset_card_eq (s := H) (n := min 2 H.card)
      (min_le_right _ _)
    have hUtwo : U.card ≤ 2 := hUcard.trans_le (min_le_left _ _)
    have hVtwo : (H \ U).card ≤ 2 := by
      rw [Finset.card_sdiff_of_subset hUH]
      omega
    have hUsmall := sum_lt_of_card_le_two α A hA hsmall hpair U hUtwo
    have hVsmall := sum_lt_of_card_le_two α A hA hsmall hpair (H \ U) hVtwo
    have hUS : Disjoint U S := by
      apply Finset.disjoint_left.mpr
      intro i hiU hiS
      exact (Finset.mem_compl.mp hiS) (hUH hiU)
    have hUScross := sum_add_sum_lt_of_no_subset_sum_in_Icc α A B havoid U S hUS hUsmall hSupper
    have hsplitH : (∑ i ∈ H \ U, α i) + ∑ i ∈ U, α i = ∑ i ∈ H, α i :=
      Finset.sum_sdiff hUH
    have hsplitAll : (∑ i ∈ H, α i) + ∑ i ∈ S, α i = T :=
      Finset.sum_add_sum_compl H α
    have hTu : T < 2 * A := by
      calc
        T = ((∑ i ∈ U, α i) + ∑ i ∈ S, α i) + ∑ i ∈ H \ U, α i := by
          rw [← hsplitAll, ← hsplitH]
          ring
        _ < A + A := add_lt_add hUScross hVsmall
        _ = 2 * A := by ring
    exact (not_lt_of_ge hTlo) (hTu.trans htwoA)
  have hHlefive : H.card ≤ 5 := by
    by_contra hnot
    have hHsix : 6 ≤ H.card := by omega
    have hcast : (6 : ℝ) ≤ (H.card : ℝ) := by exact_mod_cast hHsix
    have hHlo : 6 * D ≤ ∑ i ∈ H, α i := by
      calc
        6 * D ≤ (H.card : ℝ) * D := mul_le_mul_of_nonneg_right hcast hD.le
        _ = ∑ _i ∈ H, D := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
    have hHup : (∑ i ∈ H, α i) ≤ T :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hα i)
    exact (not_lt_of_ge (hHlo.trans hHup)) (hThi.trans_lt hsix)
  have hHcard : H.card = 5 := le_antisymm hHlefive hHfive
  obtain ⟨c, hc⟩ := three_color_five_singletons H color hHcard
  let K : Finset (Fin n) := H.filter (fun i => color i ≠ c)
  let I : Finset (Fin n) := Finset.univ.filter (fun i => color i = c)
  have hfour (V : Finset (Fin n)) (hVH : V ⊆ H) (hV : V.card = 4) :
      4 * B / 3 ≤ ∑ i ∈ V, α i := by
    have htrip (i : Fin n) (hi : i ∈ V) : B < ∑ j ∈ V.erase i, α j := by
      have hsize : (V.erase i).card = 3 := by rw [Finset.card_erase_of_mem hi, hV]
      have hlow : 3 * D ≤ ∑ j ∈ V.erase i, α j := by
        calc
          3 * D = ∑ _j ∈ V.erase i, D := by simp [hsize]
          _ ≤ _ := Finset.sum_le_sum fun j hj =>
            (Finset.mem_filter.mp (hVH (Finset.mem_of_mem_erase hj))).2.le
      have hAD : A < 3 * D := by dsimp [A, D, B]; linarith only [hτ]
      exact habove (V.erase i) (hAD.le.trans hlow)
    have heq (i : Fin n) (hi : i ∈ V) :
        (∑ j ∈ V.erase i, α j) = (∑ j ∈ V, α j) - α i := by
      exact (eq_sub_iff_add_eq).mpr (Finset.sum_erase_add V α hi)
    have hs : 4 * B ≤ ∑ i ∈ V, ∑ j ∈ V.erase i, α j := by
      calc
        4 * B = ∑ _i ∈ V, B := by simp [hV]
        _ ≤ _ := Finset.sum_le_sum fun i hi => (htrip i hi).le
    rw [Finset.sum_congr rfl heq, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hV] at hs
    norm_num only [Nat.cast_ofNat] at hs
    linarith only [hs]
  obtain ⟨V, hVK, hV⟩ := Finset.exists_subset_card_eq (s := K) (n := 4) hc
  have hKlo : 4 * B / 3 ≤ ∑ i ∈ K, α i :=
    (hfour V (hVK.trans (Finset.filter_subset _ _)) hV).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hVK (fun i _ _ => hα i))
  have hIK : Disjoint I K := by
    apply Finset.disjoint_left.mpr
    intro i hiI hiK
    exact (Finset.mem_filter.mp hiK).2 (Finset.mem_filter.mp hiI).2
  have hIKsum : (∑ i ∈ I, α i) + ∑ i ∈ K, α i ≤ T := by
    rw [← Finset.sum_union hIK]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hα i)
  have hcolorc := hcolor c
  change 1 - 34941 / 100000 - 41361 / 100000 - τ / 5 ≤ ∑ i ∈ I, α i at hcolorc
  have hcolorUp : (∑ i ∈ I, α i) ≤ 1 + τ / 1000 - 4 * B / 3 := by
    apply (le_sub_iff_add_le).mpr
    exact (add_le_add (le_refl (∑ i ∈ I, α i)) hKlo).trans (hIKsum.trans hThi)
  exact (not_lt_of_ge hcolorc) (hcolorUp.trans_lt hcolorGap)

theorem minorant_three_prime_colored_slot_trichotomy
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10)
    (r : Fin 3 → Fin 5)
    (α : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℝ)
    (hα : ∀ c i, 0 ≤ α c i)
    (hcolor : ∀ c : Fin 3,
      1 - 34941 / 100000 - 41361 / 100000 - τ / 5 ≤ ∑ i, α c i)
    (htotal : |(∑ c, ∑ i, α c i) - 1| ≤ τ / 1000)
    (hmu : ∀ (c : Fin 3) (i : Fin (2 * ((r c).val + 1))),
      i.val < (r c).val + 1 → α c i ≤ 1 / 10) :
    let I := Σ c : Fin 3, Fin (2 * ((r c).val + 1))
    (∃ s : I,
      (r s.1).val + 1 ≤ s.2.val ∧ 34941 / 100000 - τ ≤ α s.1 s.2) ∨
    (∃ S : Finset I,
      41361 / 100000 - τ ≤ ∑ s ∈ S, α s.1 s.2 ∧
        (∑ s ∈ S, α s.1 s.2) ≤ 58639 / 100000 + τ) ∨
    (∃ s t u : I,
      s ≠ t ∧ s ≠ u ∧ t ≠ u ∧
      (r s.1).val + 1 ≤ s.2.val ∧ (r t.1).val + 1 ≤ t.2.val ∧
      (r u.1).val + 1 ≤ u.2.val ∧
      (4318 / 25000 - τ ≤ α s.1 s.2 ∧
        α s.1 s.2 ≤ 10341 / 25000 + τ) ∧
      (4318 / 25000 - τ ≤ α t.1 t.2 ∧
        α t.1 t.2 ≤ 10341 / 25000 + τ) ∧
      (4318 / 25000 - τ ≤ α u.1 u.2 ∧
        α u.1 u.2 ≤ 10341 / 25000 + τ) ∧
      14659 / 25000 - τ ≤ α s.1 s.2 + α t.1 t.2 ∧
      14659 / 25000 - τ ≤ α s.1 s.2 + α u.1 u.2 ∧
      14659 / 25000 - τ ≤ α t.1 t.2 + α u.1 u.2) := by
  classical
  intro I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have htotalEq :
      (∑ i : Fin (Fintype.card I), α (e.symm i).1 (e.symm i).2) =
        ∑ c, ∑ i, α c i :=
    (e.symm.sum_comp (fun s : I => α s.1 s.2)).trans (Fintype.sum_sigma _)
  have hcolorEq (c : Fin 3) :
      (∑ i ∈ (Finset.univ.filter (fun i : Fin (Fintype.card I) => (e.symm i).1 = c)),
        α (e.symm i).1 (e.symm i).2) = ∑ j, α c j := by
    calc
      _ = ∑ i : Fin (Fintype.card I),
          if (e.symm i).1 = c then α (e.symm i).1 (e.symm i).2 else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ s : I, if s.1 = c then α s.1 s.2 else 0 :=
        e.symm.sum_comp (fun s : I => if s.1 = c then α s.1 s.2 else 0)
      _ = ∑ j, α c j := by rw [Fintype.sum_sigma]; simp
  have hcases := minorant_three_prime_heathBrown_trichotomy τ hτ hτsmall
    (fun i : Fin (Fintype.card I) => α (e.symm i).1 (e.symm i).2)
    (fun i => (e.symm i).1)
    (fun i => hα (e.symm i).1 (e.symm i).2)
    (by simpa only [htotalEq] using htotal)
    (fun c => by simpa only [hcolorEq c] using hcolor c)
  have hNonMu (s : I) (hs : 4318 / 25000 - τ ≤ α s.1 s.2) :
      (r s.1).val + 1 ≤ s.2.val := by
    by_contra hbad
    have hsmall := hmu s.1 s.2 (by omega)
    have hlt : (1 / 10 : ℝ) < α s.1 s.2 :=
      (by linarith only [hτsmall] : (1 / 10 : ℝ) < 4318 / 25000 - τ).trans_le hs
    exact (not_lt_of_ge hsmall) hlt
  rcases hcases with ⟨i, hi⟩ | ⟨S, hSlo, hShi⟩ |
    ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hijLo, hikLo, hjkLo⟩
  · refine Or.inl ⟨e.symm i, hNonMu _ ?_, hi⟩
    exact (by linarith only [] :
      4318 / 25000 - τ ≤ 34941 / 100000 - τ).trans hi
  · have hsum :
        (∑ s ∈ S.image e.symm, α s.1 s.2) =
          ∑ i ∈ S, α (e.symm i).1 (e.symm i).2 :=
      Finset.sum_image (fun i _ j _ h => e.symm.injective h)
    exact Or.inr (Or.inl ⟨S.image e.symm,
      by simpa only [hsum] using hSlo, by simpa only [hsum] using hShi⟩)
  · refine Or.inr (Or.inr ⟨e.symm i, e.symm j, e.symm k,
      ?_, ?_, ?_, hNonMu _ hi.1, hNonMu _ hj.1, hNonMu _ hk.1,
      hi, hj, hk, hijLo, hikLo, hjkLo⟩)
    · exact fun h => hij (e.symm.injective h)
    · exact fun h => hik (e.symm.injective h)
    · exact fun h => hjk (e.symm.injective h)


#print axioms minorant_three_prime_heathBrown_trichotomy
#print axioms minorant_three_prime_colored_slot_trichotomy

end PrimeGap182Analytic.Harman
