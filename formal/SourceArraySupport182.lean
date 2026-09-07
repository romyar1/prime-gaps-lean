import SourceIntegerSupport182

/-! Every nonzero coefficient of each actual face array has one of the
recorded source types. Signed combinations retain the union of their
supports; no cancellation or common-radius assumption is used. -/

noncomputable section
open PrimeGap186 PrimeGap182Analytic
open scoped BigOperators

namespace PrimeGap182
open SieveFaceRole182

def sieveRoleIntegerKinds : SieveFaceRole182 → Finset (Fin 4)
  | root => {0}
  | base => {1}
  | correction => {1, 2}
  | rootMinusBase => {0, 1}
  | subtractionMinusBase => {1, 3}
  | rootMinusSubtraction => {0, 3}

namespace TrialSmoothProfiles182

theorem sieveFacePart_source (P : TrialSmoothProfiles182) (i : Fin 39)
    (role : SieveFaceRole182) (Y : Fin 38 → Fin (P.m + 1) → ℝ)
    (h : P.sieveFacePart i role Y ≠ 0) :
    ∃ b : Fin 3, b.succ ∈ sieveRoleIntegerKinds role ∧ P.bandMaskedFace b i Y ≠ 0 := by
  cases role
  · exact (h rfl).elim
  · exact ⟨0, by decide, h⟩
  · by_cases hb : P.bandMaskedFace 0 i Y = 0
    · refine ⟨1, by decide, ?_⟩
      simpa only [sieveFacePart, hb, sub_zero] using h
    · exact ⟨0, by decide, hb⟩
  · exact ⟨0, by decide, fun hz => h (by simp only [sieveFacePart, hz, neg_zero])⟩
  · by_cases hb : P.bandMaskedFace 0 i Y = 0
    · refine ⟨2, by decide, ?_⟩
      simpa only [sieveFacePart, hb, sub_zero] using h
    · exact ⟨0, by decide, hb⟩
  · exact ⟨2, by decide, fun hz => h (by simp only [sieveFacePart, hz, neg_zero])⟩

theorem sieveRootPart_source (P : TrialSmoothProfiles182) (role : SieveFaceRole182)
    (X : Fin 39 → Fin (P.m + 1) → ℝ) (h : P.sieveRootPart role X ≠ 0) :
    0 ∈ sieveRoleIntegerKinds role ∧ P.F X ≠ 0 := by
  cases role
  · exact ⟨by decide, h⟩
  · exact (h rfl).elim
  · exact (h rfl).elim
  · exact ⟨by decide, h⟩
  · exact (h rfl).elim
  · exact ⟨by decide, h⟩

theorem sieveFaceArray_divisor_source (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (i : Fin 39) (role : SieveFaceRole182) (x : ℝ) (hx : 1 < x)
    (r : Fin 38 → ℕ) (hr : r ∈ (P.sieveFaceArray H i role x).support)
    (D : ℕ) (hD : D ∣ ∏ j, r j) :
    ∃ k ∈ sieveRoleIntegerKinds role, TrialIntegerSupport k (x ^ selbergRho182) D := by
  have hR : 1 < x ^ selbergRho182 := Real.one_lt_rpow hx (by norm_num [selbergRho182])
  change r ∈ (canonicalBandArray182 H P.a (P.sieveFacePart i role) x +
    selbergErasedArray39 i (canonicalBandArray182 H P.a (P.sieveRootPart role) x)).support at hr
  rcases Finset.mem_union.mp (Finsupp.support_add hr) with hc | he
  · obtain ⟨hsf, hdiv, hval⟩ := canonicalBandArray182_support_data H P.a
      (P.sieveFacePart i role) x r hc
    obtain ⟨b, hb, hface⟩ := P.sieveFacePart_source i role _ hval
    exact ⟨b.succ, hb, P.face_integer_support b i (presievingModulus H x) (x ^ selbergRho182)
      hR r hsf hdiv hface D hD⟩
  · obtain ⟨s, hs, hsr⟩ := selbergErasedArray39_support_witness i
      (canonicalBandArray182 H P.a (P.sieveRootPart role) x) r he
    obtain ⟨hsf, hdiv, hval⟩ := canonicalBandArray182_support_data H P.a
      (P.sieveRootPart role) x s hs
    obtain ⟨hk, hroot⟩ := P.sieveRootPart_source role _ hval
    have hrdvd : (∏ j, r j) ∣ ∏ j, s j := by
      rw [← hsr, Fin.prod_univ_succAbove _ i]
      exact dvd_mul_left _ _
    exact ⟨0, hk, P.root_integer_support (presievingModulus H x) (x ^ selbergRho182) hR
      s hsf hdiv hroot D (hD.trans hrdvd)⟩

theorem sieveFaceArray_coefficient_source (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (i : Fin 39) (role : SieveFaceRole182) (x : ℝ) (hx : 1 < x)
    (d : Fin 38 → ℕ)
    (hd : PrimeGap182.Selberg.selbergCoefficient (P.sieveFaceArray H i role x) d ≠ 0) :
    ∃ k ∈ sieveRoleIntegerKinds role,
      TrialIntegerSupport k (x ^ selbergRho182) (∏ j, d j) := by
  classical
  have hw : ∃ r ∈ (P.sieveFaceArray H i role x).support, ∀ j, d j ∣ r j := by
    apply PrimeGap182.Selberg.selbergCoefficient_mem_hereditary (P.sieveFaceArray H i role x)
      (fun e => ∃ r ∈ (P.sieveFaceArray H i role x).support, ∀ j, e j ∣ r j) _ _ d hd
    · rintro e s hes ⟨r, hr, hsr⟩
      exact ⟨r, hr, fun j => (hes j).trans (hsr j)⟩
    · intro r hr
      exact ⟨r, hr, fun _ => dvd_rfl⟩
  obtain ⟨r, hr, hdr⟩ := hw
  exact P.sieveFaceArray_divisor_source H i role x hx r hr (∏ j, d j)
    (Finset.prod_dvd_prod_of_dvd _ _ fun j _ => hdr j)

#print axioms sieveFacePart_source
#print axioms sieveRootPart_source
#print axioms sieveFaceArray_divisor_source
#print axioms sieveFaceArray_coefficient_source

end TrialSmoothProfiles182
end PrimeGap182
