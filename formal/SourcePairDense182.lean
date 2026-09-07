import SourceIntegerSupport182
import SourceModulusClasses182

/-! Each possible pair of integer sources yields a modulus in the
appropriate recorded distribution class, including the presieve. -/

noncomputable section
open PrimeGap186
open scoped BigOperators

namespace PrimeGap182

theorem logSize_lcm_le_source_sum {R S T : ℝ} (hR : 1 < R) {D E : ℕ}
    (hD : Squarefree D) (hE : Squarefree E) (hS : logSize R D ≤ S) (hT : logSize R E ≤ T) :
    logSize R (D.lcm E) ≤ S + T := by
  have hD0 := Nat.pos_of_ne_zero hD.ne_zero
  have hE0 := Nat.pos_of_ne_zero hE.ne_zero
  calc
    logSize R (D.lcm E) ≤ logSize R (D * E) :=
      Real.logb_le_logb_of_le hR (Nat.cast_pos.mpr (Nat.lcm_pos hD0 hE0))
        (Nat.cast_le.mpr (Nat.lcm_le_mul hD0 hE0))
    _ = logSize R D + logSize R E := by
      dsimp only [logSize]
      rw [Nat.cast_mul, Real.logb_mul (Nat.cast_ne_zero.mpr hD.ne_zero)
        (Nat.cast_ne_zero.mpr hE.ne_zero)]
    _ ≤ S + T := add_le_add hS hT

def trialLadderInnerKind (ν : Fin 2) : Fin 4 := if ν = 0 then 1 else 2

theorem trialLadderInner_radius (ν : Fin 2) :
    trialIntegerRadius (trialLadderInnerKind ν) = trialSourceInnerRadius ν := by fin_cases ν <;> rfl

theorem trialLadderRow_outer (ν : Fin 2) (row : TrialSourceRow) (hr : row ∈ trialSourceRows ν) :
    row ∈ trialIntegerOuterRows 0 := by
  change row ∈ trialOldSourceRows ++ trialNewSourceRows
  fin_cases ν
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ hr

theorem trialLadderRow_inner (ν : Fin 2) (row : TrialSourceRow) (hr : row ∈ trialSourceRows ν) :
    row ∈ trialIntegerInnerRows (trialLadderInnerKind ν) := by
  fin_cases ν
  · exact List.mem_append_left _ hr
  · exact hr

theorem trialInteger_ladder_modulus (ν : Fin 2) (x : ℝ) (hx : 1 < x) (W D E : ℕ)
    (hW : 0 < W) (hWs : (W : ℝ) ≤ x ^ (trialPresieveExponent : ℝ))
    (hDW : D.Coprime W) (hEW : E.Coprime W)
    (ho : TrialIntegerSupport 0 (x ^ (trialRhoStar : ℝ)) D)
    (hi : TrialIntegerSupport (trialLadderInnerKind ν) (x ^ (trialRhoStar : ℝ)) E) :
    (W.lcm (D.lcm E) : ℝ) ≤ x ^ (trialBaseModulusExponent : ℝ) ∨
      ∃ row ∈ trialSourceRows ν,
        TrialDenseModulus182 row.order row.omega row.delta x (W.lcm (D.lcm E)) := by
  let R := x ^ (trialRhoStar : ℝ)
  have hR : 1 < R := Real.one_lt_rpow hx (by norm_num [trialRhoStar])
  have hq0 : 0 < D.lcm E := Nat.lcm_pos
    (Nat.pos_of_ne_zero ho.squarefree.ne_zero) (Nat.pos_of_ne_zero hi.squarefree.ne_zero)
  have hT : logSize R E ≤ (trialSourceInnerRadius ν : ℝ) := by
    simpa only [trialLadderInner_radius] using hi.radius
  by_cases hbase : (D.lcm E : ℝ) ≤ R ^ (((1 / 2) / trialRho : ℚ) : ℝ)
  · exact Or.inl (trialBaseModulus_presieve x hx W _ hW hq0 hWs hbase)
  right
  have hlo : (((1 / 2) / trialRho : ℚ) : ℝ) < logSize R (D.lcm E) :=
    (Real.lt_logb_iff_rpow_lt hR (Nat.cast_pos.mpr hq0)).mpr (lt_of_not_ge hbase)
  have hhi : logSize R (D.lcm E) ≤ ((trialRadius + trialSourceInnerRadius ν : ℚ) : ℝ) := by
    have hS : logSize R D ≤ (trialRadius : ℝ) := ho.radius
    simpa only [Rat.cast_add] using logSize_lcm_le_source_sum hR ho.squarefree hi.squarefree hS hT
  obtain ⟨row, hr, hl, hu⟩ := (trialSourceRows_cover ν).exists_band _ hlo hhi
  have hband := (Real.lt_logb_iff_rpow_lt hR (Nat.cast_pos.mpr hq0)).mp hl
  have hupper := (Real.logb_le_iff_le_rpow hR (Nat.cast_pos.mpr hq0)).mp hu
  have hdense := trialSourceRow_lcm_dense row trialRadius (trialSourceInnerRadius ν)
    (trialSourceRows_geometry ν row hr) R hR D E ho.squarefree hi.squarefree ho.radius hT
    (ho.outer row (trialLadderRow_outer ν row hr)) (hi.inner row (trialLadderRow_inner ν row hr)) hband
  exact ⟨row, hr, trialDenseModulus_presieve row.order row.upperBand row.activation row.omega row.delta
    (trialSourceRows_presieve_retreat ν row hr) x hx W D E hW hWs hDW hEW hdense hupper⟩

theorem trialInteger_common_modulus (x : ℝ) (hx : 1 < x) (W D E : ℕ)
    (hW : 0 < W) (hWs : (W : ℝ) ≤ x ^ (trialPresieveExponent : ℝ))
    (hDW : D.Coprime W) (hEW : E.Coprime W)
    (ho : TrialIntegerSupport 2 (x ^ (trialRhoStar : ℝ)) D)
    (hi : TrialIntegerSupport 2 (x ^ (trialRhoStar : ℝ)) E) :
    (W.lcm (D.lcm E) : ℝ) ≤ x ^ (trialBaseModulusExponent : ℝ) ∨
      TrialDenseModulus182 2 trialCommonSourceOmega trialCommonSourceDelta x (W.lcm (D.lcm E)) := by
  let R := x ^ (trialRhoStar : ℝ)
  have hR : 1 < R := Real.one_lt_rpow hx (by norm_num [trialRhoStar])
  have hq0 : 0 < D.lcm E := Nat.lcm_pos
    (Nat.pos_of_ne_zero ho.squarefree.ne_zero) (Nat.pos_of_ne_zero hi.squarefree.ne_zero)
  by_cases hbase : (D.lcm E : ℝ) ≤ R ^ (((1 / 2) / trialRho : ℚ) : ℝ)
  · exact Or.inl (trialBaseModulus_presieve x hx W _ hW hq0 hWs hbase)
  right
  have hdense := trialCommonSource_lcm_dense R hR D E ho.squarefree hi.squarefree ho.radius hi.radius
    (ho.inner trialCommonInnerRow trialCommonInnerRow_mem)
    (hi.inner trialCommonInnerRow trialCommonInnerRow_mem) (lt_of_not_ge hbase)
  have hupper : (D.lcm E : ℝ) ≤ R ^ ((2 * trialEnlargedRadius : ℚ) : ℝ) := by
    apply (Real.logb_le_iff_le_rpow hR (Nat.cast_pos.mpr hq0)).mp
    have hh := logSize_lcm_le_source_sum hR ho.squarefree hi.squarefree ho.radius hi.radius
    change logSize R (D.lcm E) ≤ (trialEnlargedRadius : ℝ) + (trialEnlargedRadius : ℝ) at hh
    simpa only [logSize, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, two_mul] using hh
  exact trialDenseModulus_presieve 2 (2 * trialEnlargedRadius) (trialCommonSourceDelta / trialRho)
    trialCommonSourceOmega trialCommonSourceDelta trialOtherSources_presieve_retreat.1 x hx W D E
    hW hWs hDW hEW hdense hupper

theorem trialInteger_subtraction_modulus (x : ℝ) (hx : 1 < x) (W D E : ℕ)
    (hW : 0 < W) (hWs : (W : ℝ) ≤ x ^ (trialPresieveExponent : ℝ))
    (hDW : D.Coprime W) (hEW : E.Coprime W)
    (ho : TrialIntegerSupport 3 (x ^ (trialRhoStar : ℝ)) D)
    (hi : TrialIntegerSupport 2 (x ^ (trialRhoStar : ℝ)) E) :
    (W.lcm (D.lcm E) : ℝ) ≤ x ^ (trialBaseModulusExponent : ℝ) ∨
      TrialDenseModulus182 2 trialSubtractionSourceRow.omega trialSubtractionSourceRow.delta
        x (W.lcm (D.lcm E)) := by
  let R := x ^ (trialRhoStar : ℝ)
  have hR : 1 < R := Real.one_lt_rpow hx (by norm_num [trialRhoStar])
  have hq0 : 0 < D.lcm E := Nat.lcm_pos
    (Nat.pos_of_ne_zero ho.squarefree.ne_zero) (Nat.pos_of_ne_zero hi.squarefree.ne_zero)
  by_cases hbase : (D.lcm E : ℝ) ≤ R ^ (((1 / 2) / trialRho : ℚ) : ℝ)
  · exact Or.inl (trialBaseModulus_presieve x hx W _ hW hq0 hWs hbase)
  right
  have hirow := trialSubtractionSource_inner_owner R hR E
    (hi.inner trialCommonInnerRow trialCommonInnerRow_mem)
  have hdense := trialSourceRow_lcm_dense trialSubtractionSourceRow trialSubtractionRadius
    trialEnlargedRadius trialSubtractionSource_geometry.1 R hR D E ho.squarefree hi.squarefree
    ho.radius hi.radius (ho.outer trialSubtractionSourceRow (by simp [trialIntegerOuterRows])) hirow
    (lt_of_not_ge hbase)
  have hupper : (D.lcm E : ℝ) ≤ R ^ (trialSubtractionSourceRow.upperBand : ℝ) := by
    apply (Real.logb_le_iff_le_rpow hR (Nat.cast_pos.mpr hq0)).mp
    have hh := logSize_lcm_le_source_sum hR ho.squarefree hi.squarefree ho.radius hi.radius
    apply hh.trans
    change (trialSubtractionRadius : ℝ) + (trialEnlargedRadius : ℝ) ≤ _
    exact_mod_cast trialSubtractionSource_geometry.2.2.2.2.2.2.1
  exact trialDenseModulus_presieve 2 trialSubtractionSourceRow.upperBand
    trialSubtractionSourceRow.activation trialSubtractionSourceRow.omega trialSubtractionSourceRow.delta
    trialOtherSources_presieve_retreat.2.1 x hx W D E hW hWs hDW hEW hdense hupper

#print axioms logSize_lcm_le_source_sum
#print axioms trialInteger_ladder_modulus
#print axioms trialInteger_common_modulus
#print axioms trialInteger_subtraction_modulus

end PrimeGap182
