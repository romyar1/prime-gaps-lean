import IncidencePeriodicPoisson
import IncidenceSquarefreeCompletion

/-!
# Integer lifts of the two-dimensional finite Fourier grid

The equivalence here is built from integer division with remainder. It
identifies each residue and its aliases with exactly one integer pair;
the frequency gcd is preserved under this identification.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

variable {q : ℕ} [NeZero q]

def incidenceIntegerQuotientEquiv (q : ℕ) [NeZero q] : ℤ ≃ ℤ × ZMod q :=
  (Int.divModEquiv q).trans (Equiv.prodCongr (Equiv.refl ℤ) (ZMod.finEquiv q).toEquiv)

theorem incidenceIntegerQuotientEquiv_symm (n : ℤ) (ξ : ZMod q) :
    (incidenceIntegerQuotientEquiv q).symm (n, ξ) = n * (q : ℤ) + (ξ.val : ℤ) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

def incidenceAliasEquiv (q : ℕ) [NeZero q] :
    (ℤ × ℤ) ≃ (ℤ × ℤ) × (ZMod q × ZMod q) :=
  (Equiv.prodCongr (incidenceIntegerQuotientEquiv q) (incidenceIntegerQuotientEquiv q)).trans
    (Equiv.prodProdProdComm ℤ (ZMod q) ℤ (ZMod q))

def incidenceAliasIndex (q : ℕ) (z : ℤ × ℤ) (ξ : ZMod q × ZMod q) : ℤ × ℤ :=
  (z.1 * (q : ℤ) + (ξ.1.val : ℤ), z.2 * (q : ℤ) + (ξ.2.val : ℤ))

theorem incidenceAliasEquiv_symm (z : ℤ × ℤ) (ξ : ZMod q × ZMod q) :
    (incidenceAliasEquiv q).symm (z, ξ) = incidenceAliasIndex q z ξ := by
  change ((incidenceIntegerQuotientEquiv q).symm (z.1, ξ.1),
    (incidenceIntegerQuotientEquiv q).symm (z.2, ξ.2)) = _
  rw [incidenceIntegerQuotientEquiv_symm, incidenceIntegerQuotientEquiv_symm]
  rfl

theorem incidenceAliasEquiv_symm_apply (p : (ℤ × ℤ) × (ZMod q × ZMod q)) :
    (incidenceAliasEquiv q).symm p = incidenceAliasIndex q p.1 p.2 :=
  incidenceAliasEquiv_symm p.1 p.2

theorem incidenceAliasIndex_residue (z : ℤ × ℤ) (ξ : ZMod q × ZMod q) :
    incidenceIntegerResidue q (incidenceAliasIndex q z ξ) = ξ := by
  ext <;> simp only [incidenceAliasIndex, incidenceIntegerResidue, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, zero_add,
    ZMod.natCast_zmod_val]

theorem incidenceAliasIndex_first_div (z : ℤ × ℤ) (ξ : ZMod q × ZMod q) :
    ((incidenceAliasIndex q z ξ).1 : ℝ) / q = (z.1 : ℝ) + (ξ.1.val : ℝ) / q := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [incidenceAliasIndex, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    add_div, mul_div_cancel_right₀ _ hq]

theorem incidenceAliasIndex_second_div (z : ℤ × ℤ) (ξ : ZMod q × ZMod q) :
    ((incidenceAliasIndex q z ξ).2 : ℝ) / q = (z.2 : ℝ) + (ξ.2.val : ℝ) / q := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [incidenceAliasIndex, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    add_div, mul_div_cancel_right₀ _ hq]

private theorem incidence_gcd_residue_one (h : ℤ) :
    Nat.gcd q (h : ZMod q).val = Nat.gcd q h.natAbs := by
  have hg := Int.gcd_emod h (q : ℤ)
  rw [← ZMod.val_intCast] at hg
  simpa only [Int.gcd_def, Int.natAbs_natCast, Nat.gcd_comm] using hg

/-- The gcd in the finite-mode estimate is exactly the gcd of every integer lift. -/
theorem incidenceFrequencyGCD_integer (z : ℤ × ℤ) :
    incidenceFrequencyGCD (incidenceIntegerResidue q z) = Nat.gcd q (Int.gcd z.1 z.2) := by
  simp only [incidenceFrequencyGCD, incidenceIntegerResidue, Int.gcd_def]
  rw [← Nat.gcd_gcd_gcd_left, incidence_gcd_residue_one, incidence_gcd_residue_one,
    Nat.gcd_gcd_gcd_left]

theorem incidenceAliasIndex_gcd (z : ℤ × ℤ) (ξ : ZMod q × ZMod q) :
    Nat.gcd q (Int.gcd (incidenceAliasIndex q z ξ).1 (incidenceAliasIndex q z ξ).2) =
      incidenceFrequencyGCD ξ := by
  rw [← incidenceFrequencyGCD_integer, incidenceAliasIndex_residue]

theorem incidenceAliasIndex_ne_zero (z : ℤ × ℤ) (ξ : ZMod q × ZMod q) (hξ : ξ ≠ 0) :
    incidenceAliasIndex q z ξ ≠ 0 := by
  intro hz
  have h := incidenceAliasIndex_residue z ξ
  rw [hz] at h
  apply hξ
  exact h.symm.trans (by ext <;> simp [incidenceIntegerResidue])

set_option maxHeartbeats 600000 in
/-- Reindexing a summable integer-pair function by all residues and all aliases. -/
theorem incidenceAlias_tsum {M : Type*} [NormedAddCommGroup M] [CompleteSpace M]
    (F : ℤ × ℤ → M) (hF : Summable F) :
    (∑ ξ : ZMod q × ZMod q, ∑' z : ℤ × ℤ, F (incidenceAliasIndex q z ξ)) = ∑' z, F z := by
  have hp : Summable (fun p : (ℤ × ℤ) × (ZMod q × ZMod q) =>
      F (incidenceAliasIndex q p.1 p.2)) := by
    simpa only [Function.comp_def, incidenceAliasEquiv_symm_apply] using
      (incidenceAliasEquiv q).symm.summable_iff.mpr hF
  calc
    _ = ∑' z : ℤ × ℤ, ∑' ξ : ZMod q × ZMod q, F (incidenceAliasIndex q z ξ) := by
      simpa only [tsum_fintype] using
        hp.tsum_comm (f := fun z ξ => F (incidenceAliasIndex q z ξ))
    _ = ∑' p : (ℤ × ℤ) × (ZMod q × ZMod q), F (incidenceAliasIndex q p.1 p.2) :=
      hp.tsum_prod.symm
    _ = _ := by
      simpa only [incidenceAliasEquiv_symm_apply] using (incidenceAliasEquiv q).symm.tsum_eq F

#print axioms incidenceAliasEquiv_symm
#print axioms incidenceAliasIndex_residue
#print axioms incidenceFrequencyGCD_integer
#print axioms incidenceAliasIndex_gcd
#print axioms incidenceAliasIndex_ne_zero
#print axioms incidenceAlias_tsum

end PrimeGap182Audit
