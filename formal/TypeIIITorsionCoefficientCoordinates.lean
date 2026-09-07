import TypeIIITorsionCoefficientLimit
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Coordinates of the actual inverse-limit coefficient ring

The existing monomial bases commute with the actual reduction maps.
The compatible maps from the p-adic integers (with p replaced here by ℓ)
give a scalar map into the existing inverse-limit ring.  Compatible
finite coordinates lift to ℓ-adic coordinates, identifying its underlying
module with ℤ_[ℓ]^(p-1).  This is a module equivalence, not a product-ring
decomposition.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped Classical

/-- Reduction carries the actual monomial expansion to the expansion
whose coefficients have been reduced. -/
theorem torsionCoefficientReduce_basisCombination (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] {m n : ℕ} (hmn : m ≤ n)
    (v : Fin (p - 1) → TorsionCoefficientBase ell n) :
    torsionCoefficientReduce p ell hmn ((torsionCoefficientBasis p ell n).equivFun.symm v) =
      (torsionCoefficientBasis p ell m).equivFun.symm
        (fun i => torsionCoefficientBaseReduce ell hmn (v i)) := by
  simp only [Module.Basis.equivFun_symm_apply, Algebra.smul_def,
    torsionCoefficientBasis_apply, map_sum, map_mul, map_pow,
    torsionCoefficientReduce_root, torsionCoefficientReduce_algebraMap]

/-- Coordinates in the existing finite bases commute with the actual
coefficient reduction. -/
theorem torsionCoefficientReduce_coordinates (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] {m n : ℕ} (hmn : m ≤ n)
    (x : TorsionCoefficientRing p ell n) (i : Fin (p - 1)) :
    (torsionCoefficientBasis p ell m).equivFun (torsionCoefficientReduce p ell hmn x) i =
      torsionCoefficientBaseReduce ell hmn ((torsionCoefficientBasis p ell n).equivFun x i) := by
  have h := torsionCoefficientReduce_basisCombination p ell hmn
    ((torsionCoefficientBasis p ell n).equivFun x)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h, LinearEquiv.apply_symm_apply]

/-- The actual ℓ-adic scalar map into the already defined inverse limit. -/
def torsionCoefficientLimitPadicHom (p ell : ℕ) [Fact ell.Prime] :
    ℤ_[ell] →+* TorsionCoefficientLimit p ell :=
  torsionCoefficientLimitLift p ell
    (fun n => (algebraMap (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n)).comp
      (PadicInt.toZModPow (p := ell) (n + 1))) (by
        intro m n hmn
        apply RingHom.ext
        intro a
        simp only [RingHom.comp_apply, torsionCoefficientReduce_algebraMap]
        exact congrArg (algebraMap (TorsionCoefficientBase ell m)
          (TorsionCoefficientRing p ell m))
          (RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow
            (p := ell) (m + 1) (n + 1) (Nat.add_le_add_right hmn 1)) a))

/-- Its projection is the existing finite base inclusion after ℓ-adic reduction. -/
@[simp] theorem torsionCoefficientLimitProjection_padicHom (p ell n : ℕ)
    [Fact ell.Prime] (a : ℤ_[ell]) :
    torsionCoefficientLimitProjection p ell n (torsionCoefficientLimitPadicHom p ell a) =
      algebraMap (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n)
        (PadicInt.toZModPow (p := ell) (n + 1) a) := rfl

/-- The module structure is induced by the actual compatible scalar map. -/
instance torsionCoefficientLimit_padicAlgebra (p ell : ℕ) [Fact ell.Prime] :
    Algebra ℤ_[ell] (TorsionCoefficientLimit p ell) :=
  (torsionCoefficientLimitPadicHom p ell).toAlgebra

@[simp] theorem torsionCoefficientLimit_algebraMap (p ell : ℕ) [Fact ell.Prime] :
    algebraMap ℤ_[ell] (TorsionCoefficientLimit p ell) =
      torsionCoefficientLimitPadicHom p ell := rfl

/-- Integer representatives of compatible residues, with the unique
residue modulo ℓ^0 supplied at index zero. -/
def torsionCoefficientResidueIntSeq (ell : ℕ)
    (a : ∀ n, TorsionCoefficientBase ell n) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (a n).val

/-- Compatibility gives the divisibility needed for an actual ℓ-adic
Cauchy sequence of the integer representatives. -/
theorem torsionCoefficientResidueIntSeq_dvd (ell : ℕ) [Fact ell.Prime]
    (a : ∀ n, TorsionCoefficientBase ell n)
    (ha : ∀ (m n : ℕ) (hmn : m ≤ n), torsionCoefficientBaseReduce ell hmn (a n) = a m)
    (i : ℕ) :
    (ell : ℤ) ^ i ∣ torsionCoefficientResidueIntSeq ell a (i + 1) -
      torsionCoefficientResidueIntSeq ell a i := by
  cases i with
  | zero => simp [torsionCoefficientResidueIntSeq]
  | succ i =>
    change (ell : ℤ) ^ (i + 1) ∣ ((a (i + 1)).val : ℤ) - (a i).val
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_natCast]
    have hcast : ((a (i + 1)).val : TorsionCoefficientBase ell i) = a i := by
      calc
        _ = torsionCoefficientBaseReduce ell (Nat.le_succ i)
            ((a (i + 1)).val : TorsionCoefficientBase ell (i + 1)) :=
          (map_natCast (torsionCoefficientBaseReduce ell (Nat.le_succ i)) _).symm
        _ = a i := by rw [ZMod.natCast_zmod_val, ha]
    rw [hcast, ZMod.natCast_zmod_val, sub_self]

/-- The actual ℓ-adic limit of compatible finite residues. -/
def torsionCoefficientResidueLift (ell : ℕ) [Fact ell.Prime]
    (a : ∀ n, TorsionCoefficientBase ell n)
    (ha : ∀ (m n : ℕ) (hmn : m ≤ n), torsionCoefficientBaseReduce ell hmn (a n) = a m) :
    ℤ_[ell] :=
  PadicInt.ofIntSeq (torsionCoefficientResidueIntSeq ell a)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ ell
      (torsionCoefficientResidueIntSeq_dvd ell a ha))

/-- Every prescribed residue is the corresponding residue of the constructed limit. -/
@[simp] theorem torsionCoefficientResidueLift_spec (ell : ℕ) [Fact ell.Prime]
    (a : ∀ n, TorsionCoefficientBase ell n)
    (ha : ∀ (m n : ℕ) (hmn : m ≤ n), torsionCoefficientBaseReduce ell hmn (a n) = a m)
    (n : ℕ) :
    PadicInt.toZModPow (p := ell) (n + 1) (torsionCoefficientResidueLift ell a ha) = a n := by
  simpa only [torsionCoefficientResidueLift, torsionCoefficientResidueIntSeq,
    Int.cast_natCast, ZMod.natCast_zmod_val] using
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (torsionCoefficientResidueIntSeq ell a) ell
      (torsionCoefficientResidueIntSeq_dvd ell a ha) (n + 1)

/-- A coordinate of an element of the existing ring, lifted from its
compatible coordinates in the existing finite bases. -/
def torsionCoefficientLimitCoordinate (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (x : TorsionCoefficientLimit p ell) (i : Fin (p - 1)) : ℤ_[ell] :=
  torsionCoefficientResidueLift ell
    (fun n => (torsionCoefficientBasis p ell n).equivFun
      (torsionCoefficientLimitProjection p ell n x) i) (by
        intro m n hmn
        rw [← torsionCoefficientReduce_coordinates]
        exact congrArg (fun y => (torsionCoefficientBasis p ell m).equivFun y i)
          (x.property m n hmn))

/-- The constructed ℓ-adic coordinate has exactly the original finite coordinates. -/
@[simp] theorem torsionCoefficientLimitCoordinate_spec (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (x : TorsionCoefficientLimit p ell) (i : Fin (p - 1)) :
    PadicInt.toZModPow (p := ell) (n + 1) (torsionCoefficientLimitCoordinate p ell x i) =
      (torsionCoefficientBasis p ell n).equivFun
        (torsionCoefficientLimitProjection p ell n x) i :=
  torsionCoefficientResidueLift_spec ell _ _ n

/-- Actual finite linear combination of powers of the limit's distinguished root. -/
def torsionCoefficientLimitCombination (p ell : ℕ) [Fact ell.Prime] :
    (Fin (p - 1) → ℤ_[ell]) →ₗ[ℤ_[ell]] TorsionCoefficientLimit p ell where
  toFun v := ∑ i, v i • torsionCoefficientLimitRoot p ell ^ (i : ℕ)
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Projecting the actual linear combination gives the original finite monomial expansion. -/
theorem torsionCoefficientLimitProjection_combination (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (v : Fin (p - 1) → ℤ_[ell]) :
    torsionCoefficientLimitProjection p ell n (torsionCoefficientLimitCombination p ell v) =
      (torsionCoefficientBasis p ell n).equivFun.symm
        (fun i => PadicInt.toZModPow (p := ell) (n + 1) (v i)) := by
  change torsionCoefficientLimitProjection p ell n
    (∑ i, v i • torsionCoefficientLimitRoot p ell ^ (i : ℕ)) = _
  simp only [Module.Basis.equivFun_symm_apply, Algebra.smul_def, map_sum,
    map_mul, map_pow, torsionCoefficientLimitProjection_root,
    torsionCoefficientLimit_algebraMap, torsionCoefficientLimitProjection_padicHom,
    torsionCoefficientBasis_apply]

/-- The finite coordinates of a linear combination are its reduced ℓ-adic coefficients. -/
@[simp] theorem torsionCoefficientLimitCombination_coordinates (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (v : Fin (p - 1) → ℤ_[ell]) (i : Fin (p - 1)) :
    (torsionCoefficientBasis p ell n).equivFun
        (torsionCoefficientLimitProjection p ell n (torsionCoefficientLimitCombination p ell v)) i =
      PadicInt.toZModPow (p := ell) (n + 1) (v i) := by
  rw [torsionCoefficientLimitProjection_combination, LinearEquiv.apply_symm_apply]

/-- The original limit element is reconstructed from the lifted coordinates. -/
theorem torsionCoefficientLimitCombination_coordinate (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (x : TorsionCoefficientLimit p ell) :
    torsionCoefficientLimitCombination p ell (torsionCoefficientLimitCoordinate p ell x) = x := by
  apply torsionCoefficientLimit_ext
  intro n
  apply (torsionCoefficientBasis p ell n).equivFun.injective
  funext i
  rw [torsionCoefficientLimitCombination_coordinates, torsionCoefficientLimitCoordinate_spec]

/-- Uniqueness of all ℓ-adic residues proves uniqueness of the coefficients. -/
theorem torsionCoefficientLimitCombination_injective (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    Function.Injective (torsionCoefficientLimitCombination p ell) := by
  intro v w h
  funext i
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    let : Subsingleton (ZMod (ell ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have hn := congrArg (fun x => (torsionCoefficientBasis p ell n).equivFun
      (torsionCoefficientLimitProjection p ell n x) i) h
    simpa only [torsionCoefficientLimitCombination_coordinates] using hn

/-- Every compatible sequence has actual ℓ-adic monomial coordinates. -/
theorem torsionCoefficientLimitCombination_surjective (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    Function.Surjective (torsionCoefficientLimitCombination p ell) :=
  fun x => ⟨torsionCoefficientLimitCoordinate p ell x,
    torsionCoefficientLimitCombination_coordinate p ell x⟩

/-- A linear equivalence for the actual limit ring, not a ring-product identification. -/
def torsionCoefficientLimitEquivFun (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] :
    TorsionCoefficientLimit p ell ≃ₗ[ℤ_[ell]] (Fin (p - 1) → ℤ_[ell]) :=
  (LinearEquiv.ofBijective (torsionCoefficientLimitCombination p ell)
    ⟨torsionCoefficientLimitCombination_injective p ell,
      torsionCoefficientLimitCombination_surjective p ell⟩).symm

@[simp] theorem torsionCoefficientLimitEquivFun_symm_apply (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (v : Fin (p - 1) → ℤ_[ell]) :
    (torsionCoefficientLimitEquivFun p ell).symm v =
      torsionCoefficientLimitCombination p ell v := rfl

/-- Reduction of the linear coordinates agrees with the original projection and basis. -/
@[simp] theorem torsionCoefficientLimitEquivFun_projection (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (x : TorsionCoefficientLimit p ell) (i : Fin (p - 1)) :
    PadicInt.toZModPow (p := ell) (n + 1) (torsionCoefficientLimitEquivFun p ell x i) =
      (torsionCoefficientBasis p ell n).equivFun
        (torsionCoefficientLimitProjection p ell n x) i := by
  have h := torsionCoefficientLimitCombination_coordinates p ell n
    (torsionCoefficientLimitEquivFun p ell x) i
  rw [← torsionCoefficientLimitEquivFun_symm_apply, LinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- The coordinates of the linear equivalence are the actual limits of finite coordinates. -/
theorem torsionCoefficientLimitEquivFun_apply (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (x : TorsionCoefficientLimit p ell) :
    torsionCoefficientLimitEquivFun p ell x = torsionCoefficientLimitCoordinate p ell x := by
  apply torsionCoefficientLimitCombination_injective p ell
  rw [← torsionCoefficientLimitEquivFun_symm_apply, LinearEquiv.symm_apply_apply,
    torsionCoefficientLimitCombination_coordinate]

/-- The resulting finite basis of the existing limit ring over ℤ_[ℓ]. -/
def torsionCoefficientLimitBasis (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] :
    Module.Basis (Fin (p - 1)) ℤ_[ell] (TorsionCoefficientLimit p ell) :=
  Module.Basis.ofEquivFun (torsionCoefficientLimitEquivFun p ell)

/-- Its vectors are the unchanged powers of the actual compatible cyclotomic root. -/
theorem torsionCoefficientLimitBasis_apply (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (i : Fin (p - 1)) :
    torsionCoefficientLimitBasis p ell i = torsionCoefficientLimitRoot p ell ^ (i : ℕ) := by
  rw [torsionCoefficientLimitBasis, Module.Basis.coe_ofEquivFun]
  change torsionCoefficientLimitCombination p ell (Pi.single i 1) = _
  simp [torsionCoefficientLimitCombination, Pi.single_apply]

instance torsionCoefficientLimit_moduleFree (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] :
    Module.Free ℤ_[ell] (TorsionCoefficientLimit p ell) :=
  Module.Free.of_basis (torsionCoefficientLimitBasis p ell)

instance torsionCoefficientLimit_moduleFinite (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] :
    Module.Finite ℤ_[ell] (TorsionCoefficientLimit p ell) :=
  Module.Finite.of_basis (torsionCoefficientLimitBasis p ell)

/-- The actual free module has rank p-1. -/
theorem torsionCoefficientLimit_finrank (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] :
    Module.finrank ℤ_[ell] (TorsionCoefficientLimit p ell) = p - 1 := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (torsionCoefficientLimitBasis p ell)

#print axioms torsionCoefficientReduce_basisCombination
#print axioms torsionCoefficientReduce_coordinates
#print axioms torsionCoefficientLimitPadicHom
#print axioms torsionCoefficientLimitProjection_padicHom
#print axioms torsionCoefficientLimit_padicAlgebra
#print axioms torsionCoefficientLimit_algebraMap
#print axioms torsionCoefficientResidueIntSeq
#print axioms torsionCoefficientResidueIntSeq_dvd
#print axioms torsionCoefficientResidueLift
#print axioms torsionCoefficientResidueLift_spec
#print axioms torsionCoefficientLimitCoordinate
#print axioms torsionCoefficientLimitCoordinate_spec
#print axioms torsionCoefficientLimitCombination
#print axioms torsionCoefficientLimitProjection_combination
#print axioms torsionCoefficientLimitCombination_coordinates
#print axioms torsionCoefficientLimitCombination_coordinate
#print axioms torsionCoefficientLimitCombination_injective
#print axioms torsionCoefficientLimitCombination_surjective
#print axioms torsionCoefficientLimitEquivFun
#print axioms torsionCoefficientLimitEquivFun_symm_apply
#print axioms torsionCoefficientLimitEquivFun_projection
#print axioms torsionCoefficientLimitEquivFun_apply
#print axioms torsionCoefficientLimitBasis
#print axioms torsionCoefficientLimitBasis_apply
#print axioms torsionCoefficientLimit_moduleFree
#print axioms torsionCoefficientLimit_moduleFinite
#print axioms torsionCoefficientLimit_finrank

end PrimeGap182.TypeIII
