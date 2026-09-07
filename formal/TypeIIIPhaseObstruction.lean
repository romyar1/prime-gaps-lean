import Mathlib

/-!
# Algebraic obstruction for the Type III radial phases

This file concerns field elements and rational functions. It does not assert
that the actual correlation is the trace of a sheaf, identify its local
characters, or establish the finite-exceptional Fourier hypothesis.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open Classical Polynomial
open scoped BigOperators

set_option maxHeartbeats 2000000

section SquareRoots

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem squareRoot_aut_eq_or_neg {a : K} {v : L}
    (hv : v ^ 2 = algebraMap K L a) (σ : L ≃ₐ[K] L) :
    σ v = v ∨ σ v = -v := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, hv, AlgEquiv.commutes, ← hv]

/-- The genuine Galois sign character of a nonzero square root. -/
def squareRootSignCharacter {a : K} {v : L} (hv0 : v ≠ 0)
    (hv : v ^ 2 = algebraMap K L a) : (L ≃ₐ[K] L) →* L where
  toFun σ := σ v / v
  map_one' := by simp [hv0]
  map_mul' σ τ := by
    rcases squareRoot_aut_eq_or_neg hv τ with hτ | hτ
    · simp [AlgEquiv.mul_apply, hτ, hv0]
    · simp [AlgEquiv.mul_apply, hτ, hv0, neg_div]

theorem squareRootSignCharacter_injective [Normal K L] (h2 : (2 : L) ≠ 0)
    {ι : Type*} (a : ι → K) (v : ι → L)
    (hv0 : ∀ i, v i ≠ 0) (hv : ∀ i, v i ^ 2 = algebraMap K L (a i))
    (hclasses : Pairwise (fun i j => ¬ IsSquare (a i / a j))) :
    Function.Injective (fun i => squareRootSignCharacter (hv0 i) (hv i)) := by
  intro i j hij
  by_contra hne
  have hn := hclasses hne
  let q : L := v i / v j
  have hq0 : q ≠ 0 := div_ne_zero (hv0 i) (hv0 j)
  have hq : q ^ 2 = algebraMap K L (a i / a j) := by
    simp only [q, div_pow, hv, map_div₀]
  have hirr : Irreducible (X ^ 2 - C (a i / a j)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb =>
      hn ⟨b, by simpa only [pow_two] using hb.symm⟩)
  have hev : (aeval q) (X ^ 2 - C (a i / a j)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hq, sub_self]
  have hm : X ^ 2 - C (a i / a j) = minpoly K q :=
    minpoly.eq_of_irreducible_of_monic hirr hev (monic_X_pow_sub_C _ (by decide))
  have hqi : IsIntegral K q := ⟨_, monic_X_pow_sub_C _ (by decide), hev⟩
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hqi.isAlgebraic
    (show (aeval (-q)) (minpoly K q) = 0 by
      rw [← hm]
      simp only [map_sub, map_pow, aeval_X, aeval_C, neg_sq, hq, sub_self])
  have hsame : σ (v i) / v i = σ (v j) / v j :=
    congrArg (fun χ : (L ≃ₐ[K] L) →* L => χ σ) hij
  have hfix : σ q = q := by
    dsimp only [q]
    rw [map_div₀]
    have he := (div_eq_div_iff (hv0 i) (hv0 j)).mp hsame
    apply (div_eq_div_iff (by simpa only [map_zero] using σ.injective.ne (hv0 j)) (hv0 j)).mpr
    simpa only [mul_comm] using he
  have hqneg : q = -q := hfix.symm.trans hσ
  have : (2 : L) * q = 0 := by linear_combination hqneg
  exact (mul_ne_zero h2 hq0) this

/-- Square roots in pairwise distinct squareclasses are linearly independent.
The proof uses the actual automorphism characters and Dedekind independence. -/
theorem linearIndependent_squareRoots [Normal K L] (h2 : (2 : L) ≠ 0)
    {ι : Type*} (a : ι → K) (v : ι → L)
    (hv0 : ∀ i, v i ≠ 0) (hv : ∀ i, v i ^ 2 = algebraMap K L (a i))
    (hclasses : Pairwise (fun i j => ¬ IsSquare (a i / a j))) :
    LinearIndependent K v := by
  let χ (i : ι) := squareRootSignCharacter (hv0 i) (hv i)
  have hχ : Function.Injective χ := squareRootSignCharacter_injective h2 a v hv0 hv hclasses
  have hLI : LinearIndependent L (fun i => (χ i : (L ≃ₐ[K] L) → L)) :=
    (linearIndependent_monoidHom (L ≃ₐ[K] L) L).comp χ hχ
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  have hsumχ : ∑ j ∈ s, (algebraMap K L (c j) * v j) •
      (χ j : (L ≃ₐ[K] L) → L) = 0 := by
    ext σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    calc
      _ = ∑ j ∈ s, σ (c j • v j) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [χ, squareRootSignCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
          Algebra.smul_def, map_mul, AlgEquiv.commutes]
        field_simp [hv0 j]
      _ = σ (∑ j ∈ s, c j • v j) := (map_sum σ _ _).symm
      _ = 0 := by rw [hsum, map_zero]
  have hc := (linearIndependent_iff'.mp hLI) s
    (fun j => algebraMap K L (c j) * v j) hsumχ i hi
  exact (algebraMap K L).injective (by
    simpa only [map_zero] using (mul_eq_zero.mp hc).resolve_right (hv0 i))

end SquareRoots

section LinearFactors

variable {k ι : Type*} [Field k]

def phaseLinearProduct (γ : ι → k) (s : Finset ι) : k[X] :=
  ∏ i ∈ s, (C (γ i) - X)

theorem phaseLinearFactor_ne_zero (a : k) : C a - X ≠ 0 :=
  sub_ne_zero.mpr (X_ne_C a).symm

theorem phaseLinearProduct_ne_zero (γ : ι → k) (s : Finset ι) :
    phaseLinearProduct γ s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => phaseLinearFactor_ne_zero (γ i))

theorem phaseLinearProduct_rootMultiplicity (γ : ι → k) (hγ : Function.Injective γ)
    (s : Finset ι) (i : ι) :
    (phaseLinearProduct γ s).rootMultiplicity (γ i) = if i ∈ s then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [phaseLinearProduct, Finset.prod_empty, C_1, Finset.notMem_empty, ite_false]
      using rootMultiplicity_C (1 : k) (γ i)
  | @insert j s hj ih =>
    have hf : (C (γ j) - X : k[X]).rootMultiplicity (γ i) = if i = j then 1 else 0 := by
      rw [show C (γ j) - X = C (-1 : k) * (X - C (γ j)) by simp]
      rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))
        (X_sub_C_ne_zero _)), rootMultiplicity_C, zero_add,
        rootMultiplicity_X_sub_C, hγ.eq_iff]
    rw [phaseLinearProduct, Finset.prod_insert hj]
    change ((C (γ j) - X) * phaseLinearProduct γ s).rootMultiplicity (γ i) = _
    rw [rootMultiplicity_mul
      (mul_ne_zero (phaseLinearFactor_ne_zero _) (phaseLinearProduct_ne_zero γ s)), hf]
    change (if i = j then 1 else 0) + (phaseLinearProduct γ s).rootMultiplicity (γ i) = _
    rw [ih]
    by_cases hij : i = j
    · subst i
      simp [hj]
    · simp [hij]

/-- Distinct subsets of distinct linear factors represent different squareclasses
in the actual rational function field. The proof compares root multiplicities
in a cleared numerator/denominator identity. -/
theorem phaseLinearProduct_div_not_isSquare (γ : ι → k) (hγ : Function.Injective γ)
    (s t : Finset ι) (hst : s ≠ t) :
    ¬ IsSquare ((algebraMap k[X] (RatFunc k) (phaseLinearProduct γ s)) /
      (algebraMap k[X] (RatFunc k) (phaseLinearProduct γ t))) := by
  classical
  intro hsquare
  obtain ⟨q, hq⟩ := hsquare
  have hs0 := phaseLinearProduct_ne_zero γ s
  have ht0 := phaseLinearProduct_ne_zero γ t
  have hmaps : algebraMap k[X] (RatFunc k) (phaseLinearProduct γ s) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hs0
  have hmapt : algebraMap k[X] (RatFunc k) (phaseLinearProduct γ t) ≠ 0 :=
    RatFunc.algebraMap_ne_zero ht0
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hq
    exact (div_ne_zero hmaps hmapt) hq
  have hnum : q.num ≠ 0 := RatFunc.num_ne_zero hq0
  have hden : q.denom ≠ 0 := q.denom_ne_zero
  have hcleared : q.num ^ 2 * phaseLinearProduct γ t =
      q.denom ^ 2 * phaseLinearProduct γ s := by
    apply RatFunc.algebraMap_injective k
    have hqd := q.num_div_denom
    rw [← hqd] at hq
    simp only [map_mul, map_pow]
    field_simp [RatFunc.algebraMap_ne_zero hden, hmapt] at hq ⊢
    linear_combination -hq
  have hall (i : ι) :
      2 * q.num.rootMultiplicity (γ i) + (if i ∈ t then 1 else 0) =
      2 * q.denom.rootMultiplicity (γ i) + (if i ∈ s then 1 else 0) := by
    have hh := congrArg (fun P : k[X] => P.rootMultiplicity (γ i)) hcleared
    rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hnum) ht0),
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hden) hs0),
      phaseLinearProduct_rootMultiplicity γ hγ,
      phaseLinearProduct_rootMultiplicity γ hγ,
      pow_two, pow_two, rootMultiplicity_mul (mul_ne_zero hnum hnum),
      rootMultiplicity_mul (mul_ne_zero hden hden)] at hh
    omega
  apply hst
  ext i
  have hh := hall i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp_all
  all_goals omega

end LinearFactors

section PhaseSquare

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]

/-- A sum with two nonzero coefficients in distinct square-root characters
cannot have square in the base field. The conclusion is proved from genuine
Galois actions, rather than supplied as an independence assumption. -/
theorem square_sum_squareRoots_not_in_base (h2 : (2 : L) ≠ 0)
    (a : ι → K) (v : ι → L)
    (hv0 : ∀ i, v i ≠ 0) (hv : ∀ i, v i ^ 2 = algebraMap K L (a i))
    (hclasses : Pairwise (fun i j => ¬ IsSquare (a i / a j)))
    (s : Finset ι) (c : ι → K) (i j : ι) (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) (hci : c i ≠ 0) (hcj : c j ≠ 0) (b : K) :
    (∑ l ∈ s, c l • v l) ^ 2 ≠ algebraMap K L b := by
  intro hsq
  have hLI := linearIndependent_squareRoots h2 a v hv0 hv hclasses
  have hχ := squareRootSignCharacter_injective h2 a v hv0 hv hclasses
  apply hij
  apply hχ
  ext σ
  let ε (l : ι) : K := if σ (v l) = v l then 1 else -1
  have hσv (l : ι) : σ (v l) = ε l • v l := by
    dsimp only [ε]
    split_ifs with heq
    · simpa only [one_smul] using heq
    · rcases squareRoot_aut_eq_or_neg (hv l) σ with h | h
      · exact (heq h).elim
      · simpa only [neg_smul, one_smul] using h
  let S : L := ∑ l ∈ s, c l • v l
  obtain ⟨e, he⟩ : ∃ e : K, σ S = e • S := by
    rcases squareRoot_aut_eq_or_neg hsq σ with h | h
    · exact ⟨1, by simpa only [one_smul, S] using h⟩
    · exact ⟨-1, by simpa only [neg_smul, one_smul, S] using h⟩
  have hsum0 : (∑ l ∈ s, c l • (ε l • v l)) - e • S = 0 := by
    calc
      _ = σ S - e • S := by
        congr 1
        dsimp only [S]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro l _
        simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes, hσv]
      _ = 0 := sub_eq_zero.mpr he
  have hsum : ∑ l ∈ s, (c l * (ε l - e)) • v l = 0 := by
    convert hsum0 using 1
    dsimp only [S]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    simp only [smul_smul, mul_sub, sub_smul, mul_comm (c l) e]
  have hei : ε i = e := sub_eq_zero.mp
    ((mul_eq_zero.mp ((linearIndependent_iff'.mp hLI) s
      (fun l => c l * (ε l - e)) hsum i hi)).resolve_left hci)
  have hej : ε j = e := sub_eq_zero.mp
    ((mul_eq_zero.mp ((linearIndependent_iff'.mp hLI) s
      (fun l => c l * (ε l - e)) hsum j hj)).resolve_left hcj)
  change σ (v i) / v i = σ (v j) / v j
  rw [hσv i, hσv j, Algebra.smul_def, Algebra.smul_def, hei, hej]
  simp only [mul_div_cancel_right₀ _ (hv0 i), mul_div_cancel_right₀ _ (hv0 j)]

end PhaseSquare

section RationalPhases

variable {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]

/-- The rational coefficient of a chosen square root of `γ - z` in
`c (γ - z)^(3/2) / z`. -/
def radialPhaseScalar (c γ : k) : RatFunc k :=
  RatFunc.C c * (RatFunc.C γ - RatFunc.X) / RatFunc.X

/-- The literal finite phase sum, with the square-root choices explicit. -/
def radialPhase (Γ : Finset k) (c : k → k) (v : k → L) : L :=
  ∑ γ ∈ Γ, radialPhaseScalar (c γ) γ • v γ

theorem ratFunc_linearFactor_ne_zero (γ : k) :
    RatFunc.C γ - (RatFunc.X : RatFunc k) ≠ 0 := by
  simpa only [map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    using RatFunc.algebraMap_ne_zero (phaseLinearFactor_ne_zero γ)

theorem radialPhaseScalar_ne_zero {c : k} (hc : c ≠ 0) (γ : k) :
    radialPhaseScalar c γ ≠ 0 := by
  exact div_ne_zero (mul_ne_zero
    (by simpa only [map_zero] using RatFunc.C_injective.ne hc)
    (ratFunc_linearFactor_ne_zero γ)) RatFunc.X_ne_zero

theorem ratFunc_linearFactor_distinct_squareclasses :
    Pairwise (fun γ δ : k => ¬ IsSquare
      ((RatFunc.C γ - RatFunc.X) / (RatFunc.C δ - RatFunc.X))) := by
  intro γ δ hγδ
  simpa only [phaseLinearProduct, Finset.prod_singleton,
    map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X] using
    phaseLinearProduct_div_not_isSquare (fun x : k => x) Function.injective_id
      {γ} {δ} (by simpa only [ne_eq, Finset.singleton_inj] using hγδ)

theorem radialPhase_square_not_rational [Normal (RatFunc k) L]
    (h2 : (2 : L) ≠ 0) (Γ : Finset k) (c : k → k) (v : k → L)
    (hv : ∀ γ, v γ ^ 2 = algebraMap (RatFunc k) L (RatFunc.C γ - RatFunc.X))
    (γ δ : k) (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) (hγδ : γ ≠ δ)
    (hcγ : c γ ≠ 0) (hcδ : c δ ≠ 0) (b : RatFunc k) :
    radialPhase Γ c v ^ 2 ≠ algebraMap (RatFunc k) L b := by
  apply square_sum_squareRoots_not_in_base h2
    (fun x : k => RatFunc.C x - RatFunc.X) v
    (fun x hx => ?_) hv ratFunc_linearFactor_distinct_squareclasses
    Γ (fun x => radialPhaseScalar (c x) x) γ δ hγ hδ hγδ
    (radialPhaseScalar_ne_zero hcγ γ) (radialPhaseScalar_ne_zero hcδ δ) b
  have h := hv x
  rw [hx, zero_pow (by decide)] at h
  exact (ratFunc_linearFactor_ne_zero x)
    ((algebraMap (RatFunc k) L).injective (by simpa only [map_zero] using h.symm))

theorem radialPhase_singleton_square (γ : k) (c : k → k) (v : k → L)
    (hv : v γ ^ 2 = algebraMap (RatFunc k) L (RatFunc.C γ - RatFunc.X)) :
    radialPhase {γ} c v ^ 2 = algebraMap (RatFunc k) L
      (RatFunc.C (c γ) ^ 2 * (RatFunc.C γ - RatFunc.X) ^ 3 / RatFunc.X ^ 2) := by
  simp only [radialPhase, Finset.sum_singleton, Algebra.smul_def, mul_pow, hv]
  rw [← map_pow, ← map_mul]
  congr 1
  dsimp only [radialPhaseScalar]
  rw [div_pow]
  ring

/-- The one-phase square cannot equal a reciprocal linear function. The proof
clears actual rational denominators and evaluates the resulting polynomial
identity at the nonzero root `γ`. -/
theorem singletonPhaseSquare_ne_linearReciprocal (γ c d a b : k)
    (hγ : γ ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    RatFunc.C c ^ 2 * (RatFunc.C γ - RatFunc.X) ^ 3 / RatFunc.X ^ 2 ≠
      RatFunc.C d ^ 2 / (RatFunc.C a + RatFunc.C b * RatFunc.X) := by
  intro h
  have hC : RatFunc.C c ≠ (0 : RatFunc k) :=
    by simpa only [map_zero] using RatFunc.C_injective.ne hc
  have hnum : RatFunc.C c ^ 2 * (RatFunc.C γ - RatFunc.X) ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hC) (pow_ne_zero _ (ratFunc_linearFactor_ne_zero γ))
  have hX : (RatFunc.X : RatFunc k) ^ 2 ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  by_cases hden : (RatFunc.C a + RatFunc.C b * RatFunc.X : RatFunc k) = 0
  · rw [hden, div_zero] at h
    exact (div_ne_zero hnum hX) h
  have hp : (C c : k[X]) ^ 2 * (C γ - X) ^ 3 * (C a + C b * X) =
      (C d) ^ 2 * X ^ 2 := by
    apply RatFunc.algebraMap_injective k
    simpa only [map_mul, map_pow, map_add, map_sub,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X] using
      (div_eq_div_iff hX hden).mp h
  have heval := congrArg (Polynomial.eval γ) hp
  have hz : d ^ 2 * γ ^ 2 = 0 := by simpa using heval.symm
  exact (mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hγ)) hz

/-- The phase-square obstruction in the manuscript, for every nonempty finite
set of distinct nonzero constants and every nonzero amplitude. -/
theorem radialPhase_square_ne_linearReciprocal [Normal (RatFunc k) L]
    (h2 : (2 : L) ≠ 0) (Γ : Finset k) (hΓ : Γ.Nonempty)
    (c : k → k) (hc : ∀ γ ∈ Γ, c γ ≠ 0) (hγ0 : ∀ γ ∈ Γ, γ ≠ 0)
    (v : k → L)
    (hv : ∀ γ, v γ ^ 2 = algebraMap (RatFunc k) L (RatFunc.C γ - RatFunc.X))
    (d a b : k) (hd : d ≠ 0) :
    radialPhase Γ c v ^ 2 ≠ algebraMap (RatFunc k) L
      (RatFunc.C d ^ 2 / (RatFunc.C a + RatFunc.C b * RatFunc.X)) := by
  obtain ⟨γ, hγ⟩ := hΓ
  by_cases hs : Γ = {γ}
  · rw [hs, radialPhase_singleton_square γ c v (hv γ)]
    exact (algebraMap (RatFunc k) L).injective.ne
      (singletonPhaseSquare_ne_linearReciprocal γ (c γ) d a b
        (hγ0 γ hγ) (hc γ hγ) hd)
  · obtain ⟨δ, hδ, hδγ⟩ : ∃ δ ∈ Γ, δ ≠ γ := by
      by_contra hn
      push Not at hn
      apply hs
      ext δ
      simp only [Finset.mem_singleton]
      exact ⟨hn δ, fun h => h.symm ▸ hγ⟩
    exact radialPhase_square_not_rational h2 Γ c v hv γ δ hγ hδ hδγ.symm
      (hc γ hγ) (hc δ hδ) _

theorem radialPhase_ne_zero [Normal (RatFunc k) L]
    (h2 : (2 : L) ≠ 0) (Γ : Finset k) (hΓ : Γ.Nonempty)
    (c : k → k) (hc : ∀ γ ∈ Γ, c γ ≠ 0) (v : k → L)
    (hv : ∀ γ, v γ ^ 2 = algebraMap (RatFunc k) L (RatFunc.C γ - RatFunc.X)) :
    radialPhase Γ c v ≠ 0 := by
  have hv0 (γ : k) : v γ ≠ 0 := by
    intro hz
    have h := hv γ
    rw [hz, zero_pow (by decide)] at h
    exact (ratFunc_linearFactor_ne_zero γ)
      ((algebraMap (RatFunc k) L).injective (by simpa only [map_zero] using h.symm))
  have hLI := linearIndependent_squareRoots h2
    (fun γ : k => RatFunc.C γ - RatFunc.X) v hv0 hv
    ratFunc_linearFactor_distinct_squareclasses
  intro hz
  obtain ⟨γ, hγ⟩ := hΓ
  exact (radialPhaseScalar_ne_zero (hc γ hγ) γ)
    ((linearIndependent_iff'.mp hLI) Γ (fun δ => radialPhaseScalar (c δ) δ) hz γ hγ)

theorem radialPhase_ne_linearReciprocalSqrt [Normal (RatFunc k) L]
    (h2 : (2 : L) ≠ 0) (Γ : Finset k) (hΓ : Γ.Nonempty)
    (c : k → k) (hc : ∀ γ ∈ Γ, c γ ≠ 0) (hγ0 : ∀ γ ∈ Γ, γ ≠ 0)
    (v : k → L)
    (hv : ∀ γ, v γ ^ 2 = algebraMap (RatFunc k) L (RatFunc.C γ - RatFunc.X))
    (d a b : k) (hd : d ≠ 0) (u : L)
    (hu : u ^ 2 = algebraMap (RatFunc k) L (RatFunc.C a + RatFunc.C b * RatFunc.X)) :
    radialPhase Γ c v ≠ algebraMap (RatFunc k) L (RatFunc.C d) / u := by
  intro heq
  apply radialPhase_square_ne_linearReciprocal h2 Γ hΓ c hc hγ0 v hv d a b hd
  rw [heq, div_pow, hu, ← map_pow, ← map_div₀]


end RationalPhases

section RectangleAmplitudes

variable {k : Type*} [Field k]

abbrev PhaseRectangle := Fin 2 × Fin 2

/-- The group of chosen rectangle phases sharing the same cubic root. -/
def rectanglePhaseFiber (s : Finset PhaseRectangle) (γ : PhaseRectangle → k)
    (z : k) : Finset PhaseRectangle := s.filter (fun e => γ e = z)

def rectanglePhaseAmplitude (s : Finset PhaseRectangle)
    (γ A : PhaseRectangle → k) (z : k) : k :=
  ∑ e ∈ rectanglePhaseFiber s γ z, A e

theorem phaseAmplitude_ne_zero (h2 : (2 : k) ≠ 0) (α m A : k)
    (hα : α ≠ 0) (hm : m ≠ 0) (hA : A ^ 2 = 4 * α / m) : A ≠ 0 := by
  intro h
  have h4 : (4 : k) ≠ 0 := by simpa only [show (2 : k) ^ 2 = 4 by ring] using pow_ne_zero 2 h2
  rw [h, zero_pow (by decide)] at hA
  exact (div_ne_zero (mul_ne_zero h4 hα) hm) hA.symm

theorem distinctRow_phaseAmplitudes_not_cancel (h2 : (2 : k) ≠ 0)
    (α m m' A A' : k) (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hmm' : m ≠ m') (hA : A ^ 2 = 4 * α / m) (hA' : A' ^ 2 = 4 * α / m') :
    A + A' ≠ 0 := by
  intro hsum
  have heq : A' = -A := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hsum)
  have hp : 4 * α / m = 4 * α / m' := by rw [← hA, ← hA', heq, neg_sq]
  have h4 : (4 : k) ≠ 0 := by simpa only [show (2 : k) ^ 2 = 4 by ring] using pow_ne_zero 2 h2
  exact hmm' ((mul_left_cancel₀ (mul_ne_zero h4 hα)
    ((div_eq_div_iff hm hm').mp hp)).symm)

theorem rectanglePhaseFiber_row_injective
    (m n : Fin 2 → k) (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hninj : Function.Injective n) (s : Finset PhaseRectangle) (γ : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2) (z : k) :
    Set.InjOn Prod.fst (rectanglePhaseFiber s γ z : Set PhaseRectangle) := by
  intro e he f hf hrow
  obtain ⟨hes, hez⟩ := Finset.mem_filter.mp he
  obtain ⟨hfs, hfz⟩ := Finset.mem_filter.mp hf
  have hrat : m e.1 / n e.2 = m f.1 / n f.2 := by
    rw [← hγ e hes, ← hγ f hfs, hez, hfz]
  have hmul := (div_eq_div_iff (hn e.2) (hn f.2)).mp hrat
  rw [hrow] at hmul
  exact Prod.ext hrow (hninj (mul_left_cancel₀ (hm f.1) hmul).symm)

/-- Under distinct row and column parameters, every nonempty group sharing a
cubic root has a nonzero sum of amplitudes. This covers all subsets of the
four entries, including simultaneous opposite signs. -/
theorem rectanglePhaseAmplitude_ne_zero (h2 : (2 : k) ≠ 0)
    (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (z : k) (hz : z ∈ s.image γ) : rectanglePhaseAmplitude s γ A z ≠ 0 := by
  let F := rectanglePhaseFiber s γ z
  have hFs : F ⊆ s := Finset.filter_subset _ _
  have hF : F.Nonempty := by
    obtain ⟨e, he, hez⟩ := Finset.mem_image.mp hz
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hez⟩⟩
  have hinj : Set.InjOn Prod.fst (F : Set PhaseRectangle) :=
    rectanglePhaseFiber_row_injective m n hm hn hninj s γ hγ z
  have hcard : F.card ≤ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card_of_injOn Prod.fst
        (show Set.MapsTo Prod.fst (F : Set PhaseRectangle) (Finset.univ : Finset (Fin 2)) from
          fun _ _ => Finset.mem_univ _) hinj)
  have hpos := hF.card_pos
  by_cases htwo : F.card = 2
  · obtain ⟨e, f, hef, hpair⟩ := Finset.card_eq_two.mp htwo
    have he : e ∈ F := by rw [hpair]; simp
    have hf : f ∈ F := by rw [hpair]; simp
    have hrows : m e.1 ≠ m f.1 := fun h => hef (hinj he hf (hminj h))
    have hsum := distinctRow_phaseAmplitudes_not_cancel h2 α (m e.1) (m f.1)
      (A e) (A f) hα (hm e.1) (hm f.1) hrows (hA e (hFs he)) (hA f (hFs hf))
    change (∑ x ∈ F, A x) ≠ 0
    simpa only [hpair, Finset.sum_pair hef] using hsum
  · have hone : F.card = 1 := by omega
    obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hone
    have he : e ∈ F := by rw [heq]; simp
    change (∑ x ∈ F, A x) ≠ 0
    rw [heq, Finset.sum_singleton]
    exact phaseAmplitude_ne_zero h2 α (m e.1) (A e) hα (hm e.1) (hA e (hFs he))

end RectangleAmplitudes

section RectanglePhases

variable {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]

/-- The phase coefficient chosen from any subset of the four core entries.
Signs, including those from dual factors, are carried by the amplitudes. -/
def rectangleRadialPhase (s : Finset PhaseRectangle) (γ A : PhaseRectangle → k)
    (v : k → L) : L :=
  ∑ e ∈ s, radialPhaseScalar (A e) (γ e) • v (γ e)

theorem rectangleRadialPhase_eq_grouped (s : Finset PhaseRectangle)
    (γ A : PhaseRectangle → k) (v : k → L) :
    rectangleRadialPhase s γ A v =
      radialPhase (s.image γ) (rectanglePhaseAmplitude s γ A) v := by
  symm
  unfold radialPhase rectangleRadialPhase
  calc
    _ = ∑ z ∈ s.image γ, ∑ e ∈ s with γ e = z,
        radialPhaseScalar (A e) (γ e) • v (γ e) := by
      apply Finset.sum_congr rfl
      intro z _
      have hscalar : radialPhaseScalar (rectanglePhaseAmplitude s γ A z) z =
          ∑ e ∈ s with γ e = z, radialPhaseScalar (A e) z := by
        simp only [rectanglePhaseAmplitude, rectanglePhaseFiber, radialPhaseScalar,
          map_sum, Finset.sum_mul, Finset.sum_div]
      rw [hscalar, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_image_of_mem γ he) _

theorem ratFunc_extension_two_ne_zero (h2 : (2 : k) ≠ 0) : (2 : L) ≠ 0 := by
  intro hz
  apply h2
  apply RatFunc.C_injective
  apply (algebraMap (RatFunc k) L).injective
  simpa only [map_ofNat, map_zero] using hz

theorem rectanglePhase_roots_nonzero
    (m n : Fin 2 → k) (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (s : Finset PhaseRectangle) (γ : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2) :
    ∀ z ∈ s.image γ, z ≠ 0 := by
  intro z hz
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
  intro hez
  have h := hγ e he
  rw [hez, zero_pow (by decide)] at h
  exact (div_ne_zero (hm e.1) (hn e.2)) h.symm

/-- Universal noncancellation for all nonempty subsets of the distinct-index
rectangle and all choices among the displayed cubic roots and signs. -/
theorem rectangleRadialPhase_ne_zero [Normal (RatFunc k) L]
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (v : k → L)
    (hv : ∀ z, v z ^ 2 = algebraMap (RatFunc k) L (RatFunc.C z - RatFunc.X)) :
    rectangleRadialPhase s γ A v ≠ 0 := by
  rw [rectangleRadialPhase_eq_grouped]
  exact radialPhase_ne_zero (ratFunc_extension_two_ne_zero h2) (s.image γ) (hs.image γ)
    (rectanglePhaseAmplitude s γ A)
    (rectanglePhaseAmplitude_ne_zero h2 α hα m n hm hn hminj hninj s γ A hγ hA) v hv

/-- The precise algebraic obstruction to a coefficient of the form
`d / sqrt(a + b*z)` for every nonempty distinct-index core tensor. -/
theorem rectangleRadialPhase_ne_linearReciprocalSqrt [Normal (RatFunc k) L]
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (v : k → L)
    (hv : ∀ z, v z ^ 2 = algebraMap (RatFunc k) L (RatFunc.C z - RatFunc.X))
    (d a b : k) (hd : d ≠ 0) (u : L)
    (hu : u ^ 2 = algebraMap (RatFunc k) L (RatFunc.C a + RatFunc.C b * RatFunc.X)) :
    rectangleRadialPhase s γ A v ≠ algebraMap (RatFunc k) L (RatFunc.C d) / u := by
  rw [rectangleRadialPhase_eq_grouped]
  exact radialPhase_ne_linearReciprocalSqrt (ratFunc_extension_two_ne_zero h2)
    (s.image γ) (hs.image γ) (rectanglePhaseAmplitude s γ A)
    (rectanglePhaseAmplitude_ne_zero h2 α hα m n hm hn hminj hninj s γ A hγ hA)
    (rectanglePhase_roots_nonzero m n hm hn s γ hγ) v hv d a b hd u hu

/-- A fixed actual choice of the linear-factor square roots in the algebraic
closure, so their existence is not an extra premise of the algebraic model. -/
def algebraicPhaseRoot (z : k) : AlgebraicClosure (RatFunc k) :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) (RatFunc.C z - RatFunc.X))
    (by decide : 0 < (2 : ℕ))).choose

theorem algebraicPhaseRoot_sq (z : k) : algebraicPhaseRoot z ^ 2 =
    algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) (RatFunc.C z - RatFunc.X) :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) (RatFunc.C z - RatFunc.X))
    (by decide : 0 < (2 : ℕ))).choose_spec

/-- The obstruction instantiated in the actual algebraic closure of `k(z)`. -/
theorem algebraicRectanglePhase_ne_linearReciprocalSqrt
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (d a b : k) (hd : d ≠ 0) (u : AlgebraicClosure (RatFunc k))
    (hu : u ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C a + RatFunc.C b * RatFunc.X)) :
    rectangleRadialPhase s γ A algebraicPhaseRoot ≠
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) (RatFunc.C d) / u :=
  rectangleRadialPhase_ne_linearReciprocalSqrt h2 α hα m n hm hn hminj hninj
    s hs γ A hγ hA algebraicPhaseRoot algebraicPhaseRoot_sq d a b hd u hu

/-- Independent choices of the square-root branch at each entry are absorbed
into constant signs of the amplitudes, without changing their squares. -/
theorem rectanglePhase_normalize_root_choices
    (s : Finset PhaseRectangle) (γ A : PhaseRectangle → k) (R : PhaseRectangle → L)
    (v : k → L)
    (hR : ∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) L (RatFunc.C (γ e) - RatFunc.X))
    (hv : ∀ z, v z ^ 2 = algebraMap (RatFunc k) L (RatFunc.C z - RatFunc.X)) :
    ∃ A' : PhaseRectangle → k, (∀ e ∈ s, A' e ^ 2 = A e ^ 2) ∧
      (∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e) =
        rectangleRadialPhase s γ A' v := by
  let A' (e : PhaseRectangle) : k := if R e = v (γ e) then A e else -A e
  refine ⟨A', ?_, ?_⟩
  · intro e _
    dsimp only [A']
    split_ifs <;> simp only [neg_sq]
  · apply Finset.sum_congr rfl
    intro e he
    change radialPhaseScalar (A e) (γ e) • R e = radialPhaseScalar (A' e) (γ e) • v (γ e)
    dsimp only [A']
    split_ifs with heq
    · rw [heq]
    · have hneg : R e = -v (γ e) :=
        (sq_eq_sq_iff_eq_or_eq_neg.mp ((hR e he).trans (hv (γ e)).symm)).resolve_left heq
      rw [hneg]
      simp only [radialPhaseScalar, map_neg, neg_mul, neg_div, neg_smul, smul_neg]

/-- The exact scalar phase obstruction with independent roots at each of the
four entries; no common-root/sign convention is a premise. -/
theorem distinctRectanglePhase_ne_linearReciprocalSqrt [Normal (RatFunc k) L]
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (R : PhaseRectangle → L)
    (hR : ∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) L (RatFunc.C (γ e) - RatFunc.X))
    (v : k → L)
    (hv : ∀ z, v z ^ 2 = algebraMap (RatFunc k) L (RatFunc.C z - RatFunc.X))
    (d a b : k) (hd : d ≠ 0) (u : L)
    (hu : u ^ 2 = algebraMap (RatFunc k) L (RatFunc.C a + RatFunc.C b * RatFunc.X)) :
    (∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e) ≠
      algebraMap (RatFunc k) L (RatFunc.C d) / u := by
  obtain ⟨A', hA', heq⟩ := rectanglePhase_normalize_root_choices s γ A R v hR hv
  rw [heq]
  exact rectangleRadialPhase_ne_linearReciprocalSqrt h2 α hα m n hm hn hminj hninj
    s hs γ A' hγ (fun e he => (hA' e he).trans (hA e he)) v hv d a b hd u hu

/-- Independent root choices version in the actual algebraic closure, where
all auxiliary square roots are constructed. -/
theorem algebraicDistinctRectanglePhase_ne_linearReciprocalSqrt
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (R : PhaseRectangle → AlgebraicClosure (RatFunc k))
    (hR : ∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C (γ e) - RatFunc.X))
    (d a b : k) (hd : d ≠ 0) (u : AlgebraicClosure (RatFunc k))
    (hu : u ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C a + RatFunc.C b * RatFunc.X)) :
    (∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e) ≠
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) (RatFunc.C d) / u :=
  distinctRectanglePhase_ne_linearReciprocalSqrt h2 α hα m n hm hn hminj hninj
    s hs γ A hγ hA R hR algebraicPhaseRoot algebraicPhaseRoot_sq d a b hd u hu


end RectanglePhases

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.linearIndependent_squareRoots
#print axioms PrimeGap182.TypeIII.phaseLinearProduct_div_not_isSquare

#print axioms PrimeGap182.TypeIII.square_sum_squareRoots_not_in_base

#print axioms PrimeGap182.TypeIII.radialPhase_square_not_rational
#print axioms PrimeGap182.TypeIII.singletonPhaseSquare_ne_linearReciprocal
#print axioms PrimeGap182.TypeIII.radialPhase_square_ne_linearReciprocal

#print axioms PrimeGap182.TypeIII.radialPhase_ne_zero
#print axioms PrimeGap182.TypeIII.radialPhase_ne_linearReciprocalSqrt
#print axioms PrimeGap182.TypeIII.rectanglePhaseAmplitude_ne_zero

#print axioms PrimeGap182.TypeIII.rectangleRadialPhase_eq_grouped
#print axioms PrimeGap182.TypeIII.rectangleRadialPhase_ne_zero
#print axioms PrimeGap182.TypeIII.rectangleRadialPhase_ne_linearReciprocalSqrt
#print axioms PrimeGap182.TypeIII.algebraicRectanglePhase_ne_linearReciprocalSqrt

#print axioms PrimeGap182.TypeIII.distinctRectanglePhase_ne_linearReciprocalSqrt
#print axioms PrimeGap182.TypeIII.algebraicDistinctRectanglePhase_ne_linearReciprocalSqrt
